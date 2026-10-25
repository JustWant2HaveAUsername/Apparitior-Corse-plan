#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
课间穿梭 · 智能课表分配器
HackSHSID 2026 - Track 1 (School Life) prototype

A single-file Tkinter application that builds a weekly timetable for one student.
It minimises walking between buildings and shortfalls in lesson preparation,
then uses preference ratings as a small tie-breaker.

Run:
    python3 smart_scheduler.py
    python3 smart_scheduler.py --selftest

No third-party packages are required.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import queue
import random
import threading
import tempfile
import time
import traceback
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Optional

import tkinter as tk
import tkinter.font as tkfont
from tkinter import filedialog, messagebox, ttk


# ---------------------------------------------------------------------------
# Data and defaults
# ---------------------------------------------------------------------------

DAYS = ["周一", "周二", "周三", "周四", "周五"]
UNAVAILABLE_SLOTS = frozenset({(4, 5), (4, 6)})


def weekly_capacity(periods: list[Period]) -> int:
    return sum(period.end - period.start
               for d in range(len(DAYS)) for p, period in enumerate(periods)
               if (d, p) not in UNAVAILABLE_SLOTS)

DEFAULT_LOCATIONS = [
    "中兴楼一楼",
    "中兴楼地下一层",
    "中兴楼二楼",
    "中兴楼三楼",
    "中兴楼四楼",
    "礼堂",
    "操场",
    "逸夫楼三楼",
    "逸夫楼二楼",
]

# Rough walking estimates in minutes, used only as demo data.
# Every value is editable in the GUI. The matrix is symmetric.
_DEFAULT_DISTANCES = [
    # 中兴楼一楼 中兴楼地下一层 中兴楼二楼 中兴楼三楼 中兴楼四楼 礼堂 操场 逸夫楼三楼 逸夫楼二楼
    [0, 1, 1, 2, 3, 6, 7, 5, 6],
    [1, 0, 2, 3, 4, 7, 8, 6, 7],
    [1, 2, 0, 2, 4, 6, 7, 5, 6],
    [2, 3, 2, 0, 2, 7, 8, 6, 5],
    [3, 4, 4, 2, 0, 8, 9, 7, 6],
    [6, 7, 6, 7, 8, 0, 3, 9, 10],
    [7, 8, 7, 8, 9, 3, 0, 10, 11],
    [5, 6, 5, 6, 7, 9, 10, 0, 2],
    [6, 7, 6, 5, 6, 10, 11, 2, 0],
]

DEFAULT_COURSES = []

DEFAULT_CONFIG = {
    "periods_per_day": 7,
    "period_minutes": 45,
    "break_minutes": 10,
    "lunch_after": 4,
    "lunch_minutes": 65,
    "start_time": "08:30",
    "pref_weight": 2.5,
    "morning_meeting": True,
    "morning_meeting_location": "中兴楼地下一层",
    "morning_meeting_gap": 10,
    "order_meal": True,
    "order_meal_location": "中兴楼一楼",
    "order_meal_after_period": 1,
    "locker_location": "中兴楼地下一层",
}

# Cost weights. A minute of an impossible transition is deliberately much
# worse than a minute of ordinary walking.
W_CONFLICT = 60.0
W_PREP_SHORT = 25.0


@dataclass
class Course:
    name: str
    location: str
    lesson_minutes: int = 60   # 每周要求的总课时分钟数
    prep: int = 0
    like: int = 3
    location2: str = ""
    per_day_max: int = 2      # 每天最多安排几节
    locker: bool = False      # 是否需要去储物柜拿书
    linked: bool = False      # 是否要求两节连上（相邻时段）

    def copy(self) -> "Course":
        return Course(
            self.name,
            self.location,
            self.lesson_minutes,
            self.prep,
            self.like,
            self.location2 or "",
            self.per_day_max,
            self.locker,
            self.linked,
        )
    


def course_from_data(item: dict, legacy_period_minutes: int = 45) -> Course:
    minutes = int(item.get("lesson_minutes", 0))
    if minutes <= 0 and "sessions" in item:
        minutes = int(item["sessions"]) * legacy_period_minutes
    return Course(
        name=str(item["name"]), location=str(item["location"]),
        lesson_minutes=minutes, prep=int(item.get("prep", 0)),
        like=int(item.get("like", 3)), location2=str(item.get("location2") or ""),
        per_day_max=int(item.get("per_day_max", 2)),
        locker=bool(item.get("locker", False)), linked=bool(item.get("linked", False)),
    )


def write_json(path: str | Path, payload: dict) -> None:
    path = Path(path)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                         prefix=path.name + ".", suffix=".tmp", delete=False) as stream:
            temporary = stream.name
            json.dump(payload, stream, ensure_ascii=False, indent=2)
        os.replace(temporary, path)
    finally:
        if temporary and Path(temporary).exists():
            Path(temporary).unlink()


@dataclass
class Period:
    start: int  # minutes from midnight
    end: int
    gap: int  # minutes until the next period


@dataclass
class Metrics:
    cost: float = 0.0
    travel: int = 0
    changes: int = 0
    conflicts: int = 0
    conflict_minutes: int = 0
    prep_short: int = 0
    pref_clashes: int = 0
    classes: int = 0
    morning_travel: int = 0
    meal_travel: int = 0


@dataclass
class SolveResult:
    baseline: list[list[Optional[int]]]
    best: list[list[Optional[int]]]
    baseline_metrics: Metrics
    best_metrics: Metrics
    courses: list[Course]
    locations: list[str]
    travel: list[list[int]]
    config: dict
    periods: list[Period]
    elapsed: float
    seed: int
    location_choices: list[list[list[str]]] | None = None


# ---------------------------------------------------------------------------
# Time helpers
# ---------------------------------------------------------------------------

def hhmm_to_minutes(value: str) -> int:
    value = value.strip()
    parts = value.split(":")
    if len(parts) != 2:
        raise ValueError("时间格式应为 HH:MM，例如 08:00")
    hour, minute = int(parts[0]), int(parts[1])
    if not (0 <= hour <= 23 and 0 <= minute <= 59):
        raise ValueError("时间超出范围")
    return hour * 60 + minute


def minutes_to_hhmm(minutes: int) -> str:
    minutes = max(0, int(minutes))
    return f"{minutes // 60:02d}:{minutes % 60:02d}"


def short_location(name: str) -> str:
    return {
        "中兴楼地下一层": "中兴B1",
        "中兴楼一楼": "中兴1F",
        "中兴楼二楼": "中兴2F",
        "中兴楼三楼": "中兴3F",
        "中兴楼四楼": "中兴4F",
        "礼堂": "礼堂",
        "操场": "操场",
        "逸夫楼三楼": "逸夫3F",
        "逸夫楼二楼": "逸夫2F",
    }.get(name, name)


def build_periods(config: dict) -> list[Period]:
    # Match the fixed timetable given:
    # 8.30-9.30, 9.40-10.20, 10.30-11.10, 11.20-12.05, 13.15-14.10, 14.20-15.00, 15.10-15.50
    fixed_starts = [510, 580, 630, 680, 795, 860, 910]  # minutes from midnight
    fixed_ends = [570, 620, 670, 725, 850, 900, 950]
    count = len(fixed_starts)
    periods: list[Period] = []
    for i in range(count):
        start = fixed_starts[i]
        end = fixed_ends[i]
        if i < count - 1:
            gap = fixed_starts[i + 1] - end
        else:
            gap = int(config.get("break_minutes", 10))
        periods.append(Period(start=start, end=end, gap=gap))
    return periods


def validate_config(config: dict) -> None:
    if not 2 <= int(config["periods_per_day"]) <= 12:
        raise ValueError("每天节数应在 2–12 之间")
    if not 20 <= int(config["period_minutes"]) <= 90:
        raise ValueError("每节时长应在 20–90 分钟之间")
    if not 0 <= int(config["break_minutes"]) <= 30:
        raise ValueError("课间休息应在 0–30 分钟之间")
    if not 0 <= int(config["lunch_minutes"]) <= 120:
        raise ValueError("午休应在 0–120 分钟之间")
    if not 0 <= int(config["lunch_after"]) <= int(config["periods_per_day"]):
        raise ValueError("午休节次不合法")
    hhmm_to_minutes(str(config["start_time"]))
    if not 0 <= float(config["pref_weight"]) <= 10:
        raise ValueError("喜好平衡权重应在 0–10 之间")
    if bool(config.get("morning_meeting", False)):
        if not str(config.get("morning_meeting_location", "")).strip():
            raise ValueError("启用晨会时必须选择晨会地点")
        if not 0 <= int(config.get("morning_meeting_gap", 10)) <= 60:
            raise ValueError("晨会到第一节课的间隔应在 0–60 分钟之间")
    if bool(config.get("order_meal", False)):
        if not str(config.get("order_meal_location", "")).strip():
            raise ValueError("启用订餐时必须选择订餐地点")
    if not str(config.get("locker_location", "")).strip():
        raise ValueError("必须选择储物柜地点")


# ---------------------------------------------------------------------------
# Cost model and solver
# ---------------------------------------------------------------------------

def _preference_band(like: int) -> int:
    if like >= 4:
        return 1
    if like <= 2:
        return -1
    return 0


def _effective_location(course: Course, prev_loc: str, loc_index: dict, travel: list[list[int]]) -> str:
    if not course.location2:
        return course.location
    if not prev_loc:
        return course.location
    try:
        d1 = travel[loc_index[prev_loc]][loc_index[course.location]]
        d2 = travel[loc_index[prev_loc]][loc_index[course.location2]]
    except (KeyError, IndexError):
        return course.location
    return course.location2 if d2 < d1 else course.location


def _walk_via(
    travel: list[list[int]],
    loc_index: dict[str, int],
    base: str,
    waypoints: list[str],
    target: str,
) -> int:
    """Walk base -> waypoints -> target, summing pairwise distances."""
    walk = 0
    current = base
    for waypoint in waypoints:
        walk += travel[loc_index[current]][loc_index[waypoint]]
        current = waypoint
    walk += travel[loc_index[current]][loc_index[target]]
    return walk


def _course_scheduled_minutes(
    schedule: list[list[Optional[int]]],
    periods: list[Period],
    course_index: int,
) -> int:
    return sum(
        period.end - period.start
        for day, row in enumerate(schedule)
        for p, ci in enumerate(row)
        if ci == course_index
        for period in (periods[p],)
    )


def _schedule_is_valid(
    courses: list[Course],
    days: int,
    periods_per_day: int,
    schedule: list[list[Optional[int]]],
    periods: list[Period],
) -> bool:
    if len(schedule) != days or any(len(row) != periods_per_day for row in schedule):
        return False
    if any(ci is not None and (not isinstance(ci, int) or not 0 <= ci < len(courses))
           for row in schedule for ci in row):
        return False
    for day in range(days):
        positions: dict[int, list[int]] = {}
        counts: dict[int, int] = {}
        for p, ci in enumerate(schedule[day]):
            if ci is None:
                continue
            if (day, p) in UNAVAILABLE_SLOTS:
                return False
            counts[ci] = counts.get(ci, 0) + 1
            positions.setdefault(ci, []).append(p)
        for ci, count in counts.items():
            course = courses[ci]
            if count > course.per_day_max:
                return False
            if count > 1 and not course.linked:
                return False
            if course.linked:
                ps = positions[ci]
                if count != 2 or ps[1] != ps[0] + 1 or periods[ps[0]].gap > 10:
                    return False

    for ci, course in enumerate(courses):
        if course.lesson_minutes > 0:
            if _course_scheduled_minutes(schedule, periods, ci) != course.lesson_minutes:
                return False
    return True


def evaluate(
    schedule: list[list[Optional[int]]],
    courses: list[Course],
    locations: list[str],
    travel: list[list[int]],
    periods: list[Period],
    pref_weight: float,
    config: Optional[dict] = None,
) -> Metrics:
    """Score a timetable. Lower is better."""
    config = config or {}
    loc_index = {name: i for i, name in enumerate(locations)}
    result = Metrics()
    day_count = len(schedule)
    meeting_on = bool(config.get("morning_meeting", False))
    meeting_loc = str(config.get("morning_meeting_location", ""))
    meeting_buffer = int(config.get("morning_meeting_gap", 10))
    meal_on = bool(config.get("order_meal", False))
    meal_loc = str(config.get("order_meal_location", ""))
    meal_after = int(config.get("order_meal_after_period", 1))
    locker_loc = str(config.get("locker_location", ""))

    def valid_loc(name: str) -> bool:
        return name in loc_index

    for day in range(day_count):
        row = schedule[day]
        first_period = next((p for p, ci in enumerate(row) if ci is not None), None)
        previous: Optional[tuple[int, int, str]] = None
        if first_period is None:
            continue

        first_course = courses[row[first_period]]
        first_used = first_course.location
        if (
            meeting_on
            and valid_loc(meeting_loc)
            and first_course.location2
            and valid_loc(first_course.location2)
        ):
            d1 = travel[loc_index[meeting_loc]][loc_index[first_course.location]]
            d2 = travel[loc_index[meeting_loc]][loc_index[first_course.location2]]
            first_used = first_course.location2 if d2 < d1 else first_course.location

        first_base = meeting_loc if meeting_on and valid_loc(meeting_loc) else (locker_loc if first_course.locker and valid_loc(locker_loc) else first_used)
        first_waypoints: list[str] = []
        if meeting_on and valid_loc(meeting_loc):
            first_waypoints = [locker_loc] if (first_course.locker and valid_loc(locker_loc)) else []
        elif first_course.locker and valid_loc(locker_loc):
            first_waypoints = []

        if first_course.location2:
            first_used = min((first_course.location, first_course.location2),
                             key=lambda loc: _walk_via(travel, loc_index, first_base, first_waypoints, loc))
        first_walk = _walk_via(travel, loc_index, first_base, first_waypoints, first_used)
        first_buffer = meeting_buffer + periods[first_period].start - periods[0].start
        result.classes += 1
        result.travel += first_walk
        if meeting_on:
            result.morning_travel += first_walk
        if meeting_on and first_walk > first_buffer:
            result.conflicts += 1
            result.conflict_minutes += first_walk - first_buffer
        if meeting_on:
            available_prep = max(0, first_buffer - first_walk)
            if first_course.prep > available_prep:
                result.prep_short += first_course.prep - available_prep

        previous = (first_period, row[first_period], first_used)

        for p in range(first_period + 1, len(row)):
            ci = row[p]
            if ci is None:
                continue
            course = courses[ci]
            result.classes += 1
            prev_p, prev_ci, prev_loc_used = previous
            continuation = ci == prev_ci and course.linked and p == prev_p + 1
            used = _effective_location(course, prev_loc_used, loc_index, travel)
            waypoints: list[str] = []
            if meal_on and prev_p == meal_after - 1 and p == meal_after and valid_loc(meal_loc):
                waypoints.append(meal_loc)
            if course.locker and not continuation and valid_loc(locker_loc):
                waypoints.append(locker_loc)
            used = prev_loc_used if continuation else _effective_location(
                course, waypoints[-1] if waypoints else prev_loc_used, loc_index, travel)
            walk = _walk_via(travel, loc_index, prev_loc_used, waypoints, used)
            if meal_loc in waypoints:
                without_meal = waypoints[1:]
                result.meal_travel += max(0, walk - _walk_via(travel, loc_index, prev_loc_used, without_meal, used))
            gap = periods[p].start - periods[prev_p].end
            result.travel += walk
            if prev_loc_used != used:
                result.changes += 1
            if walk > gap:
                result.conflicts += 1
                result.conflict_minutes += walk - gap
            available_prep = max(0, gap - walk)
            if not continuation and course.prep > available_prep:
                result.prep_short += course.prep - available_prep
            band_prev = _preference_band(courses[prev_ci].like)
            band_now = _preference_band(course.like)
            if band_prev != 0 and band_prev == band_now:
                result.pref_clashes += 1
            previous = (p, ci, used)

    result.cost = (
        result.travel
        + W_CONFLICT * result.conflict_minutes
        + W_PREP_SHORT * result.prep_short
        + pref_weight * result.pref_clashes
    )
    return result


def _day_patterns(periods_per_day: int, max_per_day: int, linked: bool) -> list[list[int]]:
    """Generate all valid period subsets for a single day."""
    patterns: list[list[int]] = [[]]  # empty day is always valid
    if linked:
        # Consecutive blocks only
        for start in range(periods_per_day):
            if max_per_day >= 2 and start + 1 < periods_per_day:
                patterns.append([start, start + 1])
    else:
        from itertools import combinations

        for k in range(1, min(1, max_per_day, periods_per_day) + 1):
            for combo in combinations(range(periods_per_day), k):
                patterns.append(list(combo))
    return patterns


def _generate_all_patterns(
    periods_per_day: int,
    days: int,
    max_per_day: int,
    linked: bool,
    periods: list[Period],
    target_minutes: int,
) -> list[list[tuple[int, int]]]:
    """
    Generate candidate time-slot patterns whose total duration matches target minutes.
    Uses day-by-day backtracking with pruning (much more efficient than all combinations).
    """
    day_opts = _day_patterns(periods_per_day, max_per_day, linked)
    day_opts = [opt for opt in day_opts if not opt or not linked or periods[opt[0]].gap <= 10]
    # Precompute minutes for each day option
    day_opt_minutes = []
    for opt in day_opts:
        minutes = sum(periods[p].end - periods[p].start for p in opt)
        day_opt_minutes.append(minutes)

    patterns: list[list[tuple[int, int]]] = []

    def backtrack(day_idx: int, current_slots: list[tuple[int, int]], current_minutes: int) -> None:
        if day_idx == days:
            if current_minutes == target_minutes and current_slots:
                patterns.append(list(current_slots))
            return
        # Prune: even if we fill all remaining days with max minutes, can we reach target?
        remaining_days = days - day_idx
        max_remaining = remaining_days * max(day_opt_minutes, default=0)
        if current_minutes + max_remaining < target_minutes:
            return
        if current_minutes > target_minutes:
            return

        for opt_idx, opt in enumerate(day_opts):
            if any((day_idx, p) in UNAVAILABLE_SLOTS for p in opt):
                continue
            opt_minutes = day_opt_minutes[opt_idx]
            new_minutes = current_minutes + opt_minutes
            if new_minutes > target_minutes:
                continue
            # Add slots for this day
            added = [(day_idx, p) for p in opt]
            current_slots.extend(added)
            backtrack(day_idx + 1, current_slots, new_minutes)
            # Remove added slots
            for _ in added:
                current_slots.pop()

    backtrack(0, [], 0)
    return patterns


def _filter_patterns_by_minutes(
    patterns: list[list[tuple[int, int]]],
    periods: list[Period],
    target_minutes: int,
) -> list[list[tuple[int, int]]]:
    """Filter patterns whose total duration equals target minutes (±5 tolerance)."""
    result = []
    for pattern in patterns:
        total = sum(periods[p].end - periods[p].start for _, p in pattern)
        if total == target_minutes:
            result.append(pattern)
    return result


def _patterns_conflict(p1: list[tuple[int, int]], p2: list[tuple[int, int]]) -> bool:
    """Check if two patterns share any slot."""
    return not set(p1).isdisjoint(set(p2))


def _schedule_from_patterns(
    courses: list[Course],
    chosen_patterns: list[list[tuple[int, int]]],
    days: int,
    periods_per_day: int,
) -> list[list[Optional[int]]]:
    """Build schedule matrix from chosen patterns (one pattern per course)."""
    schedule = [[None] * periods_per_day for _ in range(days)]
    for ci, pattern in enumerate(chosen_patterns):
        for d, p in pattern:
            if (d, p) in UNAVAILABLE_SLOTS:
                raise ValueError("周五最后两节不上课")
            if schedule[d][p] is not None:
                raise ValueError("课程时段冲突，无法构建完整课表")
            schedule[d][p] = ci
    return schedule


def solve(
    courses: list[Course],
    locations: list[str],
    travel: list[list[int]],
    config: dict,
    seed: int = 2026,
    restarts: int = 5,
    iterations: int = 12000,
    progress: Optional[Callable[[str], None]] = None,
) -> SolveResult:
    """Optimise with simulated annealing over time-slot pattern choices."""
    validate_config(config)
    days = len(DAYS)
    periods = build_periods(config)
    periods_per_day = len(periods)
    pref_weight = float(config["pref_weight"])
    validate_problem(courses, locations, travel)
    capacity = weekly_capacity(periods)
    if sum(c.lesson_minutes for c in courses) > capacity:
        raise ValueError(f"所需周课时超过一周可用的 {capacity} 分钟")

    location_set = set(locations)
    if config.get("morning_meeting") and config.get("morning_meeting_location") not in location_set:
        raise ValueError("晨会地点不在地点列表中")
    if config.get("order_meal") and config.get("order_meal_location") not in location_set:
        raise ValueError("订餐地点不在地点列表中")
    if config.get("locker_location") and config["locker_location"] not in location_set:
        raise ValueError("储物柜地点不在地点列表中")
    for course in courses:
        if course.location not in location_set:
            raise ValueError(f"课程「{course.name}」的地点在列表中不存在")
        if course.location2 and course.location2 not in location_set:
            raise ValueError(f"课程「{course.name}」的第二地点在列表中不存在")
        if course.lesson_minutes < 1:
            raise ValueError(f"课程「{course.name}」的周课时至少为 1 分钟")

    rng = random.Random(seed)
    started = time.perf_counter()

    # Pre-generate candidate patterns for each course, filtered by required minutes
    course_patterns: list[list[list[tuple[int, int]]]] = []
    for course in courses:
        valid_pat = _generate_all_patterns(
            periods_per_day, days, course.per_day_max, course.linked, periods, course.lesson_minutes
        )
        if not valid_pat:
            raise ValueError(
                f"课程「{course.name}」无法找到满足周课时 {course.lesson_minutes} 分钟、"
                f"每天最多 {course.per_day_max} 节、{'连上' if course.linked else '不要求连上'} 的时段组合"
            )
        rng.shuffle(valid_pat)
        course_patterns.append(valid_pat)

    masks = [[sum(1 << (d * periods_per_day + p) for d, p in pat)
              for pat in patterns] for patterns in course_patterns]
    available_slots = [(d, p) for d in range(days) for p in range(periods_per_day)
                       if (d, p) not in UNAVAILABLE_SLOTS]

    def random_valid_assignment() -> list[list[tuple[int, int]]]:
        chosen: list[list[tuple[int, int]]] = [[] for _ in courses]
        deadline = time.perf_counter() + 15
        failed = set()

        def search(remaining: tuple[int, ...], occupied: int) -> bool:
            if not remaining:
                return True
            if time.perf_counter() > deadline:
                raise ValueError("完整排课搜索超时，尚未找到可行解；请检查课时或连堂限制后重试")
            key = (remaining, occupied)
            if key in failed:
                return False
            # Place the most constrained course first, and backtrack on conflicts.
            options = [(ci, [j for j, mask in enumerate(masks[ci]) if not mask & occupied])
                       for ci in remaining]
            ci, candidates = min(options, key=lambda item: len(item[1]))
            if candidates:
                rest = tuple(i for i in remaining if i != ci)
                for j in candidates:
                    chosen[ci] = course_patterns[ci][j]
                    if search(rest, occupied | masks[ci][j]):
                        return True
            failed.add(key)
            return False

        if not search(tuple(range(len(courses))), 0):
            raise ValueError("所有课程无法同时排入：周课时、每天一次或两节连堂的要求存在冲突。请调整后重试。")
        return chosen

    baseline_patterns = random_valid_assignment()
    baseline_schedule = _schedule_from_patterns(courses, baseline_patterns, days, periods_per_day)
    baseline_metrics = evaluate(
        baseline_schedule, courses, locations, travel, periods, pref_weight, config
    )

    best_patterns = [list(p) for p in baseline_patterns]
    best_metrics = baseline_metrics

    for restart in range(restarts):
        if progress:
            progress(f"优化中… {restart + 1}/{restarts}")

        if restart == 0:
            current_patterns = [list(p) for p in baseline_patterns]
        else:
            current_patterns = [list(p) for p in best_patterns]
        current_metrics = evaluate(
            _schedule_from_patterns(courses, current_patterns, days, periods_per_day),
            courses, locations, travel, periods, pref_weight, config,
        )

        temperature_start = 45.0
        temperature_end = 0.05
        for step in range(iterations):
            ratio = step / max(1, iterations - 1)
            temperature = temperature_start * ((temperature_end / temperature_start) ** ratio)

            candidate_patterns = [list(p) for p in current_patterns]
            if rng.random() < 0.5:
                # Equal-duration swaps keep exact weekly minutes, even on a full grid.
                current_schedule = _schedule_from_patterns(courses, current_patterns, days, periods_per_day)
                d1, p1 = rng.choice(available_slots)
                d2, p2 = rng.choice([(d, p) for d, p in available_slots
                                    if periods[p].end - periods[p].start == periods[p1].end - periods[p1].start])
                a, b = current_schedule[d1][p1], current_schedule[d2][p2]
                if a == b:
                    continue
                if a is not None:
                    candidate_patterns[a].remove((d1, p1))
                    candidate_patterns[a].append((d2, p2))
                if b is not None:
                    candidate_patterns[b].remove((d2, p2))
                    candidate_patterns[b].append((d1, p1))
            else:
                ci = rng.randrange(len(courses))
                new_pat = rng.choice(course_patterns[ci])
                if any(j != ci and _patterns_conflict(new_pat, pat)
                       for j, pat in enumerate(current_patterns)):
                    continue
                candidate_patterns[ci] = list(new_pat)
            candidate_schedule = _schedule_from_patterns(
                courses, candidate_patterns, days, periods_per_day
            )
            if not _schedule_is_valid(courses, days, periods_per_day, candidate_schedule, periods):
                continue
            candidate_metrics = evaluate(
                candidate_schedule, courses, locations, travel, periods, pref_weight, config
            )

            delta = candidate_metrics.cost - current_metrics.cost
            if delta <= 0 or rng.random() < math.exp(-delta / max(temperature, 1e-9)):
                current_patterns = candidate_patterns
                current_metrics = candidate_metrics
                if candidate_metrics.cost < best_metrics.cost:
                    best_patterns = [list(p) for p in candidate_patterns]
                    best_metrics = candidate_metrics

    best_schedule = _schedule_from_patterns(courses, best_patterns, days, periods_per_day)
    if not all(_schedule_is_valid(courses, days, periods_per_day, s, periods)
               for s in (baseline_schedule, best_schedule)):
        raise RuntimeError("课表完整性检查失败")
    elapsed = time.perf_counter() - started
    return SolveResult(
        baseline=baseline_schedule,
        best=best_schedule,
        baseline_metrics=baseline_metrics,
        best_metrics=best_metrics,
        courses=[c.copy() for c in courses],
        locations=list(locations),
        travel=[row[:] for row in travel],
        config=dict(config),
        periods=periods,
        elapsed=elapsed,
        seed=seed,
        location_choices=None,
    )


def validate_problem(courses: list[Course], locations: list[str], travel: list[list[int]], *, allow_empty: bool = False) -> None:
    if not courses and not allow_empty:
        raise ValueError("请至少添加一门课程")
    names = [c.name for c in courses]
    if len(names) != len(set(names)):
        raise ValueError("课程名称不能重复")
    if len(travel) != len(locations) or any(len(row) != len(locations) for row in travel):
        raise ValueError("路程矩阵与地点数量不一致")
    if not locations or len(set(locations)) != len(locations) or any(not name.strip() for name in locations):
        raise ValueError("地点不能为空或重复")
    if any(value < 0 for row in travel for value in row):
        raise ValueError("移动时间不能为负数")
    for course in courses:
        if course.location not in locations:
            raise ValueError(f"课程「{course.name}」的地点在列表中不存在")
        if course.location2 and course.location2 not in locations:
            raise ValueError(f"课程「{course.name}」的第二地点在列表中不存在")
        if course.lesson_minutes < 1:
            raise ValueError(f"课程「{course.name}」的周课时至少为 1 分钟")
        if not 0 <= course.prep <= 180:
            raise ValueError(f"课程「{course.name}」的课前准备时间不合法")
        if not 1 <= course.like <= 5:
            raise ValueError(f"课程「{course.name}」的喜爱度应为 1–5")
        if not 1 <= course.per_day_max <= 7:
            raise ValueError(f"课程「{course.name}」每天最多节数不合法")
        if course.linked and course.per_day_max < 2:
            raise ValueError(f"课程「{course.name}」要求两节连堂，每天最多节数必须至少为 2")


# ---------------------------------------------------------------------------
# Tkinter application
# ---------------------------------------------------------------------------

class SchedulerApp:
    COLORS = {
        "bg": "#f1f5f9",
        "surface": "#ffffff",
        "ink": "#0f172a",
        "muted": "#64748b",
        "line": "#dbe3ee",
        "accent": "#2563eb",
        "accent_dark": "#1d4ed8",
        "good": "#15803d",
        "warning": "#b45309",
    }

    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title("课间穿梭 · 智能课表分配器")
        self.root.geometry("1360x880")
        self.root.minsize(1000, 640)
        self.root.configure(bg=self.COLORS["bg"])

        self.locations = list(DEFAULT_LOCATIONS)
        self.travel = [row[:] for row in _DEFAULT_DISTANCES]
        self.courses = []
        self.config = dict(DEFAULT_CONFIG)
        try:
            import sys

            script_dir = Path(sys.argv[0]).resolve().parent
        except Exception:
            script_dir = Path.cwd()
        self.autosave_path = script_dir / "schedule_autosave.json"

        self.result: Optional[SolveResult] = None
        self.display_courses: list[Course] = []
        self.display_config = dict(DEFAULT_CONFIG)
        self._matrix_window: Optional[tk.Toplevel] = None
        self._matrix_vars: dict[tuple[int, int], tk.StringVar] = {}
        self._matrix_guard = False
        self._generating = False
        self._generation_queue: queue.Queue = queue.Queue()
        self._config_autosave_id: Optional[str] = None

        self.font_family = self._choose_font()
        self.name_font = tkfont.Font(
            family=self.font_family, size=10, weight="bold"
        )
        self.detail_font = tkfont.Font(family=self.font_family, size=8)
        self.course_locker_var = tk.BooleanVar(value=False)
        self.course_linked_var = tk.BooleanVar(value=False)
        self.course_lesson_var = tk.StringVar(value="60")
        self._setup_style()
        self._build_ui()
        self._enable_label_wrapping(self.root)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self._refresh_all()
        self._try_load_autosave()
        if self.result is None and self.courses:
            self.root.after(350, self.generate)
        elif self.result is None:
            self.status_var.set("请在左侧添加课程，或读取 JSON 文件。")

    # ------------------------------------------------------------------
    # Styling and layout
    # ------------------------------------------------------------------

    def _choose_font(self) -> str:
        families = set(tkfont.families(self.root))
        for candidate in (
            "PingFang SC",
            "Microsoft YaHei UI",
            "Microsoft YaHei",
            "Noto Sans CJK SC",
            "Source Han Sans SC",
        ):
            if candidate in families:
                return candidate
        return "TkDefaultFont"

    def _setup_style(self) -> None:
        style = ttk.Style(self.root)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass

        family = self.font_family
        style.configure(".", font=(family, 11), background=self.COLORS["surface"])
        style.configure("TFrame", background=self.COLORS["surface"])
        style.configure("App.TFrame", background=self.COLORS["bg"])
        style.configure("TLabel", background=self.COLORS["surface"], foreground=self.COLORS["ink"])
        style.configure("Muted.TLabel", foreground=self.COLORS["muted"])
        style.configure("Title.TLabel", font=(family, 20, "bold"), foreground=self.COLORS["ink"])
        style.configure("Subtitle.TLabel", font=(family, 10), foreground=self.COLORS["muted"])
        style.configure("Section.TLabel", font=(family, 12, "bold"), foreground=self.COLORS["ink"])
        style.configure("TNotebook", background=self.COLORS["bg"], borderwidth=0)
        style.configure(
            "TNotebook.Tab",
            font=(family, 11),
            padding=(16, 8),
            background="#e2e8f0",
            foreground=self.COLORS["muted"],
        )
        style.map(
            "TNotebook.Tab",
            background=[("selected", self.COLORS["surface"])],
            foreground=[("selected", self.COLORS["ink"])],
        )
        style.configure("TLabelframe", background=self.COLORS["surface"], bordercolor=self.COLORS["line"])
        style.configure(
            "TLabelframe.Label",
            background=self.COLORS["surface"],
            foreground=self.COLORS["muted"],
            font=(family, 10, "bold"),
        )
        style.configure("TEntry", padding=4)
        style.configure("TCombobox", padding=4)
        style.configure(
            "Treeview",
            background=self.COLORS["surface"],
            fieldbackground=self.COLORS["surface"],
            rowheight=27,
            borderwidth=0,
        )
        style.configure(
            "Treeview.Heading",
            font=(family, 10, "bold"),
            background="#e8eef7",
            foreground=self.COLORS["ink"],
            padding=5,
        )
        style.configure(
            "Accent.TButton",
            font=(family, 11, "bold"),
            background=self.COLORS["accent"],
            foreground="#ffffff",
            padding=(15, 8),
            borderwidth=0,
        )
        style.map(
            "Accent.TButton",
            background=[("active", self.COLORS["accent_dark"]), ("disabled", "#93b4f5")],
            foreground=[("disabled", "#f1f5f9")],
        )
        style.configure(
            "Soft.TButton",
            font=(family, 10),
            background="#e2e8f0",
            foreground=self.COLORS["ink"],
            padding=(10, 7),
            borderwidth=0,
        )
        style.map("Soft.TButton", background=[("active", "#cbd5e1")])
        style.configure("Danger.TButton", foreground="#b91c1c")

    def _build_ui(self) -> None:
        header = tk.Frame(self.root, bg=self.COLORS["surface"], padx=20, pady=12)
        header.pack(fill="x")
        header.columnconfigure(0, weight=1)

        title_box = ttk.Frame(header)
        title_box.grid(row=0, column=0, sticky="ew")
        ttk.Label(title_box, text="课间穿梭", style="Title.TLabel").pack(anchor="w")
        ttk.Label(
            title_box,
            text="智能课表分配器 · HackSHSID 2026 Track 1",
            style="Subtitle.TLabel",
        ).pack(anchor="w")

        actions = ttk.Frame(header)
        actions.grid(row=0, column=1, sticky="e")
        ttk.Button(actions, text="重置模板", style="Soft.TButton", command=self.load_demo).pack(
            side="left", padx=(0, 6)
        )
        ttk.Button(actions, text="读取", style="Soft.TButton", command=self.load_json).pack(
            side="left", padx=(0, 6)
        )
        ttk.Button(actions, text="保存", style="Soft.TButton", command=self.save_json).pack(
            side="left", padx=(0, 6)
        )
        ttk.Button(actions, text="导出 CSV", style="Soft.TButton", command=self.export_csv).pack(
            side="left", padx=(0, 12)
        )
        self.generate_button = ttk.Button(
            actions, text="生成智能课表", style="Accent.TButton", command=self.generate
        )
        self.generate_button.pack(side="left")

        def layout_header(event) -> None:
            if event.widget is header:
                stacked = event.width < 1150
                actions.grid_configure(row=1 if stacked else 0, column=0 if stacked else 1,
                                       sticky="w" if stacked else "e", pady=(8, 0) if stacked else 0)
        header.bind("<Configure>", layout_header)

        line = tk.Frame(self.root, bg=self.COLORS["line"], height=1)
        line.pack(fill="x")

        paned = ttk.Panedwindow(self.root, orient="horizontal")
        self.main_paned = paned
        paned.pack(fill="both", expand=True, padx=14, pady=14)

        left = ttk.Frame(paned, width=500)
        right = ttk.Frame(paned)
        paned.add(left, weight=0)
        paned.add(right, weight=1)

        self._build_left_panel(left)
        self._build_right_panel(right)

        def constrain_panes(_event=None) -> None:
            if paned.winfo_width() > 1:
                position = paned.sashpos(0)
                bounded = max(320, min(position, paned.winfo_width() - 465))
                if bounded != position:
                    paned.sashpos(0, bounded)
        for pane in (left, right):
            pane.bind("<Configure>", lambda _event: paned.after_idle(constrain_panes), add="+")

        status_bar = tk.Frame(self.root, bg=self.COLORS["surface"], padx=16, pady=7)
        status_bar.pack(fill="x", side="bottom")
        self.status_var = tk.StringVar(value="就绪。请先录入课程，再生成智能课表。")
        ttk.Label(status_bar, textvariable=self.status_var, style="Muted.TLabel").pack(anchor="w")

    def _enable_label_wrapping(self, widget) -> None:
        for child in widget.winfo_children():
            if isinstance(child, (tk.Label, ttk.Label)):
                if len(str(child.cget("text"))) >= 20 or child.cget("textvariable"):
                    child.configure(wraplength=300, justify="left", width=1)
                    if child.winfo_manager() == "grid":
                        child.grid_configure(sticky="ew")
                    elif child.winfo_manager() == "pack":
                        child.pack_configure(fill="x")
                    child.bind("<Configure>", self._wrap_label, add="+")
            self._enable_label_wrapping(child)

    def _wrap_label(self, event) -> None:
        event.widget.configure(wraplength=max(20, event.width - 4))
        parent = event.widget.master
        while parent is not None:
            if isinstance(parent, tk.Canvas) and hasattr(parent, "resize_content"):
                parent.after_idle(parent.resize_content)
                break
            parent = getattr(parent, "master", None)

    def _scrollable_tab(self, notebook: ttk.Notebook) -> ttk.Frame:
        page = ttk.Frame(notebook)
        page.rowconfigure(0, weight=1)
        page.columnconfigure(0, weight=1)
        canvas = tk.Canvas(page, highlightthickness=0, bg=self.COLORS["surface"])
        canvas.grid(row=0, column=0, sticky="nsew")
        vertical = ttk.Scrollbar(page, orient="vertical", command=canvas.yview)
        horizontal = ttk.Scrollbar(page, orient="horizontal", command=canvas.xview)
        vertical.grid(row=0, column=1, sticky="ns")
        horizontal.grid(row=1, column=0, sticky="ew")
        canvas.configure(yscrollcommand=vertical.set, xscrollcommand=horizontal.set)
        content = ttk.Frame(canvas, padding=12)
        item = canvas.create_window(0, 0, anchor="nw", window=content)

        def resize(_event=None) -> None:
            canvas.itemconfigure(item, width=max(560, canvas.winfo_width()),
                                 height=max(content.winfo_reqheight(), canvas.winfo_height()))
            canvas.configure(scrollregion=canvas.bbox("all"))
        canvas.resize_content = resize
        canvas.bind("<Configure>", resize)
        content.bind("<Configure>", resize)
        notebook.add(page)
        return content

    def _build_left_panel(self, parent: ttk.Frame) -> None:
        notebook = ttk.Notebook(parent)
        self.input_notebook = notebook
        notebook.pack(fill="both", expand=True)

        self.course_tab = self._scrollable_tab(notebook)
        self.location_tab = self._scrollable_tab(notebook)
        self.config_tab = self._scrollable_tab(notebook)
        for index, title in enumerate(("课程", "地点与路程", "时间与偏好")):
            notebook.tab(index, text=title)

        self._build_course_tab()
        self._build_location_tab()
        self._build_config_tab()

    def _build_course_tab(self) -> None:
        tab = self.course_tab
        tab.columnconfigure(0, weight=1)
        tab.rowconfigure(3, weight=1)

        ttk.Label(tab, text="课程信息", style="Section.TLabel").grid(
            row=0, column=0, sticky="w", pady=(0, 2)
        )
        ttk.Label(
            tab,
            text="周课时决定需要排多少节课；准备时间是上课前需要的缓冲；勾选储物柜表示该课前需先去储物柜；勾选连上表示该课的多节时段必须相邻。",
            style="Muted.TLabel",
        ).grid(row=1, column=0, sticky="w", pady=(0, 8))

        form = ttk.LabelFrame(tab, text="添加 / 编辑课程", padding=10)
        form.grid(row=2, column=0, sticky="ew", pady=(0, 10))
        form.columnconfigure(1, weight=1)
        form.columnconfigure(3, weight=1)

        # 第0行：课程名
        ttk.Label(form, text="课程名").grid(row=0, column=0, sticky="w", pady=3)
        self.course_name_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.course_name_var).grid(
            row=0, column=1, columnspan=3, sticky="ew", padx=(8, 0), pady=3
        )

        # 第1行：主地点、第二地点
        ttk.Label(form, text="主地点").grid(row=1, column=0, sticky="w", pady=3)
        self.course_location_var = tk.StringVar()
        self.course_location_combo = ttk.Combobox(
            form, textvariable=self.course_location_var, state="readonly", width=13
        )
        self.course_location_combo.grid(row=1, column=1, sticky="w", padx=(8, 12), pady=3)

        ttk.Label(form, text="第二地点").grid(row=1, column=2, sticky="e", pady=3)
        self.course_location2_var = tk.StringVar(value="（无）")
        self.course_location2_combo = ttk.Combobox(
            form,
            textvariable=self.course_location2_var,
            state="readonly",
            width=11,
        )
        self.course_location2_combo.grid(row=1, column=3, sticky="w", padx=(8, 0), pady=3)

        # 第2行：课前准备、周课时(分钟)
        ttk.Label(form, text="课前准备").grid(row=2, column=0, sticky="w", pady=3)
        self.course_prep_var = tk.StringVar(value="0")
        prep_box = ttk.Frame(form)
        prep_box.grid(row=2, column=1, sticky="w", padx=(8, 0), pady=3)
        ttk.Spinbox(
            prep_box, from_=0, to=180, increment=5, textvariable=self.course_prep_var, width=6
        ).pack(side="left")
        ttk.Label(prep_box, text="分钟", style="Muted.TLabel").pack(side="left", padx=(5, 0))

        ttk.Label(form, text="周课时").grid(row=2, column=2, sticky="e", pady=3)
        self.course_lesson_var = tk.StringVar(value="60")
        lesson_box = ttk.Frame(form)
        lesson_box.grid(row=2, column=3, sticky="w", padx=(8, 0), pady=3)
        ttk.Spinbox(
            lesson_box, from_=1, to=2100, increment=5, textvariable=self.course_lesson_var, width=6
        ).pack(side="left")
        ttk.Label(lesson_box, text="分钟/周", style="Muted.TLabel").pack(side="left", padx=(5, 0))

        # 第3行：喜爱度、储物柜、连上
        ttk.Label(form, text="喜爱度").grid(row=3, column=0, sticky="w", pady=3)
        self.course_like_var = tk.StringVar(value="3 一般")
        ttk.Combobox(
            form,
            textvariable=self.course_like_var,
            values=["1 很不喜欢", "2 不喜欢", "3 一般", "4 喜欢", "5 很喜欢"],
            state="readonly",
            width=11,
        ).grid(row=3, column=1, sticky="w", padx=(8, 0), pady=3)

        # 储物柜、连上复选框放在同一行
        opt_frame = ttk.Frame(form)
        opt_frame.grid(row=4, column=0, columnspan=4, sticky="w", pady=3)
        self.course_locker_var = tk.BooleanVar(value=False)
        self.course_linked_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(opt_frame, text="需去储物柜拿书", variable=self.course_locker_var).pack(side="left", padx=(0, 12))
        ttk.Checkbutton(opt_frame, text="两节连上(相邻时段)", variable=self.course_linked_var).pack(side="left")

        # 第4行：每天最多节数（保留作为约束）
        ttk.Label(form, text="每天最多").grid(row=3, column=2, sticky="e", pady=3)
        self.course_perday_var = tk.StringVar(value="2")
        ttk.Spinbox(
            form,
            from_=1,
            to=len(DAYS),
            textvariable=self.course_perday_var,
            width=6,
        ).grid(row=3, column=3, sticky="w", padx=(8, 0), pady=3)

        # 按钮行
        buttons = ttk.Frame(form)
        buttons.grid(row=5, column=0, columnspan=4, sticky="ew", pady=(8, 0))
        ttk.Button(buttons, text="添加课程", style="Soft.TButton", command=self.add_course).pack(
            side="left"
        )
        ttk.Button(
            buttons, text="更新选中", style="Soft.TButton", command=self.update_course
        ).pack(side="left", padx=6)
        ttk.Button(
            buttons, text="删除选中", style="Soft.TButton", command=self.delete_course
        ).pack(side="left")
        ttk.Button(buttons, text="清空表单", style="Soft.TButton", command=self.clear_course_form).pack(
            side="right"
        )

        # 课程列表
        tree_frame = ttk.Frame(tab)
        tree_frame.grid(row=3, column=0, sticky="nsew")
        tree_frame.columnconfigure(0, weight=1)
        tree_frame.rowconfigure(0, weight=1)

        columns = ("name", "location", "location2", "lesson", "perday", "prep", "like", "locker", "linked")
        self.course_tree = ttk.Treeview(
            tree_frame, columns=columns, show="headings", selectmode="browse", height=9
        )
        headings = {
            "name": "课程",
            "location": "主地点",
            "location2": "第二地点",
            "lesson": "周课时",
            "perday": "每天最多",
            "prep": "准备",
            "like": "喜爱",
            "locker": "储物柜",
            "linked": "连上",
        }
        widths = {"name": 90, "location": 90, "location2": 80, "lesson": 60, "perday": 55, "prep": 50, "like": 50, "locker": 55, "linked": 55}
        for column in columns:
            self.course_tree.heading(column, text=headings[column])
            self.course_tree.column(column, width=widths[column], minwidth=widths[column], stretch=False, anchor="center")
        self.course_tree.column("name", anchor="w")
        self.course_tree.column("location", anchor="w")
        self.course_tree.column("location2", anchor="w")
        self.course_tree.grid(row=0, column=0, sticky="nsew")

        scroll = ttk.Scrollbar(tree_frame, orient="vertical", command=self.course_tree.yview)
        scroll.grid(row=0, column=1, sticky="ns")
        self.course_tree.configure(yscrollcommand=scroll.set)
        tree_horizontal = ttk.Scrollbar(tree_frame, orient="horizontal", command=self.course_tree.xview)
        tree_horizontal.grid(row=1, column=0, sticky="ew")
        self.course_tree.configure(xscrollcommand=tree_horizontal.set)
        self.course_tree.bind("<Double-1>", self._load_selected_course_into_form)

        ttk.Label(
            tab,
            text="小提示：双击课程可载入表单修改；喜爱度只作为最后的打破平局因素。",
            style="Muted.TLabel",
            wraplength=430,
        ).grid(row=4, column=0, sticky="w", pady=(8, 0))

    def _build_location_tab(self) -> None:
        tab = self.location_tab
        tab.columnconfigure(0, weight=1)
        tab.rowconfigure(3, weight=1)

        ttk.Label(tab, text="校园地点", style="Section.TLabel").grid(
            row=0, column=0, sticky="w", pady=(0, 2)
        )
        ttk.Label(
            tab,
            text="路程单位为步行分钟。修改矩阵中的一格会同步更新往返时间。",
            style="Muted.TLabel",
            wraplength=430,
        ).grid(row=1, column=0, sticky="w", pady=(0, 8))

        add_row = ttk.Frame(tab)
        add_row.grid(row=2, column=0, sticky="ew", pady=(0, 8))
        add_row.columnconfigure(0, weight=1)
        self.location_name_var = tk.StringVar()
        ttk.Entry(add_row, textvariable=self.location_name_var).grid(
            row=0, column=0, sticky="ew", padx=(0, 6)
        )
        ttk.Button(add_row, text="添加地点", style="Soft.TButton", command=self.add_location).grid(
            row=0, column=1
        )

        list_frame = ttk.Frame(tab)
        list_frame.grid(row=3, column=0, sticky="nsew")
        list_frame.columnconfigure(0, weight=1)
        list_frame.rowconfigure(0, weight=1)
        self.location_list = tk.Listbox(
            list_frame,
            height=11,
            activestyle="none",
            borderwidth=1,
            relief="solid",
            highlightthickness=0,
            selectbackground="#dbeafe",
            selectforeground=self.COLORS["ink"],
            font=(self.font_family, 12),
        )
        self.location_list.grid(row=0, column=0, sticky="nsew")
        loc_scroll = ttk.Scrollbar(list_frame, orient="vertical", command=self.location_list.yview)
        loc_scroll.grid(row=0, column=1, sticky="ns")
        self.location_list.configure(yscrollcommand=loc_scroll.set)

        actions = ttk.Frame(tab)
        actions.grid(row=4, column=0, sticky="ew", pady=(8, 0))
        ttk.Button(
            actions, text="编辑路程矩阵…", style="Soft.TButton", command=self.open_matrix_editor
        ).pack(side="left")
        ttk.Button(
            actions, text="删除选中地点", style="Soft.TButton", command=self.delete_location
        ).pack(side="left", padx=6)

        ttk.Label(
            tab,
            text="示例路程为估算值，请按真实校园路线修改。删除地点前需先删除引用它的课程。",
            style="Muted.TLabel",
            wraplength=430,
        ).grid(row=5, column=0, sticky="w", pady=(8, 0))

    def _build_config_tab(self) -> None:
        tab = self.config_tab
        tab.columnconfigure(1, weight=1)
        tab.columnconfigure(2, weight=0)
        tab.columnconfigure(3, weight=0)

        ttk.Label(tab, text="时间设置", style="Section.TLabel").grid(
            row=0, column=0, columnspan=3, sticky="w", pady=(0, 8)
        )

        self.config_vars: dict[str, tk.StringVar] = {
            "periods_per_day": tk.StringVar(value=str(DEFAULT_CONFIG["periods_per_day"])),
            "break_minutes": tk.StringVar(value=str(DEFAULT_CONFIG.get("break_minutes", 10))),
            "pref_weight": tk.StringVar(value=str(DEFAULT_CONFIG["pref_weight"])),
            "morning_meeting_location": tk.StringVar(value=DEFAULT_CONFIG["morning_meeting_location"]),
            "morning_meeting_gap": tk.StringVar(value=str(DEFAULT_CONFIG["morning_meeting_gap"])),
            "order_meal_location": tk.StringVar(value=DEFAULT_CONFIG["order_meal_location"]),
            "locker_location": tk.StringVar(value=DEFAULT_CONFIG.get("locker_location", "中兴楼地下一层")),
        }
        self.morning_var = tk.BooleanVar(value=DEFAULT_CONFIG.get("morning_meeting", True))
        self.meal_var = tk.BooleanVar(value=DEFAULT_CONFIG.get("order_meal", True))

        ttk.Label(tab, text="课表固定").grid(row=1, column=0, sticky="w", pady=4)
        ttk.Label(
            tab,
            text="8.30-9.30、9.40-10.20、10.30-11.10、11.20-12.05、13.15-14.10、14.20-15.00、15.10-15.50（周五不上最后两节）",
            style="Muted.TLabel",
            wraplength=380,
        ).grid(row=1, column=1, columnspan=2, sticky="w", padx=(10, 0), pady=4)

        ttk.Checkbutton(tab, text="增加晨会（第一节课前）", variable=self.morning_var).grid(
            row=2, column=0, columnspan=2, sticky="w", pady=4
        )
        ttk.Label(tab, text="晨会地点").grid(row=3, column=0, sticky="w", pady=4)
        self.morning_combo = ttk.Combobox(
            tab, textvariable=self.config_vars["morning_meeting_location"], state="readonly", width=14
        )
        self.morning_combo.grid(row=3, column=1, sticky="w", padx=(10, 8), pady=4)

        ttk.Label(tab, text="晨会到第1节的间隔").grid(row=4, column=0, sticky="w", pady=4)
        gap_box = ttk.Frame(tab)
        gap_box.grid(row=4, column=1, columnspan=2, sticky="w", padx=(10, 8), pady=4)
        ttk.Spinbox(
            gap_box,
            from_=0,
            to=60,
            increment=1,
            textvariable=self.config_vars["morning_meeting_gap"],
            width=7,
        ).pack(side="left")
        ttk.Label(gap_box, text="分钟", style="Muted.TLabel").pack(side="left", padx=(5, 0))

        ttk.Checkbutton(tab, text="第1-2节课间增加订餐（9.30课后）", variable=self.meal_var).grid(
            row=5, column=0, columnspan=2, sticky="w", pady=4
        )
        ttk.Label(tab, text="订餐地点").grid(row=6, column=0, sticky="w", pady=4)
        self.meal_combo = ttk.Combobox(
            tab, textvariable=self.config_vars["order_meal_location"], state="readonly", width=14
        )
        self.meal_combo.grid(row=6, column=1, sticky="w", padx=(10, 8), pady=4)
        ttk.Label(tab, text="储物柜位置").grid(row=7, column=0, sticky="w", pady=4)
        self.locker_combo = ttk.Combobox(
            tab, textvariable=self.config_vars["locker_location"], state="readonly", width=14
        )
        self.locker_combo.grid(row=7, column=1, sticky="w", padx=(10, 8), pady=4)

        ttk.Label(tab, text="喜好平衡权重").grid(row=8, column=0, sticky="w", pady=4)
        ttk.Spinbox(tab, from_=0, to=10, increment=0.5, textvariable=self.config_vars["pref_weight"], width=8).grid(
            row=8, column=1, sticky="w", padx=(10, 8), pady=4
        )
        ttk.Label(tab, text="0 = 完全时间优先", style="Muted.TLabel").grid(row=8, column=2, sticky="w", pady=4)

        for key in self.config_vars:
            self.config_vars[key].trace_add("write", lambda *_: self._on_config_changed())
        self.morning_var.trace_add("write", lambda *_: self._on_config_changed())
        self.meal_var.trace_add("write", lambda *_: self._on_config_changed())

        self.time_preview_var = tk.StringVar()
        ttk.Label(
            tab,
            textvariable=self.time_preview_var,
            style="Muted.TLabel",
            wraplength=380,
            justify="left",
        ).grid(row=9, column=0, columnspan=3, sticky="w", pady=(10, 0))

        ttk.Separator(tab, orient="horizontal").grid(
            row=11, column=0, columnspan=3, sticky="ew", pady=12
        )
        ttk.Label(tab, text="排序目标（越小越好）", style="Section.TLabel").grid(
            row=12, column=0, columnspan=3, sticky="w", pady=(0, 4)
        )
        ttk.Label(
            tab,
            text=(
                "移动时间（含晨会/订餐/储物柜绕行）\n"
                "+ 60 × 路程冲突分钟\n"
                "+ 25 × 准备不足分钟\n"
                "+ 喜好权重 × 喜好相邻次数\n"
                "移动优先，喜好只用于耗时接近时平衡。"
            ),
            style="Muted.TLabel",
            wraplength=420,
            justify="left",
        ).grid(row=13, column=0, columnspan=3, sticky="w")

    def _build_right_panel(self, parent: ttk.Frame) -> None:
        parent.columnconfigure(0, weight=1)
        parent.rowconfigure(3, weight=1)

        summary = tk.Frame(
            parent,
            bg="#eaf1ff",
            highlightbackground="#c7d9fb",
            highlightthickness=1,
            padx=14,
            pady=8,
        )
        summary.grid(row=0, column=0, sticky="ew", pady=(0, 8))
        summary.columnconfigure(0, weight=1)

        self.headline_var = tk.StringVar(value="等待生成课表…")
        self.subline_var = tk.StringVar(value="综合评分越低，说明路程与准备时间安排得越好。")
        tk.Label(
            summary,
            textvariable=self.headline_var,
            bg="#eaf1ff",
            fg=self.COLORS["ink"],
            font=(self.font_family, 16, "bold"),
            anchor="w",
        ).grid(row=0, column=0, sticky="w")
        tk.Label(
            summary,
            textvariable=self.subline_var,
            bg="#eaf1ff",
            fg=self.COLORS["muted"],
            font=(self.font_family, 9),
            anchor="w",
        ).grid(row=1, column=0, sticky="w", pady=(2, 0))

        # Compact before/after cards keep the timetable visible on laptop screens.
        strip = tk.Frame(parent, bg=self.COLORS["bg"])
        strip.grid(row=1, column=0, sticky="ew", pady=(0, 4))
        self.metric_vars: dict[str, tuple[tk.StringVar, tk.StringVar]] = {}
        self.metric_labels: dict[str, tk.Label] = {}
        tile_specs = [
            ("score", "综合评分"),
            ("travel", "移动时间"),
            ("prep", "准备不足"),
            ("conflict", "路程冲突"),
            ("pref", "喜好相邻"),
        ]
        metric_cards = []
        for column, (key, title) in enumerate(tile_specs):
            strip.columnconfigure(column, weight=1, uniform="metric")
            card = tk.Frame(
                strip,
                bg=self.COLORS["surface"],
                highlightbackground=self.COLORS["line"],
                highlightthickness=1,
                padx=9,
                pady=5,
            )
            card.grid(
                row=0,
                column=column,
                sticky="nsew",
                padx=(0 if column == 0 else 5, 0),
            )
            metric_cards.append(card)
            tk.Label(
                card,
                text=title,
                bg=self.COLORS["surface"],
                fg=self.COLORS["muted"],
                font=(self.font_family, 9),
                anchor="w",
            ).pack(anchor="w")
            value_var = tk.StringVar(value="— → —")
            delta_var = tk.StringVar(value="等待生成")
            tk.Label(
                card,
                textvariable=value_var,
                bg=self.COLORS["surface"],
                fg=self.COLORS["ink"],
                font=(self.font_family, 12, "bold"),
                anchor="w",
            ).pack(anchor="w")
            delta_label = tk.Label(
                card,
                textvariable=delta_var,
                bg=self.COLORS["surface"],
                fg=self.COLORS["muted"],
                font=(self.font_family, 8),
                anchor="w",
            )
            delta_label.pack(anchor="w")
            self.metric_vars[key] = (value_var, delta_var)
            self.metric_labels[key] = delta_label

        def layout_metrics(event) -> None:
            if event.widget is not strip:
                return
            columns = 5 if event.width >= 680 else (3 if event.width >= 400 else 2)
            for column in range(5):
                strip.columnconfigure(column, weight=1 if column < columns else 0,
                                      uniform="metric" if column < columns else "")
            for index, card in enumerate(metric_cards):
                card.grid_configure(row=index // columns, column=index % columns,
                                    padx=(0 if index % columns == 0 else 5, 0), pady=(0, 5))
        strip.bind("<Configure>", layout_metrics)

        ttk.Label(parent, text="周课表", style="Section.TLabel").grid(
            row=2, column=0, sticky="w", pady=(8, 5)
        )

        canvas_frame = tk.Frame(
            parent,
            bg=self.COLORS["surface"],
            highlightbackground=self.COLORS["line"],
            highlightthickness=1,
        )
        canvas_frame.grid(row=3, column=0, sticky="nsew")
        canvas_frame.columnconfigure(0, weight=1)
        canvas_frame.rowconfigure(0, weight=1)

        self.schedule_canvas = tk.Canvas(
            canvas_frame,
            bg=self.COLORS["surface"],
            highlightthickness=0,
            bd=0,
        )
        self.schedule_canvas.grid(row=0, column=0, sticky="nsew")
        canvas_scroll = ttk.Scrollbar(
            canvas_frame, orient="vertical", command=self.schedule_canvas.yview
        )
        canvas_scroll.grid(row=0, column=1, sticky="ns")
        self.schedule_canvas.configure(yscrollcommand=canvas_scroll.set)
        canvas_horizontal = ttk.Scrollbar(canvas_frame, orient="horizontal", command=self.schedule_canvas.xview)
        canvas_horizontal.grid(row=1, column=0, sticky="ew")
        self.schedule_canvas.configure(xscrollcommand=canvas_horizontal.set)
        self.schedule_canvas.bind("<Configure>", lambda _event: self._redraw_timetable())
        self.schedule_canvas.bind_all(
            "<MouseWheel>",
            lambda event: self._on_mousewheel(event),
            add="+",
        )

    # ------------------------------------------------------------------
    # Data refresh helpers
    # ------------------------------------------------------------------

    def _refresh_all(self) -> None:
        self._refresh_course_tree()
        self._refresh_locations()
        self._refresh_config_vars()
        self._update_time_preview()

    def _refresh_course_tree(self) -> None:
        selected = self.course_tree.selection()
        self.course_tree.delete(*self.course_tree.get_children())
        for index, course in enumerate(self.courses):
            label = {1: "很不喜欢", 2: "不喜欢", 3: "一般", 4: "喜欢", 5: "很喜欢"}.get(
                course.like, str(course.like)
            )
            locker_text = "是" if course.locker else "否"
            linked_text = "是" if course.linked else "否"
            self.course_tree.insert(
                "",
                "end",
                iid=str(index),
                values=(
                    course.name,
                    course.location,
                    course.location2 or "（无）",
                    f"{course.lesson_minutes}′",
                    course.per_day_max,
                    f"{course.prep}′",
                    f"{course.like} {label}",
                    locker_text,
                    linked_text,
                ),
            )
        if selected and selected[0] in self.course_tree.get_children():
            self.course_tree.selection_set(selected[0])

    def _refresh_locations(self) -> None:
        self.location_list.delete(0, "end")
        for location in self.locations:
            self.location_list.insert("end", location)
        self.course_location_combo.configure(values=self.locations)
        loc2_values = ["（无）"] + self.locations
        self.course_location2_combo.configure(values=loc2_values)
        if hasattr(self, "morning_combo"):
            self.morning_combo.configure(values=self.locations)
        if hasattr(self, "meal_combo"):
            self.meal_combo.configure(values=self.locations)
        if hasattr(self, "locker_combo"):
            self.locker_combo.configure(values=self.locations)
        if self.course_location_var.get() not in self.locations:
            self.course_location_var.set(self.locations[0] if self.locations else "")
        if self.course_location2_var.get() not in loc2_values:
            self.course_location2_var.set("（无）")
        if hasattr(self, "config_vars") and self.config_vars.get("morning_meeting_location") and self.config_vars["morning_meeting_location"].get() not in self.locations:
            if self.locations:
                self.config_vars["morning_meeting_location"].set(self.locations[0])
        if hasattr(self, "config_vars") and self.config_vars.get("order_meal_location") and self.config_vars["order_meal_location"].get() not in self.locations:
            if self.locations:
                self.config_vars["order_meal_location"].set(self.locations[0])
        if hasattr(self, "config_vars") and self.config_vars.get("locker_location") and self.config_vars["locker_location"].get() not in self.locations:
            if self.locations:
                self.config_vars["locker_location"].set(self.locations[0])

    def _refresh_config_vars(self) -> None:
        if "break_minutes" in self.config_vars:
            self.config_vars["break_minutes"].set(str(self.config.get("break_minutes", DEFAULT_CONFIG.get("break_minutes", 10))))
        if "pref_weight" in self.config_vars:
            self.config_vars["pref_weight"].set(str(self.config.get("pref_weight", DEFAULT_CONFIG.get("pref_weight", 2.5))))
        if "morning_meeting_location" in self.config_vars:
            self.config_vars["morning_meeting_location"].set(self.config.get("morning_meeting_location", DEFAULT_CONFIG.get("morning_meeting_location", "中兴楼地下一层")))
        if "morning_meeting_gap" in self.config_vars:
            self.config_vars["morning_meeting_gap"].set(str(self.config.get("morning_meeting_gap", DEFAULT_CONFIG.get("morning_meeting_gap", 10))))
        if "order_meal_location" in self.config_vars:
            self.config_vars["order_meal_location"].set(self.config.get("order_meal_location", DEFAULT_CONFIG.get("order_meal_location", "中兴楼一楼")))
        if "locker_location" in self.config_vars:
            self.config_vars["locker_location"].set(self.config.get("locker_location", DEFAULT_CONFIG.get("locker_location", "中兴楼地下一层")))
        if hasattr(self, "morning_var"):
            self.morning_var.set(bool(self.config.get("morning_meeting", DEFAULT_CONFIG.get("morning_meeting", True))))
        if hasattr(self, "meal_var"):
            self.meal_var.set(bool(self.config.get("order_meal", DEFAULT_CONFIG.get("order_meal", True))))
        self._update_time_preview()

    def _read_config(self) -> dict:
        try:
            config = dict(DEFAULT_CONFIG)
            config["periods_per_day"] = 7
            config["break_minutes"] = int(self.config_vars["break_minutes"].get())
            config["pref_weight"] = float(self.config_vars["pref_weight"].get())
            config["morning_meeting"] = bool(self.morning_var.get())
            config["morning_meeting_location"] = self.config_vars["morning_meeting_location"].get()
            config["morning_meeting_gap"] = int(self.config_vars["morning_meeting_gap"].get())
            config["order_meal"] = bool(self.meal_var.get())
            config["order_meal_location"] = self.config_vars["order_meal_location"].get()
            config["order_meal_after_period"] = 1
            config["locker_location"] = self.config_vars["locker_location"].get()
        except ValueError as exc:
            raise ValueError("时间或权重设置中有无效数字") from exc
        validate_config(config)
        return config

    def _on_config_changed(self) -> None:
        self._update_time_preview()
        if self._config_autosave_id is not None:
            try:
                self.root.after_cancel(self._config_autosave_id)
            except Exception:
                pass
        self._config_autosave_id = self.root.after(500, self._config_autosave)

    def _config_autosave(self) -> None:
        self._config_autosave_id = None
        self._autosave()

    def _on_close(self) -> None:
        self._autosave()
        self.root.destroy()

    def _update_time_preview(self) -> None:
        if not hasattr(self, "time_preview_var"):
            return
        try:
            meal_loc = self.config_vars.get("order_meal_location")
            morn_loc = self.config_vars.get("morning_meeting_location")
            meal = (
                f"启用订餐（9:30课后，{meal_loc.get() if meal_loc else '中兴楼一楼'}）"
                if getattr(self, "meal_var", None) and self.meal_var.get()
                else "未启用订餐"
            )
            gap_var = self.config_vars.get("morning_meeting_gap")
            morn = (
                f"启用晨会（第1节前，{morn_loc.get() if morn_loc else '中兴楼地下一层'}，"
                f"晨会后 {gap_var.get() if gap_var else '10'} 分钟到第1节）"
                if getattr(self, "morning_var", None) and self.morning_var.get()
                else "未启用晨会"
            )
            locker_loc = self.config_vars.get("locker_location")
            locker = f"；储物柜 {locker_loc.get() if locker_loc else '中兴楼地下一层'}" if getattr(self, "course_locker_var", None) and self.course_locker_var.get() else ""
            self.time_preview_var.set(f"{morn}；{meal}{locker}")
        except Exception as exc:
            self.time_preview_var.set(f"设置待修正：{exc}")

    # ------------------------------------------------------------------
    # Course CRUD
    # ------------------------------------------------------------------

    def _course_form_values(self):
        name = self.course_name_var.get().strip()
        location = self.course_location_var.get().strip()
        location2 = self.course_location2_var.get().strip()
        if location2 == "（无）":
            location2 = ""
        if not name:
            raise ValueError("请填写课程名")
        if location not in self.locations:
            raise ValueError("请选择有效地点")
        if location2 and location2 not in self.locations:
            raise ValueError("请选择有效第二地点")
        if location2 and location2 == location:
            raise ValueError("第二地点不能与主地点相同")
        try:
            prep = int(self.course_prep_var.get())
            lesson_minutes = int(self.course_lesson_var.get())
            per_day_max = int(self.course_perday_var.get())
        except ValueError as exc:
            raise ValueError("准备时间、周课时、每天最多必须是整数") from exc
        like_text = self.course_like_var.get().strip()
        if not like_text or not like_text[0].isdigit():
            raise ValueError("请选择喜爱度")
        like = int(like_text[0])
        if not 1 <= lesson_minutes <= 2100:
            raise ValueError("周课时应在 1–2100 分钟之间")
        if not 1 <= per_day_max <= len(DAYS):
            raise ValueError("每天最多节数应在 1–5 之间")
        if not 0 <= prep <= 180:
            raise ValueError("课前准备时间应在 0–180 分钟之间")
        if not 1 <= like <= 5:
            raise ValueError("喜爱度应为 1–5")
        return (
            name,
            location,
            location2,
            lesson_minutes,
            prep,
            like,
            per_day_max,
            self.course_locker_var.get(),
            self.course_linked_var.get(),
        )

    def add_course(self) -> None:
        try:
            (name, location, location2, lesson_minutes, prep, like, per_day_max,
             locker, linked) = self._course_form_values()
        except ValueError as exc:
            messagebox.showwarning("无法添加", str(exc), parent=self.root)
            return
        if name in {course.name for course in self.courses}:
            messagebox.showwarning("无法添加", f"课程「{name}」已存在", parent=self.root)
            return
        self.courses.append(Course(
            name=name,
            location=location,
            lesson_minutes=lesson_minutes,
            prep=prep,
            like=like,
            location2=location2,
            per_day_max=per_day_max,
            locker=locker,
            linked=linked,
        ))
        self._refresh_course_tree()
        self.clear_course_form()
        self.status_var.set(f"已添加课程：{name}")
        self._autosave()

    def update_course(self) -> None:
        selection = self.course_tree.selection()
        if not selection:
            messagebox.showinfo("更新课程", "请先在列表中选择要更新的课程。", parent=self.root)
            return
        index = int(selection[0])
        try:
            (name, location, location2, lesson_minutes, prep, like, per_day_max,
             locker, linked) = self._course_form_values()
        except ValueError as exc:
            messagebox.showwarning("无法更新", str(exc), parent=self.root)
            return
        if name in {course.name for i, course in enumerate(self.courses) if i != index}:
            messagebox.showwarning("无法更新", f"课程「{name}」已存在", parent=self.root)
            return
        self.courses[index] = Course(
            name=name,
            location=location,
            lesson_minutes=lesson_minutes,
            prep=prep,
            like=like,
            location2=location2,
            per_day_max=per_day_max,
            locker=locker,
            linked=linked,
        )
        self._refresh_course_tree()
        self.status_var.set(f"已更新课程：{name}")
        self._autosave()

    def delete_course(self) -> None:
        selection = self.course_tree.selection()
        if not selection:
            messagebox.showinfo("删除课程", "请先在列表中选择要删除的课程。", parent=self.root)
            return
        index = int(selection[0])
        course = self.courses[index]
        if not messagebox.askyesno(
            "删除课程", f"确定删除「{course.name}」吗？", parent=self.root
        ):
            return
        del self.courses[index]
        self._refresh_course_tree()
        self.clear_course_form()
        self.status_var.set(f"已删除课程：{course.name}")
        self._autosave()

    def clear_course_form(self) -> None:
        self.course_name_var.set("")
        self.course_lesson_var.set("60")
        self.course_perday_var.set("2")
        self.course_prep_var.set("0")
        self.course_like_var.set("3 一般")
        self.course_locker_var.set(False)
        self.course_linked_var.set(False)
        self.course_location2_var.set("（无）")
        if self.locations:
            self.course_location_var.set(self.locations[0])
        self.course_tree.selection_remove(*self.course_tree.selection())

    def _load_selected_course_into_form(self, _event=None) -> None:
        selection = self.course_tree.selection()
        if not selection:
            return
        course = self.courses[int(selection[0])]
        self.course_name_var.set(course.name)
        self.course_location_var.set(course.location)
        self.course_location2_var.set(course.location2 or "（无）")
        self.course_lesson_var.set(str(course.lesson_minutes))
        self.course_perday_var.set(str(course.per_day_max))
        self.course_prep_var.set(str(course.prep))
        like_labels = {
            1: "1 很不喜欢",
            2: "2 不喜欢",
            3: "3 一般",
            4: "4 喜欢",
            5: "5 很喜欢",
        }
        self.course_like_var.set(like_labels.get(course.like, "3 一般"))
        self.course_locker_var.set(bool(course.locker))
        self.course_linked_var.set(bool(course.linked))
        self.status_var.set(f"已载入「{course.name}」到表单，可修改后点「更新选中」。")

    # ------------------------------------------------------------------
    # Location CRUD and travel matrix
    # ------------------------------------------------------------------

    def add_location(self) -> None:
        name = self.location_name_var.get().strip()
        if not name:
            messagebox.showwarning("添加地点", "请填写地点名称。", parent=self.root)
            return
        if name in self.locations:
            messagebox.showwarning("添加地点", f"地点「{name}」已存在。", parent=self.root)
            return
        if len(self.locations) >= 16:
            messagebox.showwarning("添加地点", "原型最多支持 16 个地点。", parent=self.root)
            return
        self.locations.append(name)
        for row in self.travel:
            row.append(3)
        self.travel.append([3] * len(self.locations))
        self.travel[-1][-1] = 0
        self.location_name_var.set("")
        self._refresh_locations()
        self._refresh_course_tree()
        self.status_var.set(f"已添加地点：{name}（默认路程 3 分钟，可在矩阵中修改）")
        self._autosave()

    def delete_location(self) -> None:
        selection = self.location_list.curselection()
        if not selection:
            messagebox.showinfo("删除地点", "请先选择一个地点。", parent=self.root)
            return
        index = selection[0]
        name = self.locations[index]
        used = [course.name for course in self.courses if course.location == name or course.location2 == name]
        if used:
            messagebox.showwarning(
                "无法删除",
                f"地点「{name}」仍被以下课程使用：{', '.join(used)}。请先修改课程地点。",
                parent=self.root,
            )
            return
        if not messagebox.askyesno("删除地点", f"确定删除「{name}」及其路程数据吗？", parent=self.root):
            return
        self.locations.pop(index)
        self.travel.pop(index)
        for row in self.travel:
            row.pop(index)
        self._refresh_locations()
        self._refresh_course_tree()
        self.status_var.set(f"已删除地点：{name}")
        self._autosave()

    def open_matrix_editor(self) -> None:
        if self._matrix_window is not None and self._matrix_window.winfo_exists():
            self._matrix_window.lift()
            return

        window = tk.Toplevel(self.root)
        self._matrix_window = window
        window.title("编辑路程矩阵")
        window.transient(self.root)
        window.configure(bg=self.COLORS["surface"])
        window.resizable(False, False)

        top = ttk.Frame(window, padding=(16, 14, 16, 8))
        top.pack(fill="x")
        ttk.Label(top, text="步行时间矩阵", style="Section.TLabel").pack(anchor="w")
        ttk.Label(
            top,
            text="单位：分钟。矩阵自动保持对称，例如修改「中兴楼→逸夫楼」会同时更新反向路程。",
            style="Muted.TLabel",
            wraplength=620,
        ).pack(anchor="w", pady=(3, 0))

        grid = ttk.Frame(window, padding=(16, 6, 16, 12))
        grid.pack(fill="both", expand=True)

        ttk.Label(grid, text="从 \\ 到", style="Muted.TLabel").grid(
            row=0, column=0, padx=3, pady=3, sticky="e"
        )
        for j, location in enumerate(self.locations):
            ttk.Label(
                grid, text=location, style="Muted.TLabel", wraplength=54, justify="center"
            ).grid(row=0, column=j + 1, padx=3, pady=3)

        self._matrix_vars = {}
        for i, location in enumerate(self.locations):
            ttk.Label(grid, text=location, style="Muted.TLabel").grid(
                row=i + 1, column=0, padx=3, pady=3, sticky="e"
            )
            for j in range(len(self.locations)):
                var = tk.StringVar(value=str(self.travel[i][j]))
                entry = ttk.Entry(grid, textvariable=var, width=5, justify="center")
                entry.grid(row=i + 1, column=j + 1, padx=2, pady=2)
                if i == j:
                    entry.state(["disabled"])
                else:
                    entry.bind(
                        "<FocusOut>",
                        lambda _e, ii=i, jj=j: self._commit_matrix_cell(ii, jj),
                    )
                    entry.bind(
                        "<Return>",
                        lambda _e, ii=i, jj=j: self._commit_matrix_cell(ii, jj),
                    )
                self._matrix_vars[(i, j)] = var

        bottom = ttk.Frame(window, padding=(16, 0, 16, 16))
        bottom.pack(fill="x")
        ttk.Button(
            bottom,
            text="应用并关闭",
            style="Accent.TButton",
            command=self._close_matrix_editor,
        ).pack(side="right")
        ttk.Label(
            bottom,
            text="建议范围 0–30 分钟；对角线固定为 0。",
            style="Muted.TLabel",
        ).pack(side="left")

        window.protocol("WM_DELETE_WINDOW", self._close_matrix_editor)
        window.grab_set()

    def _commit_matrix_cell(self, i: int, j: int) -> None:
        if self._matrix_guard or i == j:
            return
        var = self._matrix_vars.get((i, j))
        if var is None:
            return
        try:
            value = int(var.get())
            if not 0 <= value <= 60:
                raise ValueError
        except ValueError:
            var.set(str(self.travel[i][j]))
            self.status_var.set("路程必须是 0–60 的整数分钟，已恢复原值。")
            return
        self.travel[i][j] = value
        self.travel[j][i] = value
        self._matrix_guard = True
        reverse = self._matrix_vars.get((j, i))
        if reverse is not None:
            reverse.set(str(value))
        var.set(str(value))
        self._matrix_guard = False

    def _close_matrix_editor(self) -> None:
        for (i, j), _var in list(self._matrix_vars.items()):
            if i != j:
                self._commit_matrix_cell(i, j)
        if self._matrix_window is not None:
            try:
                self._matrix_window.grab_release()
            except Exception:
                pass
            self._matrix_window.destroy()
            self._matrix_window = None
        self.status_var.set("路程矩阵已更新。")
        self._autosave()

    # ------------------------------------------------------------------
    # Generate and display
    # ------------------------------------------------------------------

    def generate(self) -> None:
        if self._generating:
            return
        try:
            config = self._read_config()
            validate_problem(self.courses, self.locations, self.travel)
            total_minutes = sum(course.lesson_minutes for course in self.courses)
            total_capacity_minutes = weekly_capacity(build_periods(config))
            if total_minutes > total_capacity_minutes:
                raise ValueError(
                    f"共需 {total_minutes} 分钟课时，但一周只有 "
                    f"{total_capacity_minutes} 分钟可用时段"
                )
        except ValueError as exc:
            messagebox.showwarning("无法生成课表", str(exc), parent=self.root)
            return

        self.config = config
        self._update_time_preview()
        self._generating = True
        self.generate_button.state(["disabled"])
        self.status_var.set("正在优化课表… 综合考量移动、准备时间与喜好平衡。")
        self._generation_queue = queue.Queue()

        courses_snapshot = [course.copy() for course in self.courses]
        locations_snapshot = list(self.locations)
        travel_snapshot = [row[:] for row in self.travel]
        config_snapshot = dict(config)

        def worker() -> None:
            try:
                result = solve(
                    courses_snapshot,
                    locations_snapshot,
                    travel_snapshot,
                    config_snapshot,
                    seed=2026,
                    restarts=5,
                    iterations=12000,
                )
                self._generation_queue.put(("ok", result))
            except ValueError as exc:
                self._generation_queue.put(("error", str(exc)))
            except Exception:
                self._generation_queue.put(("error", traceback.format_exc()))

        threading.Thread(target=worker, daemon=True).start()
        self.root.after(80, self._poll_generation)

    def _poll_generation(self) -> None:
        try:
            kind, payload = self._generation_queue.get_nowait()
        except queue.Empty:
            if self._generating:
                self.root.after(80, self._poll_generation)
            return

        self._generating = False
        self.generate_button.state(["!disabled"])

        if kind == "error":
            self.status_var.set("生成失败。")
            messagebox.showerror("生成失败", str(payload), parent=self.root)
            return

        result: SolveResult = payload
        self.result = result
        self.display_courses = result.courses
        self.display_config = result.config
        self._show_result(result)
        self.status_var.set(
            f"完成：{len(result.courses)} 门课、{result.best_metrics.classes} 节、"
            f"{sum(c.lesson_minutes for c in result.courses)} 分钟，课时全部匹配。用时 {result.elapsed:.2f} 秒。"
        )
        self._autosave()

    def _show_result(self, result: SolveResult) -> None:
        before = result.baseline_metrics
        after = result.best_metrics
        reduction = 0.0
        if before.cost > 0:
            reduction = (before.cost - after.cost) / before.cost * 100
        self.headline_var.set(
            f"综合评分 {before.cost:.1f} → {after.cost:.1f}    ↓ {reduction:.1f}%"
        )
        self.subline_var.set(
            f"移动 {before.travel} → {after.travel} 分钟（含晨会 {after.morning_travel} / 订餐 {after.meal_travel}；储物柜已并入此总计）"
            f" · 准备不足 {before.prep_short} → {after.prep_short} 分钟"
            f" · 路程冲突 {before.conflict_minutes} → {after.conflict_minutes} 分钟"
        )

        cards = [
            ("score", f"{before.cost:.1f}", f"{after.cost:.1f}", self._percent_change(before.cost, after.cost)),
            ("travel", f"{before.travel}", f"{after.travel}", self._absolute_change(before.travel, after.travel, "分钟")),
            ("prep", f"{before.prep_short}", f"{after.prep_short}", self._absolute_change(before.prep_short, after.prep_short, "分钟")),
            ("conflict", f"{before.conflict_minutes}", f"{after.conflict_minutes}", self._absolute_change(before.conflict_minutes, after.conflict_minutes, "分钟")),
            ("pref", f"{before.pref_clashes}", f"{after.pref_clashes}", self._absolute_change(before.pref_clashes, after.pref_clashes, "次")),
        ]
        for key, old, new, change in cards:
            value_var, delta_var = self.metric_vars[key]
            value_var.set(f"{old} → {new}")
            delta_var.set(change)
            if change.startswith("↓"):
                self.metric_labels[key].configure(fg=self.COLORS["good"])
            elif change.startswith("↑"):
                self.metric_labels[key].configure(fg=self.COLORS["warning"])
            else:
                self.metric_labels[key].configure(fg=self.COLORS["muted"])
        self._redraw_timetable()
        self.schedule_canvas.xview_moveto(0)
        self.schedule_canvas.yview_moveto(0)

    def _reset_metric_cards(self) -> None:
        for value_var, delta_var in self.metric_vars.values():
            value_var.set("— → —")
            delta_var.set("等待生成")
        for label in self.metric_labels.values():
            label.configure(fg=self.COLORS["muted"])

    @staticmethod
    def _percent_change(before: float, after: float) -> str:
        if before <= 0:
            return "—"
        pct = (before - after) / before * 100
        if abs(pct) < 0.05:
            return "0.0%"
        return f"↓ {pct:.1f}%"

    @staticmethod
    def _absolute_change(before: int, after: int, unit: str) -> str:
        diff = before - after
        if diff > 0:
            return f"↓ {diff} {unit}"
        if diff < 0:
            return f"↑ {abs(diff)} {unit}"
        return "0"

    # ------------------------------------------------------------------
    # Timetable drawing
    # ------------------------------------------------------------------

    def _redraw_timetable(self) -> None:
        canvas = self.schedule_canvas
        canvas.delete("all")
        if self.result is None:
            width = max(canvas.winfo_width(), 480)
            height = max(canvas.winfo_height(), 300)
            canvas.create_text(
                width / 2,
                height / 2,
                text="请先添加课程，再点击右上角「生成智能课表」",
                fill=self.COLORS["muted"],
                font=(self.font_family, 13),
                width=max(280, width - 80),
                justify="center",
            )
            canvas.configure(scrollregion=(0, 0, width, height))
            canvas.xview_moveto(0)
            canvas.yview_moveto(0)
            return

        schedule = self.result.best
        courses = self.display_courses
        config = self.display_config
        periods = self.result.periods

        width = max(canvas.winfo_width(), 740)
        height = max(canvas.winfo_height(), 340)
        left_width = 82 if width >= 720 else 72
        pad = 8
        col_gap = 4
        header_height = 36
        day_count = len(DAYS)
        period_count = len(periods)

        meeting_on = bool(config.get("morning_meeting", False))
        meal_on = bool(config.get("order_meal", False))
        band_parts = []
        if meeting_on:
            band_parts.append(
                f"晨会 · {short_location(str(config.get('morning_meeting_location', '')))}（第1节前）"
            )
        if meal_on:
            band_parts.append(
                f"订餐 · {short_location(str(config.get('order_meal_location', '')))}（9:30课后）"
            )
        band_text = "　|　".join(band_parts)
        band_height = 40 if band_text else 0

        available_height = height - header_height - band_height - pad
        row_height = max(80, min(90, available_height / max(1, period_count)))
        col_width = max(
            120,
            (width - left_width - 2 * pad - col_gap * (day_count - 1)) / day_count,
        )
        details = []
        name_heights = []
        for course in courses:
            detail = short_location(course.location)
            if course.location2:
                detail += "/" + short_location(course.location2)
            if course.prep:
                detail += f" · {course.prep}′"
            details.append(detail)
            name_item = canvas.create_text(0, 0, text=course.name, font=self.name_font,
                                           width=col_width - 42, anchor="nw")
            detail_item = canvas.create_text(0, 0, text=detail, font=self.detail_font,
                                             width=col_width - 16, anchor="nw")
            name_box, detail_box = canvas.bbox(name_item), canvas.bbox(detail_item)
            name_height = name_box[3] - name_box[1]
            name_heights.append(name_height)
            row_height = max(row_height, name_height + detail_box[3] - detail_box[1] + 24)
            canvas.delete(name_item, detail_item)
        total_height = header_height + band_height + period_count * row_height + pad
        canvas.configure(scrollregion=(0, 0, width, total_height))
        canvas.create_rectangle(0, 0, width, total_height, fill=self.COLORS["surface"], outline="")

        # Top-left corner and day headers.
        canvas.create_rectangle(
            0, 0, left_width, header_height, fill="#e2e8f0", outline=""
        )
        canvas.create_text(
            left_width / 2,
            header_height / 2,
            text="节次",
            fill=self.COLORS["muted"],
            font=(self.font_family, 9, "bold"),
        )
        for d, day in enumerate(DAYS):
            x = left_width + d * (col_width + col_gap)
            canvas.create_rectangle(
                x, 0, x + col_width, header_height, fill="#e8eef7", outline="#d7e0ec"
            )
            canvas.create_text(
                x + col_width / 2,
                header_height / 2,
                text=day,
                fill=self.COLORS["ink"],
                font=(self.font_family, 11, "bold"),
            )

        # Morning meeting / meal ordering summary band.
        if band_text:
            canvas.create_rectangle(
                pad,
                header_height,
                width - pad,
                header_height + band_height - 4,
                fill="#fff7ed",
                outline="#fdba74",
            )
            canvas.create_text(
                width / 2,
                header_height + (band_height - 4) / 2,
                text=band_text,
                width=width - 32,
                fill="#9a3412",
                font=(self.font_family, 9, "bold"),
            )

        warnings = self._compute_warnings(schedule, courses, periods, config)

        # Period labels and cells.
        for p, period in enumerate(periods):
            y = header_height + band_height + p * row_height
            canvas.create_rectangle(
                0, y, left_width - 4, y + row_height - 4, fill="#f8fafc", outline=""
            )
            canvas.create_text(
                left_width - 10,
                y + row_height / 2 - 9,
                text=f"第 {p + 1} 节",
                anchor="e",
                fill=self.COLORS["ink"],
                font=(self.font_family, 10, "bold"),
            )
            canvas.create_text(
                left_width - 10,
                y + row_height / 2 + 9,
                text=f"{minutes_to_hhmm(period.start)}–{minutes_to_hhmm(period.end)}",
                anchor="e",
                fill=self.COLORS["muted"],
                font=(self.font_family, 8),
            )

            for d in range(day_count):
                if (d, p) in UNAVAILABLE_SLOTS:
                    continue
                x = left_width + d * (col_width + col_gap)
                course_index = schedule[d][p]
                if course_index is None:
                    canvas.create_rectangle(
                        x,
                        y,
                        x + col_width,
                        y + row_height - 4,
                        fill="#f8fafc",
                        outline="#dbe3ee",
                    )
                    continue

                course = courses[course_index]
                warning = (d, p) in warnings
                if course.like >= 4:
                    fill, border = "#dcfce7", "#86efac"
                elif course.like <= 2:
                    fill, border = "#fee2e2", "#fca5a5"
                else:
                    fill, border = "#eef2ff", "#c7d2fe"

                canvas.create_rectangle(
                    x,
                    y,
                    x + col_width,
                    y + row_height - 4,
                    fill=fill,
                    outline="#f59e0b" if warning else border,
                    width=2 if warning else 1,
                )
                canvas.create_text(
                    x + 8,
                    y + 6,
                    text=course.name,
                    anchor="nw",
                    fill=self.COLORS["ink"],
                    font=self.name_font,
                    width=col_width - 42,
                )
                if warning:
                    self._draw_warning(canvas, x, y, col_width)
                else:
                    canvas.create_text(
                        x + col_width - 7,
                        y + 7,
                        text=f"♥{course.like}",
                        anchor="ne",
                        fill=self.COLORS["muted"],
                        font=(self.font_family, 8),
                    )
                canvas.create_text(
                    x + 8,
                    y + 12 + name_heights[course_index],
                    text=details[course_index],
                    anchor="nw",
                    fill="#475569",
                    font=self.detail_font,
                    width=col_width - 16,
                )

        if total_height <= height + 1:
            canvas.yview_moveto(0)

    def _compute_warnings(
        self,
        schedule: list[list[Optional[int]]],
        courses: list[Course],
        periods: list[Period],
        config: dict,
    ) -> set[tuple[int, int]]:
        """Return cells whose transition is too long for the available gap."""
        if self.result is None:
            return set()
        locations = self.result.locations
        travel = self.result.travel
        loc_index = {name: i for i, name in enumerate(locations)}
        meeting_on = bool(config.get("morning_meeting", False))
        meeting_loc = str(config.get("morning_meeting_location", ""))
        meeting_gap = int(config.get("morning_meeting_gap", 10))
        meal_on = bool(config.get("order_meal", False))
        meal_loc = str(config.get("order_meal_location", ""))
        meal_after = int(config.get("order_meal_after_period", 1))
        locker_loc = str(config.get("locker_location", ""))
        warnings: set[tuple[int, int]] = set()

        for d, row in enumerate(schedule):
            first_p = next((p for p, ci in enumerate(row) if ci is not None), None)
            if first_p is None:
                continue

            first_course = courses[row[first_p]]
            first_used = first_course.location
            if meeting_on and first_course.location2 and first_course.location2 in loc_index:
                d1 = travel[loc_index[meeting_loc]][loc_index[first_course.location]]
                d2 = travel[loc_index[meeting_loc]][loc_index[first_course.location2]]
                first_used = first_course.location2 if d2 < d1 else first_course.location
            first_base = meeting_loc if meeting_on and meeting_loc in loc_index else (locker_loc if first_course.locker and locker_loc in loc_index else first_used)
            first_waypoints: list[str] = []
            if meeting_on and meeting_loc in loc_index:
                first_waypoints = [locker_loc] if (first_course.locker and locker_loc in loc_index) else []
            elif first_course.locker and locker_loc in loc_index:
                first_waypoints = []
            first_walk = _walk_via(travel, loc_index, first_base, first_waypoints, first_used)
            if first_course.location2:
                first_used = min((first_course.location, first_course.location2),
                                 key=lambda loc: _walk_via(travel, loc_index, first_base, first_waypoints, loc))
                first_walk = _walk_via(travel, loc_index, first_base, first_waypoints, first_used)
            first_buffer = meeting_gap + periods[first_p].start - periods[0].start
            if meeting_on and first_walk > first_buffer:
                warnings.add((d, first_p))

            previous = (first_p, row[first_p], first_used)
            for p in range(first_p + 1, len(row)):
                ci = row[p]
                if ci is None:
                    continue
                course = courses[ci]
                prev_p, _prev_ci, prev_used = previous
                continuation = ci == _prev_ci and course.linked and p == prev_p + 1
                used = _effective_location(course, prev_used, loc_index, travel)
                waypoints: list[str] = []
                if meal_on and prev_p == meal_after - 1 and p == meal_after and meal_loc in loc_index:
                    waypoints.append(meal_loc)
                if course.locker and not continuation and locker_loc in loc_index:
                    waypoints.append(locker_loc)
                used = prev_used if continuation else _effective_location(
                    course, waypoints[-1] if waypoints else prev_used, loc_index, travel)
                walk = _walk_via(travel, loc_index, prev_used, waypoints, used)
                gap = periods[p].start - periods[prev_p].end
                if walk > gap:
                    warnings.add((d, p))
                previous = (p, ci, used)

        return warnings

    @staticmethod
    def _fit_text(text: str, font: tkfont.Font, max_width: int) -> str:
        """Trim text to a single line that fits max_width pixels."""
        if max_width <= 0:
            return ""
        if font.measure(text) <= max_width:
            return text
        ellipsis = "…"
        while text and font.measure(text + ellipsis) > max_width:
            text = text[:-1]
        return text + ellipsis if text else ellipsis

    def _draw_warning(self, canvas, x, y, col_width) -> None:
        """Draw an orange warning badge in the card's top-right corner."""
        radius = 7
        cx = x + col_width - 14
        cy = y + 14
        canvas.create_oval(
            cx - radius,
            cy - radius,
            cx + radius,
            cy + radius,
            fill="#f59e0b",
            outline="",
        )
        canvas.create_text(
            cx,
            cy,
            text="!",
            fill="white",
            font=(self.font_family, 8, "bold"),
        )

    @staticmethod
    def _travel_lookup(
        from_location: str,
        to_location: str,
        locations: list[str],
        travel: list[list[int]],
    ) -> int:
        try:
            return travel[locations.index(from_location)][locations.index(to_location)]
        except (ValueError, IndexError):
            return 0

    def _on_mousewheel(self, event) -> None:
        try:
            widget = event.widget
            direction = -1 if event.delta > 0 else 1
            while widget is not None:
                if isinstance(widget, tk.Canvas):
                    widget.yview_scroll(direction, "units")
                    return
                widget = getattr(widget, "master", None)
        except Exception:
            pass

    # ------------------------------------------------------------------
    # Save, load, export
    # ------------------------------------------------------------------

    def load_demo(self) -> None:
        if not messagebox.askyesno(
            "重置模板",
            "这会清空课程并恢复默认地点与时间设置，确定继续吗？",
            parent=self.root,
        ):
            return
        self.locations = list(DEFAULT_LOCATIONS)
        self.travel = [row[:] for row in _DEFAULT_DISTANCES]
        self.courses = []
        self.config = dict(DEFAULT_CONFIG)
        self.result = None
        self._refresh_all()
        self.headline_var.set("已重置为空白模板")
        self.subline_var.set("可按自己的课表录入课程后生成。")
        self._reset_metric_cards()
        self._redraw_timetable()
        self.status_var.set("已恢复默认地点与时间设置，请录入课程。")
        self._autosave()

    def _data_payload(self) -> dict:
        config = self._read_config()
        return {
            "version": 2,
            "locations": self.locations,
            "travel": self.travel,
            "courses": [asdict(course) for course in self.courses],
            "config": config,
        }

    def save_json(self) -> None:
        try:
            payload = self._data_payload()
        except ValueError as exc:
            messagebox.showwarning("无法保存", str(exc), parent=self.root)
            return
        try:
            path = filedialog.asksaveasfilename(
                parent=self.root,
                title="保存课表数据",
                defaultextension=".json",
                initialfile="schedule_data.json",
                filetypes=[("JSON", "*.json")],
            )
        except tk.TclError as exc:
            messagebox.showerror("保存失败", str(exc), parent=self.root)
            return
        if not path:
            return
        try:
            write_json(path, payload)
        except OSError as exc:
            messagebox.showerror("保存失败", str(exc), parent=self.root)
            return
        self.status_var.set(f"数据已保存：{path}")

    def load_json(self) -> None:
        try:
            path = filedialog.askopenfilename(
                parent=self.root,
                title="读取课表数据",
                filetypes=[("JSON", "*.json")],
            )
        except tk.TclError as exc:
            messagebox.showerror("读取失败", str(exc), parent=self.root)
            return
        if not path:
            return
        self._load_json_path(path)

    def _load_json_path(self, path: str, auto: bool = False) -> None:
        try:
            data = json.loads(Path(path).read_text(encoding="utf-8"))
            def migrate_location(name: str) -> str:
                value = str(name)
                if value == "中兴楼底下一楼":
                    return "中兴楼地下一层"
                if value == "逸夫楼一楼":
                    return "逸夫楼三楼"
                return value

            locations = [migrate_location(str(item)) for item in data["locations"]]
            travel = [[int(value) for value in row] for row in data["travel"]]
            courses = []
            for item in data.get("courses", []):
                course = course_from_data(item, int(data.get("config", {}).get("period_minutes", 45)))
                course.location = migrate_location(course.location)
                course.location2 = migrate_location(course.location2)
                courses.append(course)
            raw_config = data.get("config", {})
            config = {**DEFAULT_CONFIG, **raw_config}
            config["periods_per_day"] = int(config["periods_per_day"])
            config["period_minutes"] = int(config["period_minutes"])
            config["break_minutes"] = int(config["break_minutes"])
            config["lunch_after"] = int(config["lunch_after"])
            config["lunch_minutes"] = int(config["lunch_minutes"])
            config["pref_weight"] = float(config["pref_weight"])
            for key in ("morning_meeting_location", "order_meal_location", "locker_location"):
                if key in config and config[key] not in locations:
                    config[key] = migrate_location(str(config[key]))
            if "morning_meeting_gap" not in raw_config:
                config["morning_meeting_gap"] = int(
                    raw_config.get("morning_meeting_minutes", 10)
                )
            for key in ("morning_meeting_location", "order_meal_location", "locker_location"):
                if config.get(key) not in locations:
                    config[key] = locations[0] if locations else ""
            validate_config(config)
            validate_problem(courses, locations, travel, allow_empty=True)
        except Exception as exc:
            if auto:
                return
            messagebox.showerror("读取失败", f"文件格式不正确：{exc}", parent=self.root)
            return

        self.locations = locations
        self.travel = travel
        self.courses = courses
        self.config = config
        self.result = None
        self._refresh_all()
        self.headline_var.set("数据已读取")
        self.subline_var.set("点击「生成智能课表」查看优化效果。")
        self._reset_metric_cards()
        self._redraw_timetable()
        self.status_var.set(f"已读取：{path}")
        if self.courses:
            self.root.after(150, self.generate)

    def _autosave(self) -> None:
        try:
            payload = self._data_payload()
            write_json(self.autosave_path, payload)
        except Exception as exc:
            self.status_var.set(f"自动保存失败：{exc}")

    def _try_load_autosave(self) -> None:
        try:
            if hasattr(self, "autosave_path") and self.autosave_path.exists():
                self._load_json_path(str(self.autosave_path), auto=True)
                if self.result is not None:
                    self.status_var.set("已从本地自动保存恢复数据")
        except Exception:
            pass

    def export_csv(self) -> None:
        if self.result is None:
            messagebox.showinfo("导出 CSV", "请先生成课表。", parent=self.root)
            return
        path = filedialog.asksaveasfilename(
            parent=self.root,
            title="导出课表 CSV",
            defaultextension=".csv",
            initialfile="smart_timetable.csv",
            filetypes=[("CSV 文件", "*.csv"), ("所有文件", "*.*")],
        )
        if not path:
            return
        result = self.result
        courses = self.display_courses
        try:
            with open(path, "w", encoding="utf-8-sig", newline="") as handle:
                writer = csv.writer(handle)
                writer.writerow(["节次", "时间"] + DAYS)
                for p, period in enumerate(result.periods):
                    row = [
                        f"第 {p + 1} 节",
                        f"{minutes_to_hhmm(period.start)}–{minutes_to_hhmm(period.end)}",
                    ]
                    for d in range(len(DAYS)):
                        if (d, p) in UNAVAILABLE_SLOTS:
                            row.append("不上课")
                            continue
                        ci = result.best[d][p]
                        if ci is None:
                            row.append("")
                        else:
                            course = courses[ci]
                            loc = course.location
                            if course.location2:
                                loc += f" / {course.location2}"
                            row.append(f"{course.name} @ {loc}")
                    writer.writerow(row)

                writer.writerow([])
                writer.writerow(["指标", "优化前", "优化后"])
                before = result.baseline_metrics
                after = result.best_metrics
                writer.writerow(["综合评分", f"{before.cost:.1f}", f"{after.cost:.1f}"])
                writer.writerow(["总移动时间（分钟）", before.travel, after.travel])
                writer.writerow(["其中：晨会移动（分钟）", before.morning_travel, after.morning_travel])
                writer.writerow(["其中：订餐绕行（分钟）", before.meal_travel, after.meal_travel])
                writer.writerow(["换教室次数", before.changes, after.changes])
                writer.writerow(["路程冲突（分钟）", before.conflict_minutes, after.conflict_minutes])
                writer.writerow(["课前准备不足（分钟）", before.prep_short, after.prep_short])
                writer.writerow(["喜好单调相邻（次）", before.pref_clashes, after.pref_clashes])
                writer.writerow([])
                writer.writerow(["说明", "优化前 = 首个完整可行课表；优化后 = 模拟退火结果"])
        except OSError as exc:
            messagebox.showerror("导出失败", str(exc), parent=self.root)
            return
        self.status_var.set(f"CSV 已导出：{path}")


# ---------------------------------------------------------------------------
# Self-test (no GUI): python3 smart_scheduler.py --selftest
# ---------------------------------------------------------------------------

def run_selftest() -> int:
    print("课间穿梭 · 自测")
    print("=" * 62)

    # Cost-model unit check
    tiny_periods = [Period(510, 570, 10), Period(580, 620, 10)]
    tiny_courses = [
        Course("A", "A", 1, 0, 2),
        Course("B", "B", 1, 10, 2),
    ]
    tiny_schedule: list[list[Optional[int]]] = [[0, 1]] + [
        [None, None] for _ in range(len(DAYS) - 1)
    ]
    tiny = evaluate(
        tiny_schedule,
        tiny_courses,
        ["A", "B"],
        [[0, 8], [8, 0]],
        tiny_periods,
        pref_weight=2.5,
    )
    assert tiny.travel == 8
    assert tiny.conflict_minutes == 0
    assert tiny.prep_short == 8
    assert tiny.pref_clashes == 1
    print("✓ 成本模型单元检查通过（路程/冲突/准备/喜好）")

    # Locker pickup check.
    locker_periods = [Period(510, 570, 10), Period(580, 620, 10)]
    locker_courses = [Course("A", "A", 1, 0, 3, "", 1), Course("B", "B", 1, 2, 3, "", 1, True)]
    locker_schedule: list[list[Optional[int]]] = [[0, 1]] + [
        [None, None] for _ in range(len(DAYS) - 1)
    ]
    locker_metrics = evaluate(
        locker_schedule,
        locker_courses,
        ["A", "L", "B"],
        [[0, 2, 1], [2, 0, 3], [1, 3, 0]],
        locker_periods,
        pref_weight=2.5,
        config={**DEFAULT_CONFIG, "locker_location": "L"},
    )
    assert locker_metrics.travel == 5, locker_metrics.travel
    print("✓ 储物柜拿书绕行检查通过（路程/冲突/准备/喜好）")

    courses = [
        Course("数学", "中兴楼二楼", 225, 5, 2, "", 1),
        Course("英语", "逸夫楼三楼", 180, 10, 3, "", 1),
        Course("物理", "中兴楼三楼", 135, 10, 2, "", 1),
        Course("化学", "中兴楼二楼", 90, 15, 4, "中兴楼四楼", 2),
        Course("体育", "操场", 90, 10, 5, "", 1),
        Course("自习", "中兴楼二楼", 180, 0, 3, "", 1),
    ]
    locations = list(DEFAULT_LOCATIONS)
    travel = [row[:] for row in _DEFAULT_DISTANCES]
    config = dict(DEFAULT_CONFIG)

    validate_config(config)
    validate_problem(courses, locations, travel)
    result = solve(
        courses,
        locations,
        travel,
        config,
        seed=2026,
        restarts=5,
        iterations=12000,
    )
    before = result.baseline_metrics
    after = result.best_metrics

    print(f"课程数           : {len(courses)}")
    print(f"每周课时         : {sum(c.lesson_minutes for c in courses)} 分钟")
    print(f"优化用时         : {result.elapsed:.2f} s")
    print(f"优化前综合评分   : {before.cost:.1f}")
    print(f"优化后综合评分   : {after.cost:.1f}")
    print(f"移动时间         : {before.travel} -> {after.travel} 分钟")
    print(f"换教室次数       : {before.changes} -> {after.changes}")
    print(f"路程冲突         : {before.conflict_minutes} -> {after.conflict_minutes} 分钟")
    print(f"课前准备不足     : {before.prep_short} -> {after.prep_short} 分钟")
    print(f"喜好单调相邻     : {before.pref_clashes} -> {after.pref_clashes} 次")
    print("-" * 62)

    # Constraint checks.
    assert after.cost <= before.cost, "优化结果不应比基线更差"
    placed = 0
    for day in range(len(DAYS)):
        for p in range(config["periods_per_day"]):
            ci = result.best[day][p]
            if ci is None:
                continue
            placed += 1
            assert courses[ci].location in locations
            if courses[ci].location2:
                assert courses[ci].location2 in locations
        day_courses = [ci for ci in result.best[day] if ci is not None]
        for ci in set(day_courses):
            assert day_courses.count(ci) <= courses[ci].per_day_max, (
                f"{courses[ci].name} 同一天超过每天最多节数"
            )

    # Every course's scheduled minutes must match lesson_minutes.
    for ci, course in enumerate(courses):
        scheduled_minutes = _course_scheduled_minutes(result.best, result.periods, ci)
        assert scheduled_minutes == course.lesson_minutes, (
            f"{course.name} 课时不匹配：排课 {scheduled_minutes} 分钟 vs 要求 {course.lesson_minutes} 分钟"
        )

    print("✓ 所有课时均已排入")
    print("✓ 同一门课每天不超过设定上限")
    print("✓ 每门课的每周课时与要求一致")
    print("✓ 优化后综合评分不高于基线")
    print("=" * 62)
    print("SELFTEST PASSED")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="课间穿梭 · 智能课表分配器")
    parser.add_argument("--selftest", action="store_true", help="运行无界面的自测")
    args, _unknown = parser.parse_known_args()
    if args.selftest:
        return run_selftest()

    root = tk.Tk()
    app = SchedulerApp(root)
    # Keep a reference for debugging in interactive sessions.
    root._app = app  # type: ignore[attr-defined]
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
