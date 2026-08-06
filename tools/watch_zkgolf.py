#!/usr/bin/env python3
"""zk.golf change detector.

Fetches the public challenge list and diffs it against the last-seen
snapshot (.zkgolf-watch-state.json, gitignored). Prints a human-readable
report of anything that changed and exits:

  0  -> no changes
  10 -> changes detected (new challenge / record moved / baseline changed)
  1  -> error (API unreachable etc.)

A NEW CHALLENGE is the jackpot signal: challenges launch with record = par,
so the first sub-par verified submission takes the crown.
"""
import json
import sys
import urllib.request
from pathlib import Path

API = "https://zk.golf/api/agent/v1/challenges"
STATE = Path(__file__).resolve().parent.parent / ".zkgolf-watch-state.json"


def fetch():
    req = urllib.request.Request(API, headers={"User-Agent": "clawd-zk-golf-watch"})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)


def main():
    try:
        challenges = fetch()
    except Exception as e:
        print(f"ERROR: fetch failed: {e}")
        return 1

    now = {
        c["slug"]: {
            "title": c["title"],
            "baseline": c["baseline_score"],
            "best": c["best_score"],
        }
        for c in challenges
    }

    if not STATE.exists():
        STATE.write_text(json.dumps(now, indent=2))
        print(f"Initialized snapshot with {len(now)} challenges.")
        return 0

    prev = json.loads(STATE.read_text())
    changes = []

    for slug, cur in now.items():
        if slug not in prev:
            fresh = " (record = par: WIDE OPEN, submit fast!)" if cur["best"] == cur["baseline"] else ""
            changes.append(
                f"NEW CHALLENGE: {slug} \"{cur['title']}\" par={cur['baseline']} best={cur['best']}{fresh}")
            continue
        old = prev[slug]
        if cur["best"] != old["best"]:
            changes.append(
                f"RECORD MOVED: {slug} {old['best']} -> {cur['best']} (par {cur['baseline']})")
        if cur["baseline"] != old["baseline"]:
            changes.append(
                f"BASELINE CHANGED: {slug} {old['baseline']} -> {cur['baseline']}")
    for slug in prev:
        if slug not in now:
            changes.append(f"CHALLENGE REMOVED: {slug}")

    STATE.write_text(json.dumps(now, indent=2))

    if not changes:
        print(f"No changes across {len(now)} challenges.")
        return 0
    print(f"{len(changes)} change(s) on zk.golf:")
    for c in changes:
        print(f"  - {c}")
    return 10


if __name__ == "__main__":
    sys.exit(main())
