import time


def decompose_duration(seconds):
    """
    Decompose a duration in seconds into (days, hours, minutes, seconds).
    Core shared algorithm for both UI and LaTeX rendering.
    """
    if seconds < 0:
        return 0, 0, 0, 0
    s = int(seconds)
    d = s // 86400
    rem = s % 86400
    h = rem // 3600
    rem %= 3600
    m = rem // 60
    s_out = rem % 60
    return d, h, m, s_out


def format_hhmmss(seconds):
    """
    Format a duration as [D days, ]HH:MM:SS.
    Replaces duplicate string logic for timedelta conversions.
    """
    d, h, m, s = decompose_duration(seconds)
    if d > 0:
        return f"{d} days, {h:02d}:{m:02d}:{s:02d}"
    return f"{h:02d}:{m:02d}:{s:02d}"


def get_current_timestamp(fmt="%H:%M:%S"):
    """
    Get the current time formatted with the given format string.
    """
    return time.strftime(fmt)
