import os
import re


def _find_repo_root() -> str:
    # 1. Check if conftest.py resolved it
    if "REPO_ROOT_DIR" in os.environ:
        return os.environ["REPO_ROOT_DIR"]

    # 2. Check if GITHUB_WORKSPACE environment variable is set
    if "GITHUB_WORKSPACE" in os.environ:
        return os.environ["GITHUB_WORKSPACE"]

    # 3. Dynamic climbing fallback
    start_dir = os.path.dirname(os.path.abspath(__file__))
    current = start_dir
    while current != os.path.dirname(current):
        sentinels = ["docs_manifest.json", "pyproject.toml", ".git"]
        if any(os.path.exists(os.path.join(current, s)) for s in sentinels):
            return current
        current = os.path.dirname(current)
    return os.path.abspath(os.path.join(start_dir, "../.."))


_REPO_ROOT = _find_repo_root()


def test_github_actions_ci_has_pythonunbuffered():
    ci_path = os.path.join(_REPO_ROOT, ".github/workflows/ci.yml")

    msg = f"ci.yml not found at {ci_path}"
    assert os.path.exists(ci_path), msg

    with open(ci_path, "r") as f:
        content = f.read()

    match = re.search(r"PYTHONUNBUFFERED\s*:\s*['\"]?1['\"]?", content)
    msg = "PYTHONUNBUFFERED: '1' not found in ci.yml env block"
    assert match is not None, msg


def test_github_actions_auto_merge_has_pythonunbuffered():
    filename = ".github/workflows/auto-merge.yml"
    auto_merge_path = os.path.join(_REPO_ROOT, filename)

    msg = f"auto-merge.yml not found at {auto_merge_path}"
    assert os.path.exists(auto_merge_path), msg

    with open(auto_merge_path, "r") as f:
        content = f.read()

    match = re.search(r"PYTHONUNBUFFERED\s*:\s*['\"]?1['\"]?", content)
    msg = "PYTHONUNBUFFERED: '1' not found in auto-merge.yml env block"
    assert match is not None, msg


def test_makefile_has_pythonunbuffered():
    makefile_path = os.path.join(_REPO_ROOT, "ualbf-project/Makefile")

    msg = f"Makefile not found at {makefile_path}"
    assert os.path.exists(makefile_path), msg

    with open(makefile_path, "r") as f:
        content = f.read()

    match = re.search(r"export\s+PYTHONUNBUFFERED\s*=\s*1", content)
    msg = "export PYTHONUNBUFFERED=1 not found in Makefile"
    assert match is not None, msg
