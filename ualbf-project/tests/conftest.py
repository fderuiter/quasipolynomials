import os

# Resolve the absolute repository root path at the start of pytest.
# conftest.py is located at <repo>/ualbf-project/tests/conftest.py.
if "REPO_ROOT_DIR" not in os.environ:
    if "GITHUB_WORKSPACE" in os.environ:
        os.environ["REPO_ROOT_DIR"] = os.environ["GITHUB_WORKSPACE"]
    else:
        abs_file = os.path.abspath(__file__)
        dir_name = os.path.dirname(abs_file)
        repo_root = os.path.abspath(os.path.join(dir_name, "../.."))
        os.environ["REPO_ROOT_DIR"] = repo_root
