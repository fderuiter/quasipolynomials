import pytest
import hashlib
from auditor import compute_verus_hashes, scan_characters, count_active_braces, is_keyword_active


def test_scanner_with_comments_and_strings():
    content = """
    // This is a line comment with { } braces
    /* This is a block comment with { } braces
       /* nested block comment with { } braces */
    */
    pub fn dummy_func() -> bool {
        let s = "brace { inside string }";
        let c = '{';
        true
    }
    """
    hashes = compute_verus_hashes(content)
    assert "dummy_func" in hashes

    # Let's verify that the body was correctly extracted
    # The body should start from the line "pub fn dummy_func() -> bool {"
    # and end at the closing brace line.
    expected_body = (
        "    pub fn dummy_func() -> bool {\n"
        '        let s = "brace { inside string }";\n'
        "        let c = '{';\n"
        "        true\n"
        "    }"
    )
    assert hashes["dummy_func"] == hashlib.sha256(expected_body.encode("utf-8")).hexdigest()


def test_allman_style_formatting():
    content = """
    pub proof fn my_allman_func()
    {
        // some code
        let a = 1;
    }
    """
    hashes = compute_verus_hashes(content)
    assert "my_allman_func" in hashes

    expected_body = (
        "    pub proof fn my_allman_func()\n"
        "    {\n"
        "        // some code\n"
        "        let a = 1;\n"
        "    }"
    )
    assert hashes["my_allman_func"] == hashlib.sha256(expected_body.encode("utf-8")).hexdigest()


def test_allman_style_module():
    content = """
    pub mod my_allman_mod
    {
        pub fn inside_mod() {
            let x = 2;
        }
    }
    """
    hashes = compute_verus_hashes(content)
    assert "my_allman_mod::inside_mod" in hashes


def test_commented_out_functions():
    content = """
    // pub fn commented_func() {
    //     let x = 1;
    // }
    /*
    pub fn blocked_func() {
        let y = 2;
    }
    */
    pub fn real_func() {
    }
    """
    hashes = compute_verus_hashes(content)
    assert "commented_func" not in hashes
    assert "blocked_func" not in hashes
    assert "real_func" in hashes


def test_escaped_quotes_in_string():
    # String contains escaped double quotes and braces inside
    content = """
    pub fn escaped_func() {
        let s = "escaped \\\" brace { inside }";
    }
    """
    hashes = compute_verus_hashes(content)
    assert "escaped_func" in hashes
