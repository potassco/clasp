#!/usr/bin/env python3
"""
Transform C++ function signatures to use trailing return types.
Only transforms if the return type has more than 4 characters.
Only processes libclasp files (clasp/ headers and src/ sources).

Usage:
    python3 tools/transform_trailing_return.py [--quiet] [<root-dir>]

Arguments:
    --quiet     Suppress per-line output; only print summary.
    <root-dir>  Root directory of the clasp repository (default: current directory).
"""

import re
import os
import sys


def get_libclasp_files(base):
    """Get all libclasp header and source files."""
    files = []
    # Header files in clasp/ directory (including subdirectories)
    for root, dirs, flist in os.walk(os.path.join(base, 'clasp')):
        for f in flist:
            if f.endswith(('.h', '.hpp', '.cpp', '.inl')):
                files.append(os.path.join(root, f))
    # Source files in src/
    src_dir = os.path.join(base, 'src')
    if os.path.isdir(src_dir):
        for f in sorted(os.listdir(src_dir)):
            if f.endswith(('.cpp', '.h')):
                files.append(os.path.join(src_dir, f))
    return sorted(files)


def strip_line_comment(s):
    """Strip C++ // comment from line, respecting strings."""
    in_str = False
    in_char = False
    i = 0
    while i < len(s):
        c = s[i]
        if in_str:
            if c == '\\':
                i += 2
                continue
            elif c == '"':
                in_str = False
        elif in_char:
            if c == '\\':
                i += 2
                continue
            elif c == "'":
                in_char = False
        else:
            if c == '"':
                in_str = True
            elif c == "'":
                in_char = True
            elif c == '/' and i + 1 < len(s) and s[i+1] == '/':
                return s[:i]
        i += 1
    return s


def find_matching_paren(s, start):
    """Find the index of the matching closing paren for the '(' at start."""
    assert s[start] == '('
    depth = 0
    i = start
    while i < len(s):
        c = s[i]
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0:
                return i
        elif c == '<':
            # Try to skip template arguments
            j = i + 1
            depth_t = 1
            while j < len(s) and depth_t > 0:
                if s[j] == '<':
                    depth_t += 1
                elif s[j] == '>':
                    depth_t -= 1
                j += 1
            if depth_t == 0:
                i = j - 1
        elif c == '"':
            j = i + 1
            while j < len(s) and s[j] != '"':
                if s[j] == '\\':
                    j += 1
                j += 1
            i = j
        i += 1
    return -1


def parse_prefix(s):
    """
    Parse prefix qualifiers and attributes from front of string.
    Returns (prefix, remaining).
    prefix contains: keywords like virtual/static/etc and [[...]] attributes.
    """
    prefix = ''
    while True:
        # Check for [[...]] attribute
        m = re.match(r'^\[\[[^\]]*\]\]\s*', s)
        if m:
            prefix += m.group()
            s = s[m.end():]
            continue
        # Check for keyword qualifier
        m = re.match(r'^(virtual|static|inline|explicit|constexpr|friend|extern|__forceinline)\s+', s)
        if m:
            prefix += m.group()
            s = s[m.end():]
            continue
        break
    return prefix, s


def is_valid_return_type(s):
    """Check if the string looks like a valid C++ return type."""
    s = s.strip()
    if not s:
        return False
    # Must not contain expression operators or string/char literals
    forbidden = set('=?!+-/%|^;.@$"\'`')
    for c in s:
        if c in forbidden:
            return False
    # Must not contain comma at top level (would indicate macro arguments)
    if ',' in s and '<' not in s:
        return False
    # Must not start with reserved non-type words
    first_word = s.split()[0] if s.split() else ''
    if first_word in ('return', 'if', 'while', 'for', 'switch', 'case',
                      'break', 'continue', 'goto', 'throw', 'delete', 'new',
                      'assert', 'static_assert'):
        return False
    return True


_VALID_SUFFIX_RE = re.compile(
    # Move leading \s* outside the repetition group to avoid nested optional quantifiers
    r'^\s*(?:(?:const|volatile|noexcept(?:\([^)]*\))?|&&?|override|final)\s*)*'
    r'(?:=\s*(?:0|default|delete)\s*)?'
    r'[;{]'
)


def is_valid_func_suffix(s):
    """
    Check if the suffix after ')' looks like a valid function declaration suffix.
    Valid suffixes: optional qualifiers followed by ; or {
    """
    return bool(_VALID_SUFFIX_RE.match(s.strip()))


def parse_suffix(suffix_str):
    """
    Parse the suffix after the closing paren of parameter list.
    Returns (pre_arrow, post_arrow, terminal) where:
    - pre_arrow: qualifiers that go before -> (const, volatile, noexcept, &, &&)
    - post_arrow: specifiers that go after -> (override, final, = 0, = default, = delete)
    - terminal: ; or { or inline body starting with {
    """
    s = suffix_str.strip()
    pre_arrow_parts = []
    post_arrow_parts = []
    terminal = ''
    i = 0

    while i < len(s):
        while i < len(s) and s[i].isspace():
            i += 1
        if i >= len(s):
            break

        if s[i] == ';':
            terminal = s[i:]
            break
        if s[i] == '{':
            terminal = s[i:]
            break

        # = 0 / = default / = delete
        if s[i] == '=':
            m = re.match(r'=\s*(0|default|delete)\s*', s[i:])
            if m:
                post_arrow_parts.append('= ' + m.group(1))
                i += m.end()
                continue
            terminal = s[i:]
            break

        if s[i:i+2] == '&&':
            pre_arrow_parts.append('&&')
            i += 2
            continue

        if s[i] == '&':
            pre_arrow_parts.append('&')
            i += 1
            continue

        m = re.match(r'[a-zA-Z_]\w*', s[i:])
        if not m:
            terminal = s[i:]
            break

        word = m.group()
        i += m.end()

        if word == 'const':
            pre_arrow_parts.append('const')
        elif word == 'volatile':
            pre_arrow_parts.append('volatile')
        elif word == 'noexcept':
            j = i
            while j < len(s) and s[j].isspace():
                j += 1
            if j < len(s) and s[j] == '(':
                end = find_matching_paren(s, j)
                if end >= 0:
                    pre_arrow_parts.append('noexcept' + s[j:end+1])
                    i = end + 1
                    continue
            pre_arrow_parts.append('noexcept')
        elif word == 'override':
            post_arrow_parts.append('override')
        elif word == 'final':
            post_arrow_parts.append('final')
        else:
            terminal = s[i - len(word):]
            break

    return ' '.join(pre_arrow_parts), ' '.join(post_arrow_parts), terminal


def transform_line(line):
    """
    Try to transform a function declaration to trailing return type syntax.
    Returns the transformed line, or the original if no transformation was made.
    """
    # Preserve EOL
    eol = ''
    content = line
    if content.endswith('\n'):
        eol = '\n'
        content = content[:-1]
    if content.endswith('\r'):
        eol = '\r' + eol
        content = content[:-1]

    # Get indentation
    indent_len = len(content) - len(content.lstrip())
    indent_str = content[:indent_len]
    content_stripped = content.lstrip()

    # Strip trailing comment for analysis (keep original for output)
    content_no_comment = strip_line_comment(content_stripped).rstrip()

    # Skip empty or comment-only lines
    if not content_no_comment:
        return line

    # Skip lines ending with \ (macro continuations)
    if content_no_comment.endswith('\\'):
        return line

    # Skip preprocessor, comments, namespace/class/struct, etc.
    if re.match(r'^(?://|/\*|#|template\b|using\b|typedef\b|namespace\b|class\b|struct\b|enum\b|union\b)', content_no_comment):
        return line

    # Skip control flow statements and C++20 constraint keywords
    if re.match(r'^(?:else\b|if\b|while\b|for\b|do\b|try\b|catch\b|switch\b|return\b|throw\b|goto\b|requires\b|co_await\b|co_yield\b|co_return\b|default\b|case\b)', content_no_comment):
        return line

    # Skip access specifiers
    if re.match(r'^(?:public|private|protected)\s*:', content_no_comment):
        return line

    # Must contain '(' to be a function
    if '(' not in content_no_comment:
        return line

    # Parse prefix qualifiers
    prefix_str, remaining = parse_prefix(content_no_comment)

    # Find position of the first '(' in remaining
    paren_pos = remaining.find('(')
    if paren_pos < 0:
        return line

    before_paren = remaining[:paren_pos]

    # Check for conversion operator: "operator TypeName(" - has no return type
    if re.match(r'^operator\s+\S', before_paren.strip()):
        return line

    # Find the function name (last qualified identifier or operator expression)
    op_match = re.search(r'\boperator\s*(?:[+\-*/%^&|~!<>=,\[\]()]{1,3}|(?:new|delete)(?:\s*\[\])?|""\s+\w+)\s*$', before_paren)
    if op_match:
        func_name = op_match.group().rstrip()
        return_type_raw = before_paren[:op_match.start()].strip()
    else:
        # Last qualified identifier (possibly with :: and optional ~)
        qual_match = re.search(r'(?:[a-zA-Z_]\w*\s*::\s*)*~?[a-zA-Z_]\w*\s*$', before_paren)
        if not qual_match or not qual_match.group().strip():
            return line
        func_name = qual_match.group().strip()
        return_type_raw = before_paren[:qual_match.start()].strip()

    # Must have a return type (constructors/destructors have none)
    if not return_type_raw:
        return line

    # Normalize the return type
    return_type = ' '.join(return_type_raw.split())

    # Skip if already trailing return type
    if return_type == 'auto':
        return line

    # Move any function specifiers (constexpr, consteval, constinit) from return_type
    # to prefix_str. These are decl-specifiers, not type-specifiers.
    # Also move any ALL_CAPS macro that precedes a specifier (e.g. POTASSCO_ATTR_INLINE).
    specifier_re = re.compile(
        r'^((?:[A-Z][A-Z0-9_]*\s+)?(?:constexpr|consteval|constinit)\s+)'
    )
    m = specifier_re.match(return_type)
    if m:
        prefix_str += m.group(1)
        return_type = return_type[m.end():]

    # Also move standalone ALL_CAPS prefix macros (like POTASSCO_ATTR_INLINE alone)
    # only if they stand alone before the actual type
    macro_re = re.compile(r'^([A-Z][A-Z0-9_]+)\s+(?=[A-Za-z_])')
    while True:
        m2 = macro_re.match(return_type)
        if m2 and m2.group(1) not in ('NULL', 'TRUE', 'FALSE'):
            after = return_type[m2.end():]
            first_after = after.split()[0] if after.split() else ''
            if not re.match(r'^[A-Z][A-Z0-9_]+$', first_after):
                prefix_str += m2.group(1) + ' '
                return_type = return_type[m2.end():]
                continue
        break

    # Validate that return type looks like a C++ type
    if not is_valid_return_type(return_type):
        return line

    # Skip if return type ends with '::' (incomplete scope parsing)
    if return_type.endswith('::'):
        return line

    # Skip if return type ends with 'operator' (conversion operator)
    if re.search(r'\boperator\s*$', return_type):
        return line

    # Check that return type does NOT contain member access
    if '.' in return_type:
        return line
    if return_type.count('<') != return_type.count('>'):
        return line

    # Check all words in return type for statement keywords
    STMT_KEYWORDS = {'return', 'if', 'else', 'while', 'for', 'switch', 'case', 'break',
                     'continue', 'goto', 'throw', 'delete', 'new', 'default',
                     'co_await', 'co_yield', 'co_return'}
    for word in return_type.split():
        if word.rstrip(':') in STMT_KEYWORDS:
            return line

    # Check return type length (must be > 4)
    if len(return_type) <= 4:
        return line

    # Check that func_name doesn't suggest this is a method call
    before_func_in_remaining = before_paren[:before_paren.rfind(func_name.split('::')[-1].strip())].rstrip()
    if before_func_in_remaining and before_func_in_remaining[-1] in '.>':
        return line

    # Find matching ')' for the parameter list
    params_close = find_matching_paren(remaining, paren_pos)
    if params_close < 0:
        return line  # Multi-line - skip

    params = remaining[paren_pos+1:params_close]
    suffix_raw = remaining[params_close+1:]

    # Parameter checks: if params indicate this is not a function declaration
    # 1. Params containing 'this' keyword
    if re.search(r'\bthis\b', params):
        return line
    # 2. Params containing value keywords or C++ cast expressions
    if re.search(r'\b(?:nullptr|NULL|true|false|static_cast|dynamic_cast|reinterpret_cast|const_cast|std::move|std::forward)\b', params):
        return line
    # 3. Params containing member access (.identifier)
    if re.search(r'\.[a-zA-Z_]', params):
        return line
    # 4. Params containing '->'
    if '->' in params:
        return line
    # 5. Params starting with & or * (address-of or dereference expression)
    if re.match(r'^[&*][a-zA-Z_~(]', params.strip()):
        return line
    # 6. Params containing unary ~ (bitwise NOT)
    if re.search(r'~[a-zA-Z_]', params):
        return line
    # 7. Params containing arithmetic operators or standalone numeric literals
    params_no_defaults = re.sub(r'=\s*[^,)]+', '', params)
    if re.search(r'(?<![a-zA-Z_\d])[\d]+(?![a-zA-Z_])', params_no_defaults):
        return line
    if re.search(r'[^<>!][-+][^->]', params_no_defaults):
        return line
    # 8. Params containing nested function calls
    if (')' in params
            and '*' not in params
            and not re.search(r'\b(?:decltype|sizeof|alignof|noexcept)\b', params)):
        return line
    # 9. Single qualified name ending in lowercase (likely enum member, not type)
    if (re.match(r'^[A-Z]\w*::[a-z]\w*$', params.strip())
            and not prefix_str and '::' not in func_name):
        return line
    # 10. Single bare lowercase identifier (likely a variable declaration by value)
    if (not prefix_str and '::' not in func_name
            and re.match(r'^[a-zA-Z_]\w*$', params.strip())
            and params.strip()[0].islower()
            and not params.strip().endswith(('_t', '_type', '_kind', '_enum'))):
        return line

    # Append any comment from the original line
    original_comment = content_stripped[len(content_no_comment):]

    # Validate the suffix looks like a function declaration
    if not is_valid_func_suffix(suffix_raw):
        return line

    # Parse suffix
    pre_arrow, post_arrow, terminal = parse_suffix(suffix_raw)

    # Build the transformed line
    func_name_norm = re.sub(r'\s+', ' ', func_name).strip()

    new_content = f'{prefix_str}auto {func_name_norm}({params})'

    if pre_arrow:
        new_content += f' {pre_arrow}'

    new_content += f' -> {return_type}'

    if post_arrow:
        new_content += f' {post_arrow}'

    # Handle terminal (;, {inline body}, etc.)
    term = terminal.strip()
    if term:
        if term.startswith('{'):
            new_content += f' {term}'
        else:
            new_content += term

    new_content += original_comment

    return indent_str + new_content + eol


def transform_file(filepath, verbose=True):
    """Transform all eligible function declarations in a file."""
    with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
        lines = f.readlines()

    new_lines = []
    changed_count = 0
    in_block_comment = False
    for i, line in enumerate(lines):
        # Track block comment state
        stripped = line.strip()
        if in_block_comment:
            if '*/' in line:
                in_block_comment = False
            new_lines.append(line)
            continue
        if stripped.startswith('/*'):
            if '*/' not in line[line.index('/*')+2:]:
                in_block_comment = True
            new_lines.append(line)
            continue

        new_line = transform_line(line)
        if new_line != line:
            changed_count += 1
            if verbose:
                print(f"  Line {i+1}:")
                print(f"    - {line.rstrip()}")
                print(f"    + {new_line.rstrip()}")
        new_lines.append(new_line)

    if changed_count > 0:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.writelines(new_lines)

    return changed_count


def main():
    args = sys.argv[1:]
    verbose = '--quiet' not in args
    args = [a for a in args if a != '--quiet']

    base = args[0] if args else os.getcwd()
    base = os.path.abspath(base)

    if not os.path.isdir(os.path.join(base, 'clasp')):
        print(f"Error: '{base}' does not look like a clasp root directory (missing 'clasp/' subdirectory).", file=sys.stderr)
        sys.exit(1)

    files = get_libclasp_files(base)
    total_files = 0
    total_changes = 0
    for filepath in files:
        rel = filepath.replace(base + os.sep, '')
        count = transform_file(filepath, verbose=verbose)
        if count > 0:
            total_files += 1
            total_changes += count
            if verbose:
                print(f"  => {rel}: {count} changes")
    print(f"\nTotal: {total_changes} transformations in {total_files} files")


if __name__ == '__main__':
    main()
