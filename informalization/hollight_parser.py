# hollight_parser.py

import re
from dataclasses import dataclass, field
from typing import List, Optional

@dataclass
class HOLStatement:
    """Stores a simplified HOL Light statement."""
    name: str
    formal_content: str  # Includes everything starting with 'let' and ending with ';;'
    pre_comment: Optional[str] = None

@dataclass
class HOLFile:
    """Stores overall file information from a HOL Light file."""
    overview: str = ""
    imports: List[str] = field(default_factory=list)
    statements: List[HOLStatement] = field(default_factory=list)

    def __len__(self) -> int:
        """Returns the number of statements in the file."""
        return len(self.statements)


def extract_overview(content: str) -> str:
    """
    Extracts an overview comment from the file, assuming the overview is given
    in a header comment block that contains a sequence of '=' characters.
    
    For example:
      (* ========================================================================= *)
      (* Representation of primes == 1 (mod 4) as sum of 2 squares.                *)
      (* ========================================================================= *)
    """
    lines = content.splitlines()
    overview_lines = []
    in_comment = False
    current_comment = []
    
    for line in lines:
        stripped = line.strip()
        # Check if the line starts a block comment
        if stripped.startswith("(*"):
            in_comment = True
            current_comment.append(stripped)
            # If the comment ends on the same line, we finish this block:
            if "*)" in stripped:
                overview_lines.append(" ".join(current_comment))
                current_comment = []
                in_comment = False
        elif in_comment:
            current_comment.append(stripped)
            # When the end of a comment is found, finish this block.
            if "*)" in stripped:
                overview_lines.append(" ".join(current_comment))
                current_comment = []
                in_comment = False
        else:
            # Stop when a non-blank, non-comment line is encountered.
            if stripped != "":
                break

    return "\n".join(overview_lines)

def extract_imports(content: str) -> List[str]:
    """
    Extract all import statements (lines beginning with 'needs "..." ;;').

    Output:
        A list of strings, each representing an import statement.
    """
    import_pattern = r'needs\s+"([^"]+)"\s*;;'
    imports = re.findall(import_pattern, content, flags=re.MULTILINE)
    return imports

def parse_statements(content: str) -> List[HOLStatement]:
    """
    Parses the file content to extract every formal statement block.
    
    The strategy is as follows:
      - Locate blocks of text that start with an optional preceding comment
        and then a "let ... ;;" segment. The formal content will include everything,
        including the leading "let" keyword.
      - Then, extract the statement name from the formal block by finding the token
        immediately after "let".
    
    Returns:
      A list of HOLStatement objects.
    """
    # Regex explanation:
    # (?:\(\*([\s\S]*?)\*\)\s*)?  --> Optionally capture a preceding comment block in group(1).
    # (let\s+[\s\S]*?;;)           --> Capture the entire statement block in group(2) (non-greedy up to ";;").
    pattern = re.compile(
        r"(?:\(\*([\s\S]*?)\*\)\s*)?"  # optional pre-comment; group(1)
        r"(let\s+[\s\S]*?;;)",         # full formal content block; group(2)
        re.MULTILINE
    )

    statements = []
    for match in pattern.finditer(content):
        pre_comment, formal_block = match.groups()
        # Extract the statement name by searching for "let" followed by the name.
        name_match = re.search(r"let\s+(\S+)", formal_block)
        if name_match:
            name = name_match.group(1)
        else:
            name = "UNKNOWN"

        stmt = HOLStatement(
            name=name.strip(),
            formal_content=formal_block.strip(),
            pre_comment=pre_comment.strip() if pre_comment else None
        )
        statements.append(stmt)
    return statements

def parse_hol_file(file_path: str) -> HOLFile:
    """
    Parses a HOL Light .ml file and extracts:
      - An overview comment (if present)
      - Import statements (lines starting with 'needs "..." ;;')
      - Every formal statement block (including the entire text from "let" to ";;")
        along with any preceding comment.
    
    Returns:
      A HOLFile instance containing the collected data.
    """
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    # print(content)
    overview = extract_overview(content)
    imports = extract_imports(content)
    statements = parse_statements(content)
    
    return HOLFile(overview=overview, imports=imports, statements=statements)

# For testing purposes, run this file directly.
if __name__ == "__main__":
    sample_file = "/home/yuzhi/workspace/repo/100/sqrt.ml"  # Replace with your HOL Light file path.
    hol_file = parse_hol_file(sample_file)
    
    print("=== Overview ===")
    print(hol_file.overview)
    print("\n=== Imports ===")
    for imp in hol_file.imports:
        print(imp)
    print("\n=== Statements ===")
    for stmt in hol_file.statements:
        print("====================================")
        print(f"Name: {stmt.name}")
        if stmt.pre_comment:
            print("Pre-Comment:")
            print(stmt.pre_comment)
        print("Formal Content:")
        print(stmt.formal_content)
        print("\n")

