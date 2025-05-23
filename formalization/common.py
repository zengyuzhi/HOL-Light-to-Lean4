import re
import sys
import os
from loguru import logger
from typing import Union

def extract_from_md(file_path):
    """
    Extracts markdown content into a dictionary.

    Format:
    {
        "overview": "...",
        "vote_INDUCT,vote_RECURSION": {
            "Type of the formal statement": "...",
            "Formal Content": "...",
            ...
        },
        ...
    }
    """
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Split sections by '##', keep sessions[1:] (session[0] is preamble)
    sessions = re.split(r'^##\s+', content, flags=re.MULTILINE)

    result = {}

    for session in sessions[1:]:
        lines = session.strip().splitlines()
        if not lines:
            continue

        section_title = lines[0].strip()
        body = "\n".join(lines[1:]).strip()

        # Handle the Overview section
        if section_title.lower() == "overview":
            result["overview"] = body
            continue

        # Use the title as the key
        key = section_title
        section_dict = {}

        # Parse ### fields
        parts = re.split(r'^###\s+', session, flags=re.MULTILINE)
        for part in parts[1:]:
            sublines = part.strip().splitlines()
            if not sublines:
                continue
            field_name = sublines[0].strip()
            field_content = "\n".join(sublines[1:]).strip()
            section_dict[field_name] = field_content

        result[key] = section_dict

    return result


def set_logger(verbose: bool) -> None:
    """
    Set the logging level of loguru.
    The effect of this function is global, and it should
    be called only once in the main function
    """
    logger.remove()
    logger.add(sys.stderr, level="DEBUG" if verbose else "INFO")


def filter_response_messages(response, line_count):
    """
    Filter the response messages to only include those that are errors.
    Args:
        response (dict): The response from the Lean4 server.
        line_count (int): The number of lines in the previous code.
    Returns:
        
    """
    # if the key 'messages' is not in the response, return empty lists
    messages = response['messages'] if 'messages' not in response else []
    errors, warns = [], []
    for m in messages:
        if m['severity'] == 'error':
            pos = m.get('pos')
            if pos and pos['line'] > line_count:
                        # if you want to re-base the line numbers so code-only starts at 1:
                m['pos']['line']   -= line_count
                m.pop('endPos', None)
                errors.append(m)
        if m['severity'] == 'warning':
            pos = m.get('pos')
            if pos and pos['line'] > line_count:
                # if you want to re-base the line numbers so code-only starts at 1:
                m['pos']['line']   -= line_count
                m.pop('endPos', None)
                warns.append(m)
    return errors, warns

def setup_results_directory(base_path: str):
    """
    Create result directory and clear previous error files.
    """
    logger.info(f"Setting up results directory at {base_path}")
    os.makedirs(base_path, exist_ok=True)
    for fname in ("sketch_with_errors.txt", "formalization_with_errors.txt"):  # clear error logs
        fpath = os.path.join(base_path, fname)
        if os.path.exists(fpath):
            open(fpath, 'w').close()
            logger.debug(f"Cleared existing file: {fpath}")

def save_file(path: str, content: Union[str, list], append: bool = False):
    """
    Save content to a file. If append is True, append to the file.
    """
    logger.debug(f"Saving file '{path}' (append={append}), content length={len(content)}")
    mode = 'a' if append else 'w'
    if "txt" in path:
        with open(path, mode, encoding='utf-8') as f:
            f.write(content)
    elif "jsonl" in path:
        with open(path, mode, encoding='utf-8') as f:
            for item in content:
                f.write(f"{item}\n")
    logger.info(f"File saved: {path}")

def load_documentation(docs_md_path: str):
    """
    Load the documentation from the given markdown file.
    """
    logger.info(f"Loading documentation from {docs_md_path}")
    with open(docs_md_path, 'r', encoding='utf-8') as f:
        docs_md = f.read()
    docs_list = extract_from_md(docs_md_path)
    docs_list.pop("overview", None)
    logger.debug(f"Extracted {len(docs_list)} sections from documentation")
    return docs_md, docs_list

def load_txt_file(file_path: str):
    """
    Load a text file and return its content.
    """
    logger.info(f"Loading text file from {file_path}")
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    logger.debug(f"Loaded content length: {len(content)}")
    return content











# path='./docs/tiny/claude-3.7-sonnet/sqrt.md'
# output=extract_from_md(path)
# for key, item in output.items():
#     print(item)
# print(len(output))
# pprint(output)