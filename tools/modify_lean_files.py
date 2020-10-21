import bisect
from pathlib import Path
from typing import Dict, List, Set, Tuple

from tokenize_lean_files import LeanFile

class LeanModifier:
    lean_path: Path
    deletions: Set[int]
    additions: Dict[int, List[str]]
    def __init__(self, lean_path: Path):
        self.lean_path = lean_path
        self.deletions = set()
        self.additions = {}

    def replace_lines(self, start_line_ix: int, end_line_ix: int, new_lines: str) -> None:
        """
        Replace lines of code

        start_line_ix: Line index in the original file.  Inclusive.  0-indexed.
        end_line_ix:   Line index in the original file.  Exclusive.  0-indexed.              
        new_lines:     New code lines to add to file.  
                       Single string with new lines.  Must end in a newline
        """
        assert new_lines.endswith("\n")
        self._comment_out_lines(start_line_ix, end_line_ix)
        self._insert_lines(end_line_ix, new_lines)

    def add_lines(self, start_line_ix: int, new_lines: str) -> None:
        """
        Add lines of code

        start_line_ix: Line index in the original file to begin insert.
        new_lines:     New code lines to add to file.  
                       Single string with new lines.  Must end in a newline
        """
        assert new_lines.endswith("\n")
        self._insert_lines(start_line_ix, new_lines)

    def _comment_out_lines(self, start: int, end: int):
        for ix in range(start, end):
            assert ix not in self.deletions, f"Can't make multiple deletions to line {ix}."
            self.deletions.add(ix)

    def _insert_lines(self, ix: int, lines: str):
        assert ix not in self.additions, f"Can't make multiple additions to line {ix}."
        self.additions[ix] = lines[:-1].split("\n")

    def build_file(self):
        """
        Apply all edits and replace the current lean file.
        """
        new_lines = []
        with open(self.lean_path, "r") as f:
            for ix, line in enumerate(f):
                if ix in self.additions:
                    new_lines.append("--PR BEGIN CODE INSERT")
                    for new_line in self.additions[ix]:
                        new_lines.append(new_line + '\n')
                    new_lines.append("--PR END CODE INSERT")

                if ix in self.deletions:
                    new_lines.append("--PR REMOVE LINE: " + line)
                else:
                    new_lines.append(line)
        
        with open(self.lean_path, "w") as f:
            f.writelines(new_lines)
            
            




