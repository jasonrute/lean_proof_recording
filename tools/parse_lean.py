import sys
from pathlib import Path
from pprint import pprint
import traceback
from typing import Any, Dict, List, Optional, Set

from tokenize_lean_files import LeanFile, Token

COMMANDS = {"theorem", "axiom", "axioms", "variable", "protected", "private", "hide",
         "definition", "meta", "mutual", "example", "noncomputable", "abbreviation",
         "variables", "parameter", "parameters", "constant", "constants",
         "using_well_founded", "[whnf]",
         "end", "namespace", "section", "prelude",
         "import", "inductive", "coinductive", "structure", "class", "universe", "universes", "local",
         "precedence", "reserve", "infixl", "infixr", "infix", "postfix", "prefix", "notation",
         "set_option", "open", "export", "@[",
         "attribute", "instance", "include", "omit", "init_quotient",
         "declare_trace", "add_key_equivalence",
         "run_cmd", "#check", "#reduce", "#eval", "#print", "#help", "#exit",
         "#compile", "#unify", "lemma", "def"}

ARROWS = {'->', '→'}
BINDERS = {'Pi', 'forall', '∀', 'Π', 'Σ', '∑', '∏', 'exists', '∃', 'λ', 'fun', '⨆', '⋂', '⋃', '∫', '∫⁻', '⨁'}
BRACKETS = {'{': '}', '(': ')', '[': ']', '⟨': '⟩', '⟪': '⟫', '⟮': '⟯'}
LEFT_BRACKETS = set(BRACKETS.keys())
RIGHT_BRACKETS = set(BRACKETS.values())

def next_token(lean_file, token):
    # note we use end_column here
    for t in lean_file.iter_tokens_right(token.line, token.end_column):
        return t

def prev_token(lean_file, token):
    for t in lean_file.iter_tokens_left(token.line, token.start_column):
        return t

def search_right(lean_file, start, targets):
    for t in lean_file.iter_tokens_right(start.line, start.start_column):
        if t.string in targets:
            return t
    return None

def search_left(lean_file, start, targets):
    for t in lean_file.iter_tokens_left(start.line, start.start_column):
        if t.string in targets:
            return t
    return None

class LeanParser:
    token_lines : List[List[Token]]
    line : int
    column: int
    pos: int
    current_token: Optional[Token]
    def __init__(self, lean_file: LeanFile, line: int, column: int):
        """
        Start parser on this file and this position
        """
        self.token_lines = lean_file.lines
        self.line = line
        self.column = column
        pos = None
        current = None
        for i, t in enumerate(self.token_lines[self.line]):
            if t.start_column == column:
                pos = i
                current = t
        assert pos is not None
        assert current is not None
        self.pos = pos
        self.current_token = current  
    
    # low level parser stuff
    def peek(self) -> Token:
        return self.current_token

    def next(self) -> Token:
        token = self.current_token
        assert token is not None

        # avoid using the absolute positions in the tokens
        length = self.current_token.end_column - self.current_token.start_column
        
        if self.pos + 1 < len(self.token_lines[self.line]):
            self.pos += 1
            self.column += length
        else:
            self.line += 1
            self.pos = 0
            self.column += 0
        
        if self.is_eof():
            self.current_token = None
        else:
            self.current_token = self.token_lines[self.line][self.pos]
        
        return token

    def is_eof(self) -> bool:
        return self.line == len(self.token_lines)

    def raise_error(self, msg: str):
        raise Exception(msg, self.line, self.column)

    # medium level parsing
    def read_next(self) -> str:
        if self.is_eof():
            self.raise_error('Expected token but EOF')
        return self.next().string

    def read_token(self, expected_string: str) -> str:
        t = self.next()
        if t.string != expected_string:
            self.raise_error('Expected {} but found {}'.format(repr(expected_string), repr(t.string)))
        return t.string
    
    def is_token(self, expected_string: str) -> bool:
        t = self.peek()
        return t.string == expected_string

    def read_token_in(self, expected_strings: Set[str]) -> str:
        t = self.next()
        if t.string not in expected_strings:
            self.raise_error('Expected {} but found {}'.format(repr(expected_strings), repr(t.string)))
        return t.string

    def is_token_in(self, expected_strings: Set[str]) -> bool:
        t = self.peek()
        return t.string in expected_strings

    def read_alphanum(self) -> str:
        t = self.next()
        if t.type != "alphanumeric":
            self.raise_error('Expected alphanumeric but found {}'.format(repr(t.string)))
        return t.string

    def is_alphanum(self) -> bool:
        t = self.peek()
        return t.type == "alphanumeric"

    def consume_space(self):
        while not self.is_eof() and self.peek().type in ["whitespace", "line_comment", "block_comment"]:
            self.next()  # consume that token
    
    # high level parse stuff
    def read_univs(self) -> Dict[str, Any]:
        self.read_token("{")
        self.consume_space()
        univs = []
        while not self.is_token("}"):
            u = self.read_alphanum()
            univs.append(u)
            self.consume_space()
        self.read_token("}")
        self.consume_space()
        return {
            "type": "univs",
            "univs": univs
        }
    def read_name_part(self) -> str:
        if self.is_token("«"):
            l = self.read_token("«")
            n = self.read_alphanum()
            r = self.read_token("»")
            return l + n + r
        else:
            return self.read_alphanum()

    def read_namespace(self) -> str:
        name = self.read_name_part()
        self.read_token(".")
        return name

    def read_full_name(self):
        self.consume_space()
        name_path = []
        name = self.read_name_part()
        name_path.append(name)
        while self.is_token("."):
            self.read_token(".")
            name = self.read_name_part()
            name_path.append(name)
        return {
            "type": "name", 
            "name": name_path
        }

    def read_expr_until(self, end_tokens: Set[str]) -> Dict[str, Any]:
        """
        This is tricky, since I don't know the full expression syntax.  
        I'll cheat and just match with the expected end token.
        """
        self.consume_space()
        expr_parts = []
        while not self.is_token_in(end_tokens):
            # go through all the expression constructors
            # binders
            if self.is_token_in(BINDERS):
                binder = self.read_token_in(BINDERS)
                bound_part = self.read_expr_until({","})
                self.read_token(",")
                expr = self.read_expr_until(end_tokens)
                part = {
                    "type": "bound_expr",
                    "binder": binder,
                    "bound_part": bound_part,  # not parsing this right now
                    "expr": expr
                }

            # brackets {} () [], etc with comma seperators
            elif self.is_token_in(LEFT_BRACKETS):
                left_bracket = self.read_token_in(LEFT_BRACKETS)
                right_bracket = BRACKETS[left_bracket]
                sub_exprs = []
                sub_expr = self.read_expr_until({",", right_bracket})
                sub_exprs.append(sub_expr)
                while self.is_token(","):
                    self.read_token(",")
                    sub_expr = self.read_expr_until({",", right_bracket})
                    sub_exprs.append(sub_expr)
                self.read_token(right_bracket)
                part = {
                    "type": "bracket",
                    "brackets": [left_bracket, right_bracket],
                    "exprs": sub_exprs
                }

            # if then else
            elif self.is_token("if"):
                self.read_token("if")
                if_part = self.read_expr_until({"then"})
                self.read_token("then")
                then_part = self.read_expr_until({"else"})
                self.read_token("else")
                else_part = self.read_expr_until(end_tokens)
                part = {
                    "type": "ite",
                    "if": if_part,
                    "then": then_part,
                    "else": else_part
                }

            # let := in
            elif self.is_token("let"):
                self.read_token("let")
                var_part = self.read_expr_until({":="})
                self.read_token(":=")
                expr_part = self.read_expr_until({"in"})
                self.read_token("in")
                body_part = self.read_expr_until(end_tokens)
                part = {
                    "type": "let",
                    "var": var_part,
                    "expr": expr_part,
                    "body": body_part
                }

            # match with | := end
            elif self.is_token("match"):
                self.read_token("math")
                match_part = self.read_expr_until({"with"})
                self.read_token("with")
                self.consume_space()
                cases = [] 
                while self.is_token("|"):
                    self.read_token("|")
                    case_start = self.read_expr_until({":="})
                    case_body = self.read_expr_until({"|", "end"})
                    cases.append({
                        "type": "case",
                        "pattern": case_start,
                        "value": case_body
                    })
                self.read_token("end")
                part = {
                    "type": "match",
                    "match_expr": match_part,
                    "cases": cases
                }

            # begin end
            elif self.is_token("begin"):
                self.read_token("begin")
                tactics = []
                # TODO: Make this read_tactic_until
                tactic = self.read_expr_until({",", "end"})
                tactics.append(tactic)
                while self.is_token(","):
                    self.read_token(",")
                    # TODO: Make this read_tactic_until
                    tactic = self.read_expr_until({",", "end"})
                    tactics.append(tactic)
                self.read_token("end")
                part = {
                    "type": "beginend",
                    "tactics": tactics
                }

            # calc
            elif self.is_token("calc"):
                self.read_token("calc")
                calc_parts = []
                calc_part = self.read_expr_until({"..."} | end_tokens)
                calc_parts.append(calc_part)
                while self.is_token("..."):
                    self.read_token("...")
                    calc_part = self.read_expr_until({"..."} | end_tokens)
                    calc_parts.append(calc_part)
                part = {
                    "type": "calc",
                    "parts": calc_parts
                }

            # do
            elif self.is_token("do"):
                self.read_token("do")
                do_parts = []
                do_part = self.read_expr_until({","} | end_tokens)
                do_parts.append(do_part)
                while self.is_token(","):
                    self.read_token(",")
                    do_part = self.read_expr_until({","} | end_tokens)
                    do_parts.append(do_part)
                part = {
                    "type": "do",
                    "parts": do_parts
                }
            
            # by
            elif self.is_token("by"):
                self.read_token("by")
                # TODO: Make this read_tactic_until
                tactic = self.read_expr_until(end_tokens)
                part = {
                    "type": "by",
                    "tactic": tactic
                }

            # unexpected token
            elif self.is_token_in({","} | COMMANDS | RIGHT_BRACKETS):
                s = self.peek().string
                self.raise_error(f"Expected expression to end {end_tokens} but found {repr(s)}")
            
            else:
                # Include whitespace here since
                # it may be important, but convert commments
                # to whitespace
                # TODO: Remove comments
                part = self.read_next()

            expr_parts.append(part)
        return {
            "type": "expr", 
            "expr_parts": expr_parts
        }

    def read_parameter_block(self) -> Dict[str, Any]:
        left_bracket = self.read_token_in(LEFT_BRACKETS)
        right_bracket = BRACKETS[left_bracket]
        self.consume_space()
        # note a square bracket [ ] may not have variables or a colon
        expr = self.read_expr_until({":", ":=", right_bracket})
        
        if self.is_token(":"):
            self.read_token(":")
            vars = expr
            expr = self.read_expr_until({":=", right_bracket})
        else:
            vars = None
        
        if self.is_token(":="):
            self.read_token(":=")
            default_expr = self.read_expr_until({right_bracket})
        else:
            default_expr = None
        
        self.read_token(right_bracket)
        self.consume_space()
        return {
            "type": "param_block", 
            "brackets": [left_bracket, right_bracket],
            "vars": vars, 
            "type_expr": expr, 
            "default_expr": default_expr
        }

    def read_signature_type(self) -> Dict[str, Any]:
        arg_types = []
        type_expr = self.read_expr_until(ARROWS | {":=", "|"})
        while self.is_token_in(ARROWS):
            self.read_token_in(ARROWS)
            arg_types.append(type_expr)
            type_expr = self.read_expr_until(ARROWS | {":=", "|"})
        return {
            "type": "singature_type",
            "arg_type": arg_types,
            "result_type": type_expr
        }

    def read_signature(self) -> Dict[str, Any]:
        self.consume_space()
        params = []
        while self.is_token_in(LEFT_BRACKETS):
            param = self.read_parameter_block()
            params.append(param)
        self.consume_space()
        if self.is_token(":"):
            self.read_token(":")
            self.consume_space()
            sign_type = self.read_signature_type()
        else:
            sign_type = None
        return {
            "type": "signature",
            "params": params,
            "signature_type": sign_type
        }

    def read_body(self) -> Dict[str, Any]:
        parts = self.read_expr_until(COMMANDS)
        return {
            "type": "body", 
            "parts": parts
        }

    def read_def(self) -> Dict[str, Any]:
        self.consume_space()
        if self.is_token("{"):
            univs = self.read_univs()
        else:
            univs = None
        name = self.read_full_name()
        signature = self.read_signature()
        # TODO: fix this
        #body = self.read_body()
        return {
            "type": "deflike", 
            "univ": univs, 
            "name": name, 
            "signature": signature, 
            #"body": body
        }

def slice(lean_file, start, end):
    s = []
    for t in lean_file.iter_tokens_right(start.line, start.start_column):
        if t.line == end.line and t.start_column == end.start_column:
            return s
        s.append(t)

    return None

def main():
    assert len(sys.argv) == 2
    lean_dir = Path(sys.argv[1])
    assert lean_dir.is_dir

    for f in lean_dir.glob("**/*.lean"):
        #print(f)
        decls = set()
        lean_file = LeanFile(str(f))
        for line in lean_file.lines:
            for token in line:
                if token.string == "def" and prev_token(lean_file, token).type == "whitespace":
                    try:
                        parser = LeanParser(lean_file, token.line, token.start_column)
                        parser.read_token("def")
                        ast = parser.read_def()
                        #pprint(ast)
                        interactive_parts = []
                        for param in ast['signature']['params']:
                            if param['type_expr']['expr_parts'][0] in ["parse", "itactic", "interactive"]:
                                interactive_parts.append({
                                    'param_type': 'bracket',
                                    'parser': param['type_expr']['expr_parts'][1:]
                                })
                        for param in ast['signature']['signature_type']['arg_type']:
                            if param[0] in ["parse", "itactic", "interactive"]:
                                interactive_parts.append({
                                    'param_type': 'arrow',
                                    'parser': param[1:]
                                })
                        if interactive_parts:
                            print()
                            print(f)
                            print("".join(t.string for t in line))
                            pprint(interactive_parts)
                    except Exception:
                        print()
                        print(f)
                        print("".join(t.string for t in line))
                        traceback.print_exc()

if __name__ == "__main__":
    main()