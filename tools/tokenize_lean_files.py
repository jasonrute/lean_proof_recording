"""
Tools for parsing lean files into tokens
"""
import collections
import re


# here we use 0-indexing for the lines and columns
Token = collections.namedtuple('Token', ['string', 'type', 'line', 'start_column', 'end_column'])

# there are other tokens as well, but these are important and/or easy to work with
SPECIAL_TOKENS = [["(",":",":",")"], [".",".","."], ["[","whnf","]"], ["<","|",">"], ["%","%"], ["(",")"], ["{","!"], ["!","}"], ["Type","*"], ["Sort","*"], ["(",":"], [":",")"], ["/","/"], [".","."], [":","="], ["@","@"], ["-",">"], ["<","-"], ["^","."], ["@","["], ["#","check"], ["#","reduce"], ["#","eval"], ["#","print"], ["#","help"], ["#","exit"], ["#","compile"], ["#","unify"], ["(","|"], ["|",")"]]
# make sure they are sorted longest first
SPECIAL_TOKENS = list(sorted(SPECIAL_TOKENS, key=len, reverse=True))

class LeanFile:
    def __init__(self, filename):
        assert filename.endswith(".lean"), filename

        # read file
        lines = []
        with open(filename, 'r') as f:
            for line in f:
                lines.append(line)
        
        # tokenize
        self.lines = []
        prev_token_type = 'whitespace'
        for i, line in enumerate(lines):
            tokens = LeanFile.tokenize_line(line, i, prev_token_type)
            prev_token_type  = tokens[-1].type
            self.lines.append(tokens)

    @staticmethod
    # this isn't completely accurate.  I think it also will capture
    # - char literals, e.g. 'a'
    # - 
    # see https://github.com/leanprover/lean/blob/master/src/util/name.cpp
    def is_name_char(c):
        # special good characters
        if c in ['_', "'"]:
            return True
        # three special bad unicode
        if c in ['λ', 'Π', 'Σ']:
            return False
        # standard characters
        u = ord(c)
        if (ord('A') <= u <= ord('Z') or
            ord('a') <= u <= ord('z') or
            ord('0') <= u <= ord('9')):
            return True
        # other acceptable unicode
        if ((0x3b1   <= u and u <= 0x3c9 and u != 0x3bb) or # Lower greek, but lambda
            (0x391   <= u and u <= 0x3A9 and u != 0x3A0 and u != 0x3A3) or # Upper greek, but Pi and Sigma
            (0x3ca   <= u and u <= 0x3fb) or               # Coptic letters
            (0x1f00  <= u and u <= 0x1ffe) or              # Polytonic Greek Extended Character Set
            (0x2100  <= u and u <= 0x214f) or              # Letter like block
            (0x1d49c <= u and u <= 0x1d59f) or             # Latin letters, Script, Double-struck, Fractur
            (0x207f  <= u and u <= 0x2089) or              # n superscript and numberic subscripts
            (0x2090  <= u and u <= 0x209c) or              # letter-like subscripts
            (0x1d62  <= u and u <= 0x1d6a)):               # letter-like subscripts
            return True
        return False
        
    @staticmethod
    def tokenize_line(line, line_num, prev_token_type):
        assert prev_token_type in ['whitespace', 'block_comment', 'line_comment'], prev_token_type
        # step 1: label char types
        # options: 'whitespace', 'symbol', 'alphanumeric', 'line_comment', 
        #          'block_comment', 'block_comment_terminal', 'string_literal', 
        #          'string_literal_terminal'
        prev_char = None
        prev_char_type = prev_token_type if prev_token_type != 'line_comment' else 'whitespace'
        char_types = []
        for i, char in enumerate(line):
            # label symbol type
            if prev_char_type == "line_comment":
                char_type = "line_comment"
            elif prev_char_type == "block_comment":
                if (prev_char, char) == ("-", "/"):
                    char_type = "block_comment_terminal"
                else:
                    char_type = "block_comment"
            elif prev_char_type == "string_literal":
                if char == '"' and prev_char != "\\":
                    char_type = "string_literal_terminal"
                else:
                    char_type = "string_literal"
            elif char == "-" and line[i+1] == "-":
                char_type = "line_comment"
            elif char == "/" and line[i+1] == "-":
                char_type = "block_comment"
            elif char.isspace():
                char_type = "whitespace"
            # this captures character literals too which is fine for now
            elif LeanFile.is_name_char(char):
                char_type = "alphanumeric"
            else:
                char_type = "symbol"
            
            char_types.append(char_type)
            prev_char_type = char_type
            prev_char = char
        
        # step 2: join certain char_type pairs
        tokens = []
        prev_char_type = None
        token_string = None
        token_type = None
        token_start = None
        
        for i, (char, char_type) in enumerate(zip(line, char_types)):
            if prev_char_type is None:
                token_string = char
                token_type = char_type
                token_start = i
            elif prev_char_type == "block_comment" and char_type == "block_comment_terminal":
                token_string += char
            elif prev_char_type == "string_literal" and char_type == "string_literal_terminal":
                token_string += char
            elif char_type != "symbol" and prev_char_type == char_type:
                token_string += char
            else:
                tokens.append(Token(token_string, token_type, line_num, token_start, i))
                token_string = char
                token_type = char_type
                token_start = i
            prev_char_type = char_type    
        tokens.append(Token(token_string, token_type, line_num, token_start, i))
        
        # step 3: combine certain tokens
        combined_tokens = []
        i = 0
        while i < len(tokens):
            # find longest token group which is in the list of special tokens
            # the tokens are sorted longest first
            for special in SPECIAL_TOKENS:
                if all(t.string == s for t, s in zip(tokens[i:i+len(special)], special)):
                    new_token = Token(
                        string="".join(special),
                        type='symbol',
                        line=tokens[i].line,
                        start_column=tokens[i].start_column,
                        end_column=tokens[i+len(special)-1].end_column
                    )
                    i2 = i + len(special)
                    break
            else:
                new_token = tokens[i]
                i2 = i + 1
            
            combined_tokens.append(new_token)
            i = i2

        return combined_tokens
    
    def get_token(self, line, column):
        assert line < len(self.lines)
        for token in self.lines[line]:
            if token.start_column < column:
                assert token.end_column <= column, "The provided line/column ({},{}) doesn't match with the closest token ({},{}):\n{}".format(line, column, line, token.start_column, token.string)
                continue
            if token.start_column == column:
                return token
            
        assert False
    
    def get_token_pos(self, line, column):
        assert line < len(self.lines)
        for pos, token in enumerate(self.lines[line]):
            if token.start_column < column:
                continue
            if token.start_column == column:
                return pos
            assert False
        assert False

    def iter_tokens_right(self, start_line, start_column):
        start_pos = self.get_token_pos(start_line, start_column)
        for line in self.lines[start_line:]:
            for token in line[start_pos:]:
                yield token
            start_pos = 0
    
    def iter_tokens_left(self, start_line, start_column):
        start_pos = self.get_token_pos(start_line, start_column)
        for line in reversed(self.lines[0:start_line+1]):
            for token in reversed(line[0: start_pos]): # don't include current token
                yield token
            start_pos = None

if __name__ == "__main__":
    #filename = "tmp/proof_recording_example.lean"
    filename = "/Users/jasonrute/.elan/toolchains/leanprover-community-lean-3.20.0/lib/lean/library/init/data/nat/bitwise.lean"

    assert not LeanFile.is_name_char('λ')
    assert not LeanFile.is_name_char('Π')
    assert not LeanFile.is_name_char('Σ')

    leanfile = LeanFile(filename)
    print(len(leanfile.lines))
    for line in leanfile.lines:
        #print(line)
        print([t.string for t in line])
        #print([t.type for t in line])
        #print([t.start_column for t in line])
        #print([t.end_column for t in line])