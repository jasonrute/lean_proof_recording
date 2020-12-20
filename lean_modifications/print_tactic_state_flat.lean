/- This is a staging area for code which will be inserted
into a Lean file. 

The code to be inserted is between the line comments
`PR BEGIN MODIFICATION` and `PR END MODIFICATION`

It will be inserted by `insert_proof_recording_code.py`.

Insert info:
  - file: `_target/lean/library/init/meta/tactic.lean`
  - location: end of file

Most of this code is carefully written, but
any code labeled "BEGIN/END CUSTOMIZABLE CODE"
encourages customization to change what
is being recorded
-/

--PR BEGIN MODIFICATION
meta def tactic_state.to_flattened_string (ts : tactic_state) : tactic string := pure ts.to_format.to_string
local notation `PRINT_TACTIC_STATE` := tactic_state.to_flattened_string
--PR END MODIFICATION
