1. trailing comma
outside-in approach
  if in {} or begin...end parent:
    check for trailing comma preceeding } or end
    if so, then adjust the end position
  otherwise I know I'm in a begin end block or <tactic> {...} block
    use parsing (as I'm doing to find matching `end` or `}`
    check for trailing comma preceeding the `end` or `}`
inside-out approach
  keep the same

2. Handle `... ; [...]`.
  when checking tokens if token is `;`, then check next (non-whitespace token) to see if it is `[`.  If so, then make it a `;[]` tactic.  (CAREFUL HERE:  I need to find the CORRECT ;)
  Check all code which uses `;` to see if it needs to be adapted to `;[]`
  When parsing outside-in style, 
    the first child should end at `;`
    the other children should be inside `[]` with the last child ending at `]`
  When parsing inside out, do as before.

3. Handle `<|>`.
  If `<|>` preceeds a tactic, then we know where a `<|>` block is.
  Jump up a level and insert the tactic.
  ...

4. Unexecuted tactics.
  Only <|> and ; can have dead tactics.  (Not even ;[].)  For ; we know there should be two children.  If not the second is dead.  But if nested, we don't know where the ; is.  To find that, we can search forward, counting `;`.  (In this case we want to do the inside-out search at the largest depths first.  We know the start of the dead tactic and can use that to find the end.)

  For <|> it is similar.  If we have a tactic ending in <|>, then we know we have a <|>.  


Main idea:
If we are careful, we can use forward inside-out search, but at every point check that we reached the expected point.  In the process, we will find trailing commas, <|>, `...;[...]` and dead tactics.
Start at lowest depth.
Do forward search (making sure to go as far as children.)
- If end with <|> then replace all pointers to this tactic with another level inbetween.
  - If next tactic is after the <|> then good
  - Otherwise it is unexecuted.  Add it into the tree.
- If end with ; then that ; is the position of the parent ; or ;[] tactic.
  - I should know if that is where ; is expected or if I'm in the second half of a nested ; and I don't know where to find ;
- If end with , and I'm in a begin, {, or ;[...] block (determine from start of block).  Then I expect next tactic to start after the comma.
  - If no next tactic, then has to be `end` or `}`. 
- Any other situation, I have to be either the last tactic in a ; or inside a by.  Use forward search to find the end.  If parent of ; is something other than `by`, then continue as before.

