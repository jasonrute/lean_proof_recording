# TODO

## Infrastructure
- [x] Record githash for lean and mathlib and lean github/version.  Put in raw_data
- [ ] Put lean running inside context manager.  Hopefully this will prevent runaway lean processes if python is closed early.
- [x] Save all lean files in paths.  This way we also save any modifications to the base lean files.
- [x] Save files first.  We want to do all easy stuff before running the long script which may fail.
- [ ] Figure out how to get lean files so as not to modifying elan toolchains
  - [x] Manually
  - [ ] Automatically
- [ ] Make full workflow
  - [x] Manually
  - [ ] (More) Automatically
- [x] Make seperate process to break up the traces.  For each trace, add filename and trace position.
- [ ] Make class for accessing raw_data
- [ ] **Figure out how to load data faster (or at least by file so I'm not waiting as long)**
  - [ ] I could do the initial read, break into files, and then do the full pipeline for each file seperately?

## File parsing and tokenizer
- [x] **Run parser over file which matches parentheses and other things.  Get it to run on all of mathlib.**
  - [x] Cases:
    - Matching `()`, `[]`, `begin...end`, `match...end`, etc
    - Seperators `,`, `;`, `|`, etc
      - Turn on/off as needed.  match `|` at outermost level and inside `match...end` only
    - Commands are seperators at outermost level and inside `namespace...end`, `open...end`
  - [x] Groupsings: e.g. `['(', ['big', 'apple'], ',', 'orange', ')']`
  - [ ] Add better types to parser
  - [ ] Add better position recording

## Tactic command recording
- [ ] **Combine all tactics with same (line, column, depth) and use that to do tactic recording.  Then ignore index.**
- [ ] **Use parsing to find matching `{` for tactic symbol `}`.  This way can avoid cases with no children.**
- [ ] Test on mathlib
- [ ] Fix known issues:
  - [ ] `...;[...]`
  - [ ] trailing commas
  - [ ] dead tactics
  - [ ] `<|>`
- [ ] Add more checks
  - [ ] Check that tactic strings don't subsume non-decendent tactics
  - [ ] Check that blocks beginning in `begin` end with `end` or `, end`

## Tactic flow
- [ ] Seperate out as its own thing
- [ ] Record if tactic contributes to solving goal
- [ ] Maybe do more with finding straight path through the tree

## Tactic state recording
- [ ] record tactic state as string before and after
- [ ] maybe record which goals have changed?  Can I hash goals?  Or just compare metavariable ids?
- [ ] record environment hash
- [ ] Show possibility for more detailed tactic state recording
- [ ] make simple tactic prediction dataset

## Tactic parameter recording
- [ ] **make script to modify `parse` and `itactic` in parameters**
  - [ ] Improve parser to get relevant information
- [ ] use to find all tactic arguments
- [ ] compare to other tactic string methods
