# TODO

## Infrastructure
- [ ] Record githash for lean and mathlib and lean github/version.  Put in raw_data
- [ ] Put lean running inside context manager.  Hopefully this will prevent runaway lean processes if python is closed early.
- [ ] Save all lean files in paths.  This way we also save any modifications to the base lean files.
- [ ] Save files first.  We want to do all easy stuff before running the long script which may fail.
- [ ] Figure out how to get lean files so as not to modifying elan toolchains
- [ ] Make full workflow
- [ ] Make seperate process to break up the traces.  For each trace, add filename and trace position.

## Tactic command recording
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
- [ ] make script to modify `parse` and `itactic` in parameters
- [ ] use to find all tactic arguments
- [ ] compare to other tactic string methods
