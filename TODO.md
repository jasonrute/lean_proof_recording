# TODO

## Infrastructure
- [ ] Record githash for lean and mathlib and lean github/version.  Put in raw_data
- [ ] Figure out how to get lean files so not modifying elan toolchains
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
  - Check that tactic strings don't subsume non-decendant tactics

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
- [ ] make script to switch parser and itactic
- [ ] make script to switch parser and itactic
- [ ] record tactic state as string before and afte
