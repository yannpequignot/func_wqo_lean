# Mathlib Style Guide — Remaining Issues

This document summarizes the code quality improvements made and lists remaining issues
that should be addressed to bring the project closer to Mathlib standards.

## Changes Made

### Bug fixes
- **Typo fix**: `NowhereLocllyConstant` → `NowhereLocallyConstant` (in `CBAnalysis.lean`, `NonScattered.lean`)

### File naming
- `MaxMinhelpers.lean` → `MaxMinHelpers.lean` (CamelCase)
- `blackboard.lean` → `Blackboard.lean` (CamelCase)
- Updated all import statements referencing these files

### Code cleanup
- **Replaced `exact?`** with actual proof terms in 6 files
- **Fixed 124 unused variable warnings** by prefixing with `_`
- **Fixed 6 unused section variable warnings** by adding `omit [...] in`
- **Fixed unused simp arguments** in `GeneralStructure.lean`, `MaxFunLimitRank.lean`,
  `CBRankHelpers.lean` (3 of the original warnings)
- **Fixed `simpa` → `simp`** where suggested by linter (`UpperBound.lean`)
- **Fixed `<;>` → `;`** where linter indicated only one goal (`MaxFunMaximum.lean`)
- **Merged `intro` calls** where suggested (`MinFunHelpers.lean`)
- **Removed trailing semicolons** from all `.lean` files (~1916 instances)
- **Fixed angle bracket spacing** (`⟨ x, y ⟩` → `⟨x, y⟩`, ~476 instances)

### Documentation
- Added `/-! ... -/` module docstrings to:
  - `BaireSpace/Basics.lean`
  - `Bqo/2nLTmIsTwoBQO.lean`
  - `PointedGluing/ContinuousOnTau.lean`
  - `PointedGluing/MaxFunLimitRank.lean`
- Added `/-- ... -/` docstrings to definitions:
  - `SuccMaxDom`, `SuccMaxFun` in `Defs.lean`
  - `gClopenDom`, `gClopenFun`, `gRestr`, `cbRankRestr`, `TreeT`, `gClopenDomEquiv`
    in `MaxFunLimitRank.lean`

### Cleanup
- Cleaned up `Main.lean` (removed excessive `set_option` and pretty-printing options)

## Remaining Issues (lower priority)

### 1. Unused simp arguments (45 warnings)
Many `simp` / `simp_all` calls include arguments that the linter reports as unused.
These are tricky to fix automatically because removing the argument sometimes causes
the proof to break (the argument may be needed for intermediate steps but appears unused
to the linter). Each should be investigated manually.

Affected files: `Gluing.lean`, `CBRankHelpers.lean`, `CBRankSimpleHelpers.lean`,
`ContinuousOnTau.lean`, `BasicProperties.lean`, `MaxMinHelpers.lean`,
`NonScattered.lean`, `Decomposition.lean`, `MaxFunMaximum.lean`,
`MinFunHelpers.lean`, `MinFunLocalHelpers.lean`, `GeneralStructureHelpers.lean`

### 2. `refine'` usage (224 instances)
`refine'` is deprecated in Mathlib in favor of `refine` with `?_` placeholders.
Migrating requires changing unnamed goals `_` to `?_` throughout. This is a
mechanical but widespread change.

### 3. Line length (>100 chars)
Approximately 600 lines exceed the Mathlib 100-character line length limit.
Many of these are in complex tactic proofs with inline expressions. Breaking
these up improves readability but requires careful attention to tactic structure.

### 4. Spaces around operators in tactic expressions
Some files have extra whitespace in places like `( fun x => ... )`, `[ arg1, arg2 ]`,
etc. Mathlib prefers minimal whitespace: `(fun x => ...)`, `[arg1, arg2]`.

### 5. Comment style
Some comments use banner-style separators (`-- ════════════`) or section markers
(`-- ── Step 1: ... ──────`). Mathlib prefers `/-! ... -/` documentation blocks
for section headers and minimal inline comments.

### 6. `set_option maxHeartbeats`
Most files set `maxHeartbeats` to 4000000 or 8000000 globally. Mathlib prefers
localizing these to specific declarations that need them, using
`set_option maxHeartbeats N in` before the specific `lemma`/`theorem`.

### 7. `relaxedAutoImplicit false`
This option is set in most files. In current Mathlib, `relaxedAutoImplicit false`
is the default and does not need to be set explicitly.
