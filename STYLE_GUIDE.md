# Mathlib Style Guide — Status

This document summarizes code quality improvements made to bring the project
closer to Mathlib standards.

## Changes Made

### Bug fixes
- **Typo fix**: `NowhereLocllyConstant` → `NowhereLocallyConstant` (in `CBAnalysis.lean`, `NonScattered.lean`)

### File naming
- `MaxMinhelpers.lean` → `MaxMinHelpers.lean` (CamelCase)
- `blackboard.lean` → `Blackboard.lean` (CamelCase)
- Updated all import statements referencing these files

### Deprecated tactic migration
- **Replaced all 228 `refine'` instances** with `refine` using `?_` placeholders.
  Several non-trivial cases required restructuring proofs:
  - `Continuous.congr`/`ContinuousOn.congr` patterns using `use` were refactored
    to use explicit `(f := ...)` named arguments or `apply` with `pick_goal`
  - `ContinuouslyReduces` existential witnesses made explicit
  - Argument order in recursive calls made explicit where inference failed

### Removed redundant options
- **Removed `set_option relaxedAutoImplicit false`** from all 38 files
  (this is the default in Lean 4.28.0)

### `set_option maxHeartbeats` localization
- **Removed global `set_option maxHeartbeats`** from all 44 files.
- Only 7 declarations across 5 files actually needed elevated heartbeats:
  - `CBRankHelpers.lean`: `CBLevel_block_backward` (4M)
  - `NonScattered.lean`: `cantor_g_sigma_isEmbedding` (4M), `nlc_countable_embedding_concrete` (4M)
  - `MaxMinHelpers.lean`: `gluingSet_subtype_val_scattered` (4M)
  - `ClopenPartitionReduces.lean`: `clopen_partition_to_gluing_reduces` (4M)
  - `MinFunHelpers.lean`: `pgl_lower_bound_tau_cont` (8M)
  - `MaxFunMaximum.lean`: `simple_piece_reduces_to_maxfun` (4M)
  - `GeneralStructure.lean`: `MaxFun_le_MinFun` (8M), `MaxFun_le_limit_rank` (8M),
    `general_structure_theorem` (8M)
- All other declarations compile with the default 200K heartbeats.

### Spacing normalization
- **Removed spaces inside parentheses**: `( fun x => ...)` → `(fun x => ...)`
  and `(... )` → `(...)` across 730 lines in 33 files
- **Removed spaces inside brackets**: `[ arg1, arg2 ]` → `[arg1, arg2]`
- **Removed trailing whitespace** from 65 lines across all files
- **Normalized trailing newlines**: ensured all files end with exactly one newline

### Documentation
- **Added `/-! ... -/` module docstrings** to all files, including:
  - `Main.lean`, `SelfSimilarity.lean`, `Blackboard.lean`
  - `BaireSpace/Basics.lean`, `Bqo/2nLTmIsTwoBQO.lean`
  - `PointedGluing/ContinuousOnTau.lean`, `PointedGluing/MaxFunLimitRank.lean`
- **Converted 153 block comments** (`/- ... -/`) preceding declarations to proper
  doc comments (`/-- ... -/`) where appropriate (short comments ≤ 5 lines)
- Added `/-- ... -/` docstrings to definitions:
  - `SuccMaxDom`, `SuccMaxFun` in `Defs.lean`
  - `gClopenDom`, `gClopenFun`, `gRestr`, `cbRankRestr`, `TreeT`, `gClopenDomEquiv`
    in `MaxFunLimitRank.lean`

### Code cleanup
- **Replaced `exact?`** with actual proof terms in 6 files
- **Fixed 124 unused variable warnings** by prefixing with `_`
- **Fixed 6 unused section variable warnings** by adding `omit [...] in`
- **Fixed unused simp arguments** in `GeneralStructure.lean`, `MaxFunLimitRank.lean`,
  `CBRankHelpers.lean` (3 of the original warnings)
- **Fixed `simpa` → `simp`** where suggested by linter (`UpperBound.lean`)
- **Fixed `<;>` → `;`** where linter indicated only one goal (`MaxFunMaximum.lean`)
- **Merged `intro` calls** where suggested (`MinFunHelpers.lean`)
- **Removed trailing semicolons** from all `.lean` files
- **Removed banner-style comments** (`-- ════════════`) with cleaner section
  markers or `/-! ... -/` documentation blocks
- **Cleaned up `Main.lean`** (removed excessive `set_option` and pretty-printing options)

## Remaining Lower-Priority Items

### 1. Line length (>100 chars)
Approximately 540 lines exceed the Mathlib 100-character line length limit.
Most of these are in complex tactic proofs with inline expressions (e.g.,
long `simp_all` calls, nested `obtain`/`refine` chains, or expressions with
many hypothesis names). Breaking these up would require careful restructuring
of individual proof steps.

### 2. Unused simp arguments
The linter no longer reports unused simp argument warnings in the current build.
Previously reported warnings appear to have been resolved by earlier cleanup passes.
