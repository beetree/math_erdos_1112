import Lake
open Lake DSL

package erdos1112 where

-- Erdős #1112 is verified against a pinned snapshot of the dependency stack:
--   formal-conjectures rev 75573bb6, Mathlib rev a3a10db0e9, Lean v4.27.0.
-- The revisions are frozen in `lake-manifest.json`; do not run `lake update`
-- (it would float the pins). See `README.md` for the build/verification recipe.
require formal_conjectures from git
  "https://github.com/google-deepmind/formal-conjectures" @ "75573bb6ae02bcb7008714e2bdb11ee09a52d142"

@[default_target]
lean_lib «Erdos1112» where

/-- Proof development for Erdős #1112: proves the canonical `Erdos1112.erdos_1112`
dichotomy (and the two halves) in `Erdos1112Proof/Final.lean`, `sorry`-free.
Marked `@[default_target]` so `lake build` builds the whole proof, not just the
definitions. -/
@[default_target]
lean_lib «Erdos1112Proof» where
