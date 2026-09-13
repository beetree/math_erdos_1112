/-
Compatibility shim: the two-letter combinatorial core (the interval
property, the sweep, the width dichotomy, and the boundary width
palindrome–border–period argument) has moved to
`Erdos1112Proof.Short.BinaryCore`, under the same namespace
(`Erdos1112.Proof`) and the same declaration names (`qCount`, `Wset`,
`wmin`, `wmax`, `sweep`, `WidthTwoAt`, `IsPalindromePrefix`,
`width_of_unbalanced`, etc.) — see that file for the paper correspondence
and documentation.

This file now only re-exports those declarations via `import`, so that
existing dependents of `NonEx.TwoLetter.Core`
(`NonEx/TwoLetter/MH/Slope.lean`, `NonEx/TwoLetter/MH/Subwindow.lean`,
`NonEx/TwoLetter/MH/Walk.lean`, and the root `Erdos1112Proof.lean`)
continue to build unchanged. It is temporary scaffolding for the old
balanced/Sturmian (`NonEx.TwoLetter.Balanced`, `NonEx.TwoLetter.MH.*`)
proof, pending its deletion once nothing else depends on it.
-/
import Erdos1112Proof.Short.BinaryCore
