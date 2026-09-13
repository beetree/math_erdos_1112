# Density dependency for the short proof

The pinned Mathlib does not supply Kneser’s asymptotic-density theorem. This
branch formalizes the consequence used by the paper: for sets containing zero,
either the sumset has at least the sum of their lower densities, or it contains
an arithmetic-progression tail. The final assembly is still in progress.

The proof uses ordinary e-transforms, a fair least-unresolved-element sequence,
and a minimum-gap dichotomy. Unbounded gaps give the density alternative by
counting. Stabilized gaps give a finite residue alphabet; compression and finite
modular subset sums produce arbitrarily long intervals. A finite Mann inequality
then supplies the required density estimate. Finite second sets are handled
directly by their zero contribution to joint density.

Primary mathematical sources:

- M. Kneser, *Abschätzung der asymptotischen Dichte von Summenmengen*,
  Math. Z. 58 (1953), 459–484. [Original volume at Göttingen](https://gdz.sub.uni-goettingen.de/id/PPN266833020_0058).
- John B. Lane, *A New Approach to Kneser’s Theorem on Asymptotic Density*,
  Virginia Polytechnic Institute and State University, 1973.
  [University repository](https://vtechworks.lib.vt.edu/items/9c965bdb-611b-42ef-8bca-8d76c6ad2d92).
  Chapter I, Theorems 12–13 supply the finite Mann and long-interval estimates;
  Chapter II, Definition 6 and Lemmas 7–9 supply compression and density scaling.

The Lean code is a new formalization of these mathematical arguments. The source
PDFs are not distributed with this repository. The finite Kneser port in the
separate `KneserFinite` directory has its own provenance; it does not establish
this asymptotic-density result.

`Defs.lean` defines counts, lower density, joint lower density and analytic
helpers. `ETransform.lean` proves the transform identities. The remaining
components are in `Short/Kneser*.lean`; see the root `PROGRESS.md` for which
assemblies are verified. An explicit theorem hypothesis is not an axiom, but
it remains an obligation until its caller supplies a proved result.
