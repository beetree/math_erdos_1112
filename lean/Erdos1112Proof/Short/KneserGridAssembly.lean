/- Composes the finite-word realization and residue-frame lemmas of
`Short/KneserGrid.lean` with the modular covering multiset of
`Short/KneserResidues.exists_modular_cover`, scaled by the class count `h`,
for the density route documented in `Short/KneserDensity/README.md`.

Given a compressed pair with a fixed base interval `[0,h)` in `A_i`, a
persistent pair at distance `F := (f/g)*h`, and a persistent residue
alphabet `h * (R/g)` modulo `F`: scales the unscaled covering multiset (at
modulus `F0 := f/g` over alphabet `G := R/g`) by `h`, threads it through
`Short/KneserGrid.realization_of_modular_subset_sums` starting from
`Finset.range h`, proves the scaled multiset's subset sums realize every
residue mod `F0*h`, and finishes with
`Short/KneserGrid.bounded_residue_frame` to produce arbitrarily long
intervals in a later first component (`interval_of_scaled_cover`).

No compression algebra, no long-block density estimate, no Mann count:
those are separate files. -/
import Erdos1112Proof.Short.Intervals
import Erdos1112Proof.Short.KneserResidues
import Erdos1112Proof.Short.KneserGrid

namespace Erdos1112.Proof.Short.KneserDensity

open Erdos1112.Proof Erdos1112.Proof.Short

/-- **Steps 5+6 assembled, with the scale `h`.** Given a finite alphabet `G`
and base modulus `F0 > 0` with `gcd (insert F0 G) = 1` (the finite-cyclic-
group coprimality from compression step 4), a compressed pair `(A,B)` fair
w.r.t. `FairAbsorption`, a base interval `[0,h) ⊆ A i`, second components
that persistently realize every scaled residue `h*d` modulo `F0*h` for
`d ∈ G`, and persistent pairs at distance `F0*h`: some later first
component contains an interval of every length `L`. -/
theorem interval_of_scaled_cover {A B : ℕ → Set ℕ} {F0 h i : ℕ} {G : Finset ℕ}
    (hF0 : 0 < F0) (hh : 0 < h) (hgcd : (insert F0 G).gcd id = 1)
    (hfair : FairAbsorption A B) (hmono : Monotone A) (hanti : Antitone B)
    (hinit : ∀ e < h, e ∈ A i)
    (hres : ∀ n ≥ i, ∀ d ∈ G, ∃ b ∈ B n, b % (F0 * h) = (h * d) % (F0 * h))
    (hpairs : ∀ n ≥ i, ∃ b ∈ B n, b + F0 * h ∈ B n) :
    ∀ L, ∃ j ≥ i, ∃ x, ∀ t < L, x + t ∈ A j := by
  -- Step 5's finite-cyclic-group covering multiset, at the unscaled modulus.
  obtain ⟨S₀, hS₀G, hS₀cov⟩ := exists_modular_cover G F0 hF0 hgcd
  -- Scale by `h`: subset sums scale exactly (`subsetSums_scale`).
  set S := S₀.map (h * ·) with hSdef
  have hScov_eq : subsetSums S = (subsetSums S₀).image (h * ·) := subsetSums_scale h S₀
  have hE : ∀ e ∈ Finset.range h, e ∈ A i := fun e he => hinit e (Finset.mem_range.mp he)
  -- Every scaled entry of `S` is persistently realized in `B`, from `hres`.
  have hSdelta : ∀ n ≥ i, ∀ δ ∈ S, ∃ b ∈ B n, b % (F0 * h) = δ % (F0 * h) := by
    intro n hn δ hδ
    obtain ⟨d, hdS₀, rfl⟩ := Multiset.mem_map.mp hδ
    exact hres n hn d (hS₀G d hdS₀)
  -- Step 5: realize `Finset.range h` shifted by every subset sum of `S`.
  obtain ⟨j, hji, E', hE'mem, hrep⟩ :=
    realization_of_modular_subset_sums hfair hmono hanti hE S hSdelta
  -- The scale arithmetic: `E'` hits every residue mod `F0*h`.
  have hE'cov : ∀ r < F0 * h, ∃ e' ∈ E', e' % (F0 * h) = r := by
    intro r hr
    set e := r % h with hedef
    set q := r / h with hqdef
    have hdiv : h * q + e = r := Nat.div_add_mod r h
    obtain ⟨u₀, hu₀mem, hu₀mod⟩ := hS₀cov (q % F0) (Nat.mod_lt q hF0)
    have hscaled : (h * u₀) % (h * F0) = (h * q) % (h * F0) :=
      (show Nat.ModEq F0 u₀ q from hu₀mod).mul_left' h
    have hu : h * u₀ ∈ subsetSums S := by
      rw [hScov_eq]; exact Finset.mem_image.mpr ⟨u₀, hu₀mem, rfl⟩
    have heF : e < h := Nat.mod_lt r hh
    obtain ⟨e', he'mem, he'mod⟩ := hrep (h * u₀) hu e (Finset.mem_range.mpr heF)
    refine ⟨e', he'mem, ?_⟩
    have hchain2 : (e + h * u₀) % (h * F0) = (e + h * q) % (h * F0) :=
      Nat.ModEq.add_left e (show Nat.ModEq (h * F0) (h * u₀) (h * q) from hscaled)
    have hFh : h * F0 = F0 * h := by ring
    rw [hFh] at hchain2
    have heq2 : e + h * q = r := by omega
    rw [he'mod, hchain2, heq2, Nat.mod_eq_of_lt hr]
  -- Step 6: the residue-frame corollary turns the covering `E'` into an
  -- actual interval.
  intro L
  obtain ⟨j', hjj', x, hx⟩ :=
    bounded_residue_frame hfair hmono hanti (show 0 < F0 * h by positivity) hE'mem hE'cov
      (fun n hn => hpairs n (hji.trans hn)) L
  exact ⟨j', hji.trans hjj', x, hx⟩

end Erdos1112.Proof.Short.KneserDensity
