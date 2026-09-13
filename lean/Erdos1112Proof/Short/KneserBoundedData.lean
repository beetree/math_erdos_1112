/- Assembles the persistent-residue arithmetic and the compressed grid data
from the stabilized branch of `Short/KneserStabilization.lean`, for the
density route documented in `Short/KneserDensity/README.md`.

Given `Aseq A₀ B₀`, `Bseq A₀ B₀` (`Short/KneserConcrete.lean`) and a stable
gap `f` together with a stable residue alphabet `R` of `Bseq A₀ B₀` mod `f`
from a combined index `N'` (`Short/KneserStabilization.stabilization_bundle`):

* proves the **persistent-residues arithmetic** (`persistent_residue_mod`):
  scaling a residue `r' ≡ b (mod f)` by `1/g` (`g := gcd(insert f R)`) and
  then by `h` gives `h·(b/g) ≡ h·(r'/g) (mod (f/g)·h)`;
* derives the persistent pair at the compressed distance from `gapMin`'s
  pair-attainment (`Short/KneserStabilization.gapMin_pair`) via
  `Short/KneserCompressionSequence.compressed_pair`;
* lifts the compression algebra (`Short/KneserCompression`,
  `Short/KneserCompressionSequence`) to the actual sequences `Aseq`/`Bseq`
  (fairness, monotonicity/antitonicity, the initial interval);
* discharges every hypothesis of
  `Short/KneserGridAssembly.interval_of_scaled_cover` and invokes it,
  producing arbitrarily long intervals in a later compressed first
  component.

`compressed_grid_bundle` takes the minimum representative frame
`r : Fin h → ℕ` (`hr0`, `hr_inj`, `hrmem`, `hrA`) as an explicit hypothesis,
generic in whatever frame is supplied. `Short/KneserMinima.lean` proves the
frame is invariant along the sequence; `Short/KneserFrame.lean` supplies
the enumeration (`exists_frame`). `compressed_grid_bundle_unconditional`
specializes `compressed_grid_bundle` to `exists_frame`'s output, so the
only remaining hypotheses are `0 ∈ A₀` and the stabilization data itself.
Both theorems are kept: `compressed_grid_bundle` stays available for any
other frame source.

The block-growth/cofinite-vs-density dichotomy (`Short/KneserBlocks.lean`,
`Short/KneserBlockSequence.lean`), the compression density-count algebra
beyond what feeds the frame (`Short/KneserCompression`,
`Short/KneserDensityScaling.lean`), and the unbounded-gap branch
(`Short/KneserSpacing.lean`) are separate files, not duplicated here. -/
import Erdos1112Proof.Short.KneserGridAssembly
import Erdos1112Proof.Short.KneserCompressionSequence
import Erdos1112Proof.Short.KneserConcrete
import Erdos1112Proof.Short.KneserStabilization
import Erdos1112Proof.Short.KneserFrame

namespace Erdos1112.Proof.Short

open Erdos1112.Proof.Short.KneserDensity
open Erdos1112.Proof.Short.KneserCompression
open scoped Classical

/-! ### The persistent-residues arithmetic (the new content of this file) -/

/-- **The missing-scale congruence.** If `b ≡ r' (mod f)` and `g` divides
`f`, `r'`, and `b`, then scaling by `1/g` and then by `h` preserves the
congruence, at the scaled modulus `(f/g)·h`: `h·(b/g) ≡ h·(r'/g)`. This is
exactly the arithmetic step 4 needs to transport `B`'s stable residue
alphabet mod `f` to the compressed alphabet `h·(R/g)` mod `(f/g)·h`. -/
theorem persistent_residue_mod {f g r' b h : ℕ} (hg : 0 < g) (hgf : g ∣ f) (hgr' : g ∣ r')
    (hbmod : b % f = r') :
    (h * (b / g)) % ((f / g) * h) = (h * (r' / g)) % ((f / g) * h) := by
  obtain ⟨k, hk⟩ : ∃ k, b = f * k + r' := ⟨b / f, by
    conv_lhs => rw [← Nat.div_add_mod b f, hbmod]⟩
  obtain ⟨f', rfl⟩ := hgf
  obtain ⟨r'', rfl⟩ := hgr'
  have hbg : b / g = r'' + f' * k := by
    rw [hk, show g * f' * k + g * r'' = g * (r'' + f' * k) by ring,
      Nat.mul_div_cancel_left _ hg]
  have hr'g : g * r'' / g = r'' := Nat.mul_div_cancel_left _ hg
  have hfg : g * f' / g = f' := Nat.mul_div_cancel_left _ hg
  rw [hbg, hr'g, hfg]
  have he : h * (r'' + f' * k) = h * r'' + (f' * h) * k := by ring
  rw [he, Nat.add_mul_mod_self_left]

/-- If `gapMin S = f > 0`, `gapSet S` is nonempty (else `sInf` of the empty
set would force `gapMin S = 0`). Bridges `KneserStabilization`'s stabilized
gap value back to the pair-attainment lemmas, which need nonemptiness. -/
theorem gapSet_nonempty_of_gapMin_pos {S : Set ℕ} {f : ℕ} (hf : 0 < f) (hgap : gapMin S = f) :
    (gapSet S).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  unfold gapMin at hgap
  rw [hne] at hgap
  simp [Nat.sInf_empty] at hgap
  omega

/-- Repackaging `stable_gcd_dvd_B_from` (whose `hstable` hypothesis is
self-referential, `residueAlphabet B f n = residueAlphabet B f N`) for the
more convenient form actually available once the residue alphabet has
stabilized to a *named* `R`. -/
theorem stable_gcd_dvd_B_from' {B : ℕ → Set ℕ} {f N' : ℕ} {R : Finset ℕ} (hf : 0 < f)
    (hstabR : ∀ n, N' ≤ n → residueAlphabet B f n = R) :
    ∀ n, N' ≤ n → ∀ b ∈ B n, (insert f R).gcd id ∣ b := by
  intro n hn b hb
  have hstable' : ∀ m, N' ≤ m → residueAlphabet B f m = residueAlphabet B f N' := by
    intro m hm
    rw [hstabR m hm, hstabR N' le_rfl]
  have := stable_gcd_dvd_B_from hf hstable' n hn b hb
  rwa [hstabR N' le_rfl] at this

/-! ### The compressed grid bundle -/

/-- **The compressed-sequence interval-growth bundle.** From the ordinary
`e`-transform sequence `Aseq A₀ B₀`/`Bseq A₀ B₀`, a stable gap `f > 0` (from
`N` on) and stable residue alphabet `R` (from `N' ≥ N` on), together with a
minimum representative frame `r : Fin h → ℕ` for `Aseq A₀ B₀ N'`'s residue
classes mod `g := gcd(insert f R)` (`hr0`, `hr_inj`, `hrmem`, `hrA` — generic
here in the frame; see `compressed_grid_bundle_unconditional` below for the
specialization to `Short/KneserFrame.exists_frame`'s actual construction):
the compressed pair is positive-modulus, gcd-normalized, fair,
monotone/antitone, has persistent residues and persistent pairs at the
compressed scale, and consequently a later compressed first component
contains an interval of every length `L`. -/
theorem compressed_grid_bundle
    {A₀ B₀ : Set ℕ}
    {N f : ℕ} (hf : 0 < f) (hstabF : ∀ n, N ≤ n → gapMin (Bseq A₀ B₀ n) = f)
    {N' : ℕ} (hNN' : N ≤ N') {R : Finset ℕ}
    (hstabR : ∀ n, N' ≤ n → residueAlphabet (Bseq A₀ B₀) f n = R)
    {g F0 : ℕ} {G : Finset ℕ} {h : ℕ} {r : Fin h → ℕ}
    (hgdef : g = (insert f R).gcd id) (hF0def : F0 = f / g) (hGdef : G = R.image (· / g))
    (hh : 0 < h) (hr0 : r ⟨0, hh⟩ = 0)
    (hr_inj : Function.Injective (fun j : Fin h => r j % g))
    (hrmem : ∀ j, r j ∈ Aseq A₀ B₀ N')
    (hrA : ∀ a ∈ Aseq A₀ B₀ N', ∃ j t, a = r j + g * t) :
    0 < g ∧ 0 < F0 ∧ (insert F0 G).gcd id = 1 ∧
    FairAbsorption (fun n => compressedSet g h r (Aseq A₀ B₀ n))
      (fun n => compressedSetZero g h (Bseq A₀ B₀ n)) ∧
    Monotone (fun n => compressedSet g h r (Aseq A₀ B₀ n)) ∧
    Antitone (fun n => compressedSetZero g h (Bseq A₀ B₀ n)) ∧
    0 ∈ compressedSet g h r (Aseq A₀ B₀ N') ∧
    r ⟨0, hh⟩ = 0 ∧ Function.Injective (fun j : Fin h => r j % g) ∧
    (∀ a ∈ Aseq A₀ B₀ N', ∃ j t, a = r j + g * t) ∧
    (∀ n, N' ≤ n → ∀ d ∈ G, ∃ b ∈ compressedSetZero g h (Bseq A₀ B₀ n),
      b % (F0 * h) = (h * d) % (F0 * h)) ∧
    (∀ n, N' ≤ n → ∃ b ∈ compressedSetZero g h (Bseq A₀ B₀ n),
      b + F0 * h ∈ compressedSetZero g h (Bseq A₀ B₀ n)) ∧
    (∀ L, ∃ j ≥ N', ∃ x, ∀ t < L, x + t ∈ compressedSet g h r (Aseq A₀ B₀ j)) := by
  have hgpos : 0 < g := hgdef ▸ stable_gcd_pos hf
  have hgf : g ∣ f := hgdef ▸ stable_gcd_dvd_f
  have hF0pos : 0 < F0 := hF0def ▸ Nat.div_pos (Nat.le_of_dvd hf hgf) hgpos
  have hgcdnorm : (insert F0 G).gcd id = 1 := by
    rw [hF0def, hGdef, hgdef]; exact stable_gcd_normalized hf
  have hfair : FairAbsorption (fun n => compressedSet g h r (Aseq A₀ B₀ n))
      (fun n => compressedSetZero g h (Bseq A₀ B₀ n)) := compressed_fair (fair_Aseq_Bseq A₀ B₀)
  have hmono : Monotone (fun n => compressedSet g h r (Aseq A₀ B₀ n)) :=
    fun m n hmn => compressedSet_mono (Aseq_monotone A₀ B₀ hmn)
  have hanti : Antitone (fun n => compressedSetZero g h (Bseq A₀ B₀ n)) :=
    fun m n hmn => compressedSetZero_mono (Bseq_antitone A₀ B₀ hmn)
  have hzero : 0 ∈ compressedSet g h r (Aseq A₀ B₀ N') :=
    compressed_initial_interval hrmem 0 hh
  have hgdvdB : ∀ n, N' ≤ n → ∀ b ∈ Bseq A₀ B₀ n, ∃ t, b = g * t := by
    intro n hn b hb
    have hdvd : g ∣ b := hgdef ▸ stable_gcd_dvd_B_from' hf hstabR n hn b hb
    obtain ⟨t, ht⟩ := hdvd
    exact ⟨t, ht⟩
  have hres : ∀ n, N' ≤ n → ∀ d ∈ G, ∃ b ∈ compressedSetZero g h (Bseq A₀ B₀ n),
      b % (F0 * h) = (h * d) % (F0 * h) := by
    intro n hn d hd
    rw [hGdef] at hd
    obtain ⟨r', hr'R, rfl⟩ := Finset.mem_image.mp hd
    have hr'mem : r' ∈ residueAlphabet (Bseq A₀ B₀) f n := by rw [hstabR n hn]; exact hr'R
    obtain ⟨-, b, hbmem, hbmod⟩ := Finset.mem_filter.mp hr'mem
    have hgr' : g ∣ r' := hgdef ▸ stable_gcd_dvd_of_mem hr'R
    obtain ⟨t, rfl⟩ := hgdvdB n hn b hbmem
    refine ⟨h * t, ⟨t, hbmem, rfl⟩, ?_⟩
    have ht : g * t / g = t := Nat.mul_div_cancel_left _ hgpos
    have hpm := persistent_residue_mod (h := h) hgpos hgf hgr' hbmod
    rwa [ht, ← hF0def] at hpm
  have hpairs : ∀ n, N' ≤ n → ∃ b ∈ compressedSetZero g h (Bseq A₀ B₀ n),
      b + F0 * h ∈ compressedSetZero g h (Bseq A₀ B₀ n) := by
    intro n hn
    have hgapn : gapMin (Bseq A₀ B₀ n) = f := hstabF n (hNN'.trans hn)
    have hne : (gapSet (Bseq A₀ B₀ n)).Nonempty := gapSet_nonempty_of_gapMin_pos hf hgapn
    obtain ⟨b, hb, hbf⟩ := gapMin_pair hne
    rw [hgapn] at hbf
    have hcp := compressed_pair (B := Bseq A₀ B₀ n) (g := g) (h := h) (f := f) hgpos hgf
      (hgdvdB n hn) ⟨b, hb, hbf⟩
    rwa [← hF0def, mul_comm h F0] at hcp
  refine ⟨hgpos, hF0pos, hgcdnorm, hfair, hmono, hanti, hzero, hr0, hr_inj, hrA, hres, hpairs,
    fun L => ?_⟩
  exact interval_of_scaled_cover hF0pos hh hgcdnorm hfair hmono hanti
    (fun e he => compressed_initial_interval hrmem e he) hres hpairs L

/-! ### Specialization: no frame hypothesis left open

`Short/KneserFrame.exists_frame` (read-only) enumerates exactly the minimum
representative frame `compressed_grid_bundle` needs. Specializing to it
removes `hr0`/`hr_inj`/`hrmem`/`hrA` from the hypothesis list entirely — the
only inputs left are `0 ∈ A₀` and the stabilization data itself. -/

/-- **The compressed-sequence interval-growth bundle, unconditionally.**
Same conclusion as `compressed_grid_bundle`, but with the minimum
representative frame *constructed* (via `KneserFrame.exists_frame`) rather
than assumed: the only hypotheses are `0 ∈ A₀` and the stable-gap/stable-
residue-alphabet data. -/
theorem compressed_grid_bundle_unconditional
    {A₀ B₀ : Set ℕ} (hA0 : 0 ∈ A₀)
    {N f : ℕ} (hf : 0 < f) (hstabF : ∀ n, N ≤ n → gapMin (Bseq A₀ B₀ n) = f)
    {N' : ℕ} (hNN' : N ≤ N') {R : Finset ℕ}
    (hstabR : ∀ n, N' ≤ n → residueAlphabet (Bseq A₀ B₀) f n = R) :
    ∃ (g F0 : ℕ) (G : Finset ℕ) (h : ℕ) (r : Fin h → ℕ),
      0 < g ∧ 0 < F0 ∧ (insert F0 G).gcd id = 1 ∧
      FairAbsorption (fun n => compressedSet g h r (Aseq A₀ B₀ n))
        (fun n => compressedSetZero g h (Bseq A₀ B₀ n)) ∧
      Monotone (fun n => compressedSet g h r (Aseq A₀ B₀ n)) ∧
      Antitone (fun n => compressedSetZero g h (Bseq A₀ B₀ n)) ∧
      (∀ L, ∃ j ≥ N', ∃ x, ∀ t < L, x + t ∈ compressedSet g h r (Aseq A₀ B₀ j)) := by
  set g := (insert f R).gcd id with hgdef
  have hgpos : 0 < g := hgdef ▸ stable_gcd_pos hf
  have hgdvdBN' : ∀ b ∈ Bseq A₀ B₀ N', g ∣ b :=
    hgdef ▸ stable_gcd_dvd_B_from' hf hstabR N' le_rfl
  obtain ⟨h, hh, r, hr0, hr_inj, hrmem', hrA'⟩ :=
    exists_frame A₀ B₀ g N' hgpos hA0 hgdvdBN'
  refine ⟨g, f / g, R.image (· / g), h, r, ?_⟩
  obtain ⟨hgpos', hF0pos, hgcdnorm, hfair, hmono, hanti, -, -, -, -, -, -, hinterval⟩ :=
    compressed_grid_bundle hf hstabF hNN' hstabR (g := g) (F0 := f / g) (G := R.image (· / g))
      rfl rfl rfl hh hr0 hr_inj (fun j => hrmem' j N' le_rfl) (fun a ha => hrA' N' le_rfl a ha)
  exact ⟨hgpos', hF0pos, hgcdnorm, hfair, hmono, hanti, hinterval⟩

end Erdos1112.Proof.Short
