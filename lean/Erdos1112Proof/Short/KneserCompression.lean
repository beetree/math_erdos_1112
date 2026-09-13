/-
Lane's Chapter Two, Definition 6 and Lemmas 7-9: the residue-compression
map `Λ` ("the basic map") used to rescale a pair `A, B` (`B` confined to
multiples of a modulus `g`) down to a pair on a smaller modulus `h`, the
number of residue classes mod `g` actually occurring in `A`. See
`Defs.lean` (`posCount`, `lowerDensity`, `twoFoldLowerDensity`) and
`Short/KneserDensity/README.md` for the source and page references.

Lane's setup (Definition 6): `A ⊆ J`, `g ∈ J⁺`, and
`0 = r₀ < r₁ < ⋯ < r_{h-1}` are the *smallest representatives in `A`* of the
`h` residue classes mod `g` that occur in `A`. Rather than fixing "smallest
representative" as part of any definition (that choice belongs to whoever
instantiates these lemmas from an actual `A`), every lemma below instead
takes `r : Fin h → ℕ` together with exactly the two properties of the
representatives Lane's proofs actually use:

* `hr_inj`: distinct indices give distinct residues mod `g` (this, plus
  `j < h`, is what makes the encoding below injective — Lane's remark that
  "`Λ` is one to one");
* `hA`: every element of the target set is *some* `r j + g * t`
  (Lane's standing fact that `A` is contained in the union of the residue
  classes with representatives `r j`, restated concretely with `t : ℕ`
  rather than `α ∈ I`, since every element of `A` beyond `r j` in its class
  is reached by *adding* non-negative multiples of `g`, `r j` being the
  smallest one already in `A`).

No global minimality, and in particular no bound `r j < g`, is assumed
anywhere: Lane's representatives are the smallest elements of `A` in their
residue class, not the smallest non-negative integers in that class, so
`r j` can be arbitrarily large compared to `g`. This is exactly why property
(4) of Lemma 7 needs a genuine `O(1)` error term (`Finset.sum r`, an
`x`-independent constant) while property (3) (for `B`, whose only
representative is `r₀ = 0` itself) is exact.
-/
import Mathlib
import Erdos1112Proof.Short.KneserDensity.Defs

namespace Erdos1112.Proof.Short.KneserCompression

open Erdos1112.Proof.Short.KneserDensity
open scoped Classical

/-! ### Definition 6 (p. 27): the basic map `Λ`, in coordinates

Lane's `Λ (r j + α g) = j + α h` is restated as a map out of coordinate
pairs `(j, t) : Fin h × ℕ` (`α` renamed `t` and restricted to `ℕ`, since
every occurrence in Lemmas 7-9 has `α ≥ 0`). -/

/-- The basic map `Λ`, in coordinates: `encode h j t = j + h * t`. Applying
this to a pair `(j, t)` witnessing `a = r j + g * t ∈ A` computes `Λ(a) = â`
(Definition 6, p. 27). -/
def encode (h : ℕ) (j : Fin h) (t : ℕ) : ℕ := j.val + h * t

/-- **`Λ` is one to one** (Definition 6, p. 27, second paragraph), in
coordinates: distinct pairs `(j, t)` (with `j < h` automatic from `j : Fin h`)
encode to distinct naturals. This is pure base-`h` positional arithmetic and
uses none of the representative data `r`. -/
theorem encode_injective {h : ℕ} (hh : 0 < h) :
    Function.Injective (fun p : Fin h × ℕ => encode h p.1 p.2) := by
  rintro ⟨j₁, t₁⟩ ⟨j₂, t₂⟩ heq
  simp only [encode] at heq
  have ht : t₁ = t₂ := by
    have h1 : (j₁.val + h * t₁) / h = t₁ := by
      rw [Nat.add_mul_div_left _ _ hh, Nat.div_eq_of_lt j₁.isLt, Nat.zero_add]
    have h2 : (j₂.val + h * t₂) / h = t₂ := by
      rw [Nat.add_mul_div_left _ _ hh, Nat.div_eq_of_lt j₂.isLt, Nat.zero_add]
    rw [heq] at h1
    exact h1.symm.trans h2
  have hj : j₁.val = j₂.val := by
    have h1 : (j₁.val + h * t₁) % h = j₁.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j₁.isLt]
    have h2 : (j₂.val + h * t₂) % h = j₂.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j₂.isLt]
    rw [heq] at h1
    exact h1.symm.trans h2
  exact Prod.ext (Fin.ext hj) ht

/-- **Sums preserve `j` and add `t`** (the coordinate shadow of Lemma 7,
property (5), p. 28, specialized to `x` a multiple of `g`, which is exactly
how it is used to prove property (7)): adding `h * s` to `encode h j t` is
the same as encoding `(j, t + s)`. -/
@[simp] theorem encode_add_mul (h : ℕ) (j : Fin h) (t s : ℕ) :
    encode h j (t + s) = encode h j t + h * s := by
  simp only [encode]; ring

/-! ### The compressed sets `Â`, `B̂` -/

/-- **`Â`**, i.e. `Λ(A)` (Definition 6 / Lemma 7, applied to a set `A`):
the image, under the basic map, of every element of `A` that is of the form
`r j + g * t`. -/
def compressedSet (g h : ℕ) (r : Fin h → ℕ) (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ (j : Fin h) (t : ℕ), r j + g * t ∈ A ∧ n = encode h j t}

/-- **`B̂`**, i.e. `Λ(B)` for a set `B` confined to multiples of `g` (Lemma 7,
property (1)'s proof, p. 28: `B = {g k : k ∈ K}`, `B̂ = {h k : k ∈ K}`).
Stated directly, independently of `compressedSet`, matching the fact that
`B`'s elements all lie in the `j = 0` residue class with representative
`r₀ = 0`, so no representative system for `B` itself is needed. -/
def compressedSetZero (g h : ℕ) (B : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ t : ℕ, g * t ∈ B ∧ n = h * t}

theorem mem_compressedSet {g h : ℕ} {r : Fin h → ℕ} {A : Set ℕ} {n : ℕ} :
    n ∈ compressedSet g h r A ↔ ∃ j t, r j + g * t ∈ A ∧ n = encode h j t := Iff.rfl

theorem mem_compressedSetZero {g h : ℕ} {B : Set ℕ} {n : ℕ} :
    n ∈ compressedSetZero g h B ↔ ∃ t, g * t ∈ B ∧ n = h * t := Iff.rfl

/-! ### Lemma 7, property (7) (p. 28): `Λ(A + B) = Λ(A) + Λ(B)`

Lane derives this from property (5) (`Λ(a + x) = Λ(a) + Λ(x)` for `a ∈ A`
and `x ≡ 0 mod g`) applied to `x = b ∈ B`. The proof below is a direct
computation with `encode_add_mul` playing the role of property (5), plus
`hr_inj` to identify, on the `⊆` side, *which* residue class an element of
`A + B` came from in `A`. -/

open scoped Pointwise in
/-- **`Â + B̂ = (A+B)^`** (Lemma 7, property (7), p. 28), for the compressed
sets defined above: this needs `g > 0`, distinct residues (`hr_inj`), and
that every element of `A` (not of `B`: `B`'s elements are handled directly by
`hB`, needing no representative system of their own) is covered by the
representative system `r`. -/
theorem compressedSet_add {g h : ℕ} (hg : 0 < g) {r : Fin h → ℕ}
    (hr_inj : Function.Injective fun j : Fin h => r j % g)
    {A B : Set ℕ} (hA : ∀ a ∈ A, ∃ j t, a = r j + g * t) (hB : ∀ b ∈ B, ∃ t, b = g * t) :
    compressedSet g h r (A + B) = compressedSet g h r A + compressedSetZero g h B := by
  ext n
  simp only [mem_compressedSet, mem_compressedSetZero, Set.mem_add]
  constructor
  · rintro ⟨j, t, hmem, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hmem
    obtain ⟨j', t', ha'⟩ := hA a ha
    obtain ⟨s, hbs⟩ := hB b hb
    -- from `a + b = r j + g t`, `a = r j' + g t'`, `b = g s`, identify `j' = j`
    have heq : r j' + g * (t' + s) = r j + g * t := by
      rw [mul_add, ← add_assoc, ← ha', ← hbs]
      exact hab
    have hmod : r j' % g = r j % g := by
      have := congrArg (· % g) heq
      simpa [Nat.add_mul_mod_self_left] using this
    have hjj' : j' = j := hr_inj hmod
    subst hjj'
    have ht : t' + s = t := by
      have hcancel : g * (t' + s) = g * t := by
        have := heq
        omega
      exact Nat.eq_of_mul_eq_mul_left hg hcancel
    refine ⟨encode h j' t', ⟨j', t', ha'.symm ▸ ha, rfl⟩, h * s, ⟨s, hbs.symm ▸ hb, rfl⟩, ?_⟩
    rw [← encode_add_mul, ht]
  · rintro ⟨_, ⟨j, t, hmemA, rfl⟩, _, ⟨s, hmemB, rfl⟩, rfl⟩
    refine ⟨j, t + s, ⟨r j + g * t, hmemA, g * s, hmemB, by ring⟩, ?_⟩
    rw [encode_add_mul]

/-! ### Lemma 7, property (3) (p. 28): `B(xg) = B̂(xh)`, exactly

`B`'s only representative is `r₀ = 0` itself, so (unlike `A`, see below) there
is no boundary effect at all: both counts reduce to counting the *same*
index set `{t ∈ [1,x] : g t ∈ B}`, once via the injective map `t ↦ g * t`
and once via `t ↦ h * t`. -/

private theorem compressedSetZero_inter_Icc {g h : ℕ} (hh : 0 < h)
    (B : Set ℕ) (x : ℕ) :
    compressedSetZero g h B ∩ Set.Icc 1 (x * h) =
      (fun t : ℕ => h * t) '' (Set.Icc 1 x ∩ {t : ℕ | g * t ∈ B}) := by
  ext n
  simp only [compressedSetZero, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_image]
  constructor
  · rintro ⟨⟨t, htB, rfl⟩, h1, h2⟩
    have ht0 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · simp at h1
      · exact ht0
    have htx : t ≤ x := by
      have h2' : h * t ≤ h * x := by rw [mul_comm h x]; exact h2
      exact Nat.le_of_mul_le_mul_left h2' hh
    exact ⟨t, ⟨⟨ht0, htx⟩, htB⟩, rfl⟩
  · rintro ⟨t, ⟨⟨ht1, htx⟩, htB⟩, rfl⟩
    refine ⟨⟨t, htB, rfl⟩, ?_, ?_⟩
    · calc 1 ≤ h * 1 := by omega
      _ ≤ h * t := Nat.mul_le_mul_left h ht1
    · calc h * t ≤ h * x := Nat.mul_le_mul_left h htx
      _ = x * h := mul_comm h x

private theorem B_inter_Icc {g : ℕ} (hg : 0 < g) {B : Set ℕ} (hB : ∀ b ∈ B, ∃ t, b = g * t)
    (x : ℕ) :
    B ∩ Set.Icc 1 (x * g) = (fun t : ℕ => g * t) '' (Set.Icc 1 x ∩ {t : ℕ | g * t ∈ B}) := by
  ext n
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_image]
  constructor
  · rintro ⟨hnB, h1, h2⟩
    obtain ⟨t, rfl⟩ := hB n hnB
    have ht0 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · simp at h1
      · exact ht0
    have htx : t ≤ x := by
      have h2' : g * t ≤ g * x := by rw [mul_comm g x]; exact h2
      exact Nat.le_of_mul_le_mul_left h2' hg
    exact ⟨t, ⟨⟨ht0, htx⟩, hnB⟩, rfl⟩
  · rintro ⟨t, ⟨⟨ht1, htx⟩, htB⟩, rfl⟩
    refine ⟨htB, ?_, ?_⟩
    · calc 1 ≤ g * 1 := by omega
      _ ≤ g * t := Nat.mul_le_mul_left g ht1
    · calc g * t ≤ g * x := Nat.mul_le_mul_left g htx
      _ = x * g := mul_comm g x

/-- **`B(xg) = B̂(xh)`, exactly** (Lemma 7, property (3), p. 28): counting
`B` up to `xg` and counting its compression up to `xh` agree on the nose, no
error term. -/
theorem posCount_compressedSetZero {g h : ℕ} (hg : 0 < g) (hh : 0 < h) {B : Set ℕ}
    (hB : ∀ b ∈ B, ∃ t, b = g * t) (x : ℕ) :
    posCount (compressedSetZero g h B) (x * h) = posCount B (x * g) := by
  unfold posCount
  rw [compressedSetZero_inter_Icc hh B x, B_inter_Icc hg hB x,
    Set.ncard_image_of_injective _ (fun a b (hab : h * a = h * b) => Nat.eq_of_mul_eq_mul_left hh hab),
    Set.ncard_image_of_injective _ (fun a b (hab : g * a = g * b) => Nat.eq_of_mul_eq_mul_left hg hab)]

/-! ### Lemma 7, property (4) (p. 28-29): `A(xg) = Â(xh) + O(1)`

Unlike `B`, `A`'s representatives `r j` need not be `< g` (Lane's `r j` is
the *smallest element of `A`* in its residue class, not the smallest
non-negative integer in that class), so the `t`-range reaching `x * g` in
`A`'s class `j` depends on `r j`, while the `t`-range reaching `x * h` under
`Λ` does not (it is exactly `t < x`, or `1 ≤ t ≤ x` for `j = 0`, regardless
of `r j`). Both directions below are proved by an explicit injection between
the relevant `posCount` index sets, using `Set.ncard_le_ncard_of_injOn`. -/

/-- The arithmetic core of property (4): given `r j + g * t` lands in
`(0, x * g]`, its image `encode h j t` lands in `(0, x * h]`. This needs
`hr0`/`hr_inj` only for the boundary case `t = x`, where `r j + g * t ≤ x * g`
forces `r j = 0`, hence (by distinctness of residues) `j = ⟨0, hh⟩`. -/
private theorem encode_mem_Icc {g h x : ℕ} (hg : 0 < g) (hh : 0 < h) {r : Fin h → ℕ}
    (hr0 : r ⟨0, hh⟩ = 0) (hr_inj : Function.Injective fun j : Fin h => r j % g)
    {j : Fin h} {t : ℕ} (ha1 : 1 ≤ r j + g * t) (ha2 : r j + g * t ≤ x * g) :
    1 ≤ encode h j t ∧ encode h j t ≤ x * h := by
  constructor
  · rcases Nat.eq_zero_or_pos (encode h j t) with hz | hpos
    · exfalso
      simp only [encode] at hz
      have hjz : j.val = 0 := by omega
      have htz : t = 0 := by
        rcases Nat.mul_eq_zero.mp (show h * t = 0 by omega) with h0 | t0
        · omega
        · exact t0
      have hjeq : j = ⟨0, hh⟩ := Fin.ext hjz
      rw [hjeq, hr0, htz, mul_zero, add_zero] at ha1
      omega
    · exact hpos
  · have htx : t ≤ x := by
      have hgtx : g * t ≤ g * x := by
        have h5 : g * t ≤ x * g := by omega
        rwa [mul_comm x g] at h5
      exact Nat.le_of_mul_le_mul_left hgtx hg
    rcases lt_or_eq_of_le htx with htlt | hteq
    · have h1 : h * t ≤ h * (x - 1) := Nat.mul_le_mul_left h (by omega)
      have h2 : h * (x - 1) + h = h * x := by
        have hx1 : x - 1 + 1 = x := by omega
        calc h * (x - 1) + h = h * (x - 1 + 1) := by ring
          _ = h * x := by rw [hx1]
      have h3 : j.val < h := j.isLt
      have h4 : x * h = h * x := mul_comm x h
      simp only [encode]
      omega
    · have hrj0 : r j = 0 := by
        rw [hteq] at ha2
        have h5 : x * g = g * x := mul_comm x g
        omega
      have hmod : (fun j : Fin h => r j % g) j = (fun j : Fin h => r j % g) ⟨0, hh⟩ := by
        simp [hrj0, hr0]
      have hjeq : j = ⟨0, hh⟩ := hr_inj hmod
      have hj0 : j.val = 0 := by rw [hjeq]
      simp only [encode, hj0, hteq, zero_add]
      exact le_of_eq (mul_comm h x)

/-- **`A(xg) ≤ Â(xh)`** (half of Lemma 7, property (4), p. 28-29): the
compressed count never *undercounts* `A`. -/
theorem posCount_compressedSet_ge {g h : ℕ} (hg : 0 < g) (hh : 0 < h) {r : Fin h → ℕ}
    (hr0 : r ⟨0, hh⟩ = 0) (hr_inj : Function.Injective fun j : Fin h => r j % g)
    {A : Set ℕ} (hA : ∀ a ∈ A, ∃ j t, a = r j + g * t) (x : ℕ) :
    posCount A (x * g) ≤ posCount (compressedSet g h r A) (x * h) := by
  classical
  unfold posCount
  refine Set.ncard_le_ncard_of_injOn
    (fun a => if ha : a ∈ A then
        encode h (hA a ha).choose (hA a ha).choose_spec.choose else 0)
    ?_ ?_ ((Set.finite_Icc 1 (x * h)).inter_of_right _)
  · rintro a ⟨haA, ha1, ha2⟩
    simp only [Set.mem_Icc, Set.mem_inter_iff, dif_pos haA]
    set j := (hA a haA).choose with hjdef
    set t := (hA a haA).choose_spec.choose with htdef
    have hjt : a = r j + g * t := (hA a haA).choose_spec.choose_spec
    have ha1' : 1 ≤ r j + g * t := hjt ▸ ha1
    have ha2' : r j + g * t ≤ x * g := hjt ▸ ha2
    exact ⟨⟨j, t, hjt ▸ haA, rfl⟩, encode_mem_Icc hg hh hr0 hr_inj ha1' ha2'⟩
  · rintro a ⟨haA, -, -⟩ b ⟨hbA, -, -⟩ hab
    simp only [dif_pos haA, dif_pos hbA] at hab
    set j₁ := (hA a haA).choose with hj1def
    set t₁ := (hA a haA).choose_spec.choose with ht1def
    have ha' : a = r j₁ + g * t₁ := (hA a haA).choose_spec.choose_spec
    set j₂ := (hA b hbA).choose with hj2def
    set t₂ := (hA b hbA).choose_spec.choose with ht2def
    have hb' : b = r j₂ + g * t₂ := (hA b hbA).choose_spec.choose_spec
    have hpair : (j₁, t₁) = (j₂, t₂) := encode_injective hh hab
    rw [ha', hb', (Prod.mk.injEq ..).mp hpair |>.1, (Prod.mk.injEq ..).mp hpair |>.2]

/-- Arithmetic core of the reverse bound: given `encode h j t` lands in
`(0, x * h]`, the corresponding `r j + g * t` lands in `(0, x * g + ∑ r]`.
This is the converse of `encode_mem_Icc`, and is where `∑ⱼ r j` genuinely
enters: the compressed window for class `j` is `t < x` regardless of `r j`,
so `r j + g * t` can overshoot `x * g` by as much as `r j`. -/
private theorem A_mem_Icc {g h x : ℕ} (hg : 0 < g) (hh : 0 < h) {r : Fin h → ℕ}
    (hr0 : r ⟨0, hh⟩ = 0) (hr_inj : Function.Injective fun j : Fin h => r j % g)
    {j : Fin h} {t : ℕ} (hn1 : 1 ≤ encode h j t) (hn2 : encode h j t ≤ x * h) :
    1 ≤ r j + g * t ∧ r j + g * t ≤ x * g + ∑ k : Fin h, r k := by
  constructor
  · rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · subst ht0
      have hj1 : 1 ≤ j.val := by simpa [encode] using hn1
      have hjne : j ≠ ⟨0, hh⟩ := by rintro rfl; simp at hj1
      have hrjne : r j ≠ 0 := by
        intro hrj0
        apply hjne
        have hmod : (fun j : Fin h => r j % g) j = (fun j : Fin h => r j % g) ⟨0, hh⟩ := by
          simp [hrj0, hr0]
        exact hr_inj hmod
      omega
    · have h9 : 1 ≤ g * t := by
        calc 1 ≤ g * 1 := by omega
          _ ≤ g * t := Nat.mul_le_mul_left g htpos
      omega
  · have htx : t ≤ x := by
      simp only [encode] at hn2
      have h6 : h * t ≤ h * x := by
        have h7 : x * h = h * x := mul_comm x h
        omega
      exact Nat.le_of_mul_le_mul_left h6 hh
    have hgtx : g * t ≤ g * x := Nat.mul_le_mul_left g htx
    have hrjC : r j ≤ ∑ k : Fin h, r k :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    have h8 : x * g = g * x := mul_comm x g
    omega

/-- The choice function underlying the reverse injection: for `n` in the
compressed set, pick the (unique, by `hr_inj`) witnessing `A`-element. -/
private noncomputable def toA (g : ℕ) {h : ℕ} (r : Fin h → ℕ) (A : Set ℕ) (n : ℕ) : ℕ :=
  if hn : n ∈ compressedSet g h r A then r hn.choose + g * hn.choose_spec.choose else 0

private theorem toA_spec {g h : ℕ} {r : Fin h → ℕ} {A : Set ℕ} {n : ℕ}
    (hn : n ∈ compressedSet g h r A) :
    ∃ j t, n = encode h j t ∧ r j + g * t ∈ A ∧ toA g r A n = r j + g * t := by
  refine ⟨hn.choose, hn.choose_spec.choose, hn.choose_spec.choose_spec.2,
    hn.choose_spec.choose_spec.1, ?_⟩
  unfold toA
  rw [dif_pos hn]

/-- **`Â(xh) ≤ A(xg) + ∑ⱼ r j`** (the other half of Lemma 7, property (4)):
the compressed count never *overcounts* `A` by more than the `x`-independent
constant `∑ⱼ r j`. This is where the genuine `O(1)` error lives: a pair
`(j, t)` in the compressed window (`t < x`, independent of `r j`) can encode
an element `r j + g * t` of `A` that overshoots `x * g` by as much as `r j`. -/
theorem posCount_compressedSet_le_add {g h : ℕ} (hg : 0 < g) (hh : 0 < h) {r : Fin h → ℕ}
    (hr0 : r ⟨0, hh⟩ = 0) (hr_inj : Function.Injective fun j : Fin h => r j % g)
    -- `hA` (`A`'s covering by `r`) is not needed for *this* direction (only
    -- membership of the specific witnessing element in `A`, which
    -- `compressedSet`'s own definition already supplies); kept as a
    -- hypothesis anyway so this lemma's signature matches
    -- `posCount_compressedSet_ge`'s, for a single combined `O(1)` statement.
    {A : Set ℕ} (_hA : ∀ a ∈ A, ∃ j t, a = r j + g * t) (x : ℕ) :
    posCount (compressedSet g h r A) (x * h) ≤ posCount A (x * g) + ∑ j : Fin h, r j := by
  classical
  set C : ℕ := ∑ j : Fin h, r j with hCdef
  have hposCountAC : posCount A (x * g + C) ≤ posCount A (x * g) + C := by
    rw [posCount_window_add A (Nat.le_add_right (x * g) C)]
    gcongr
    calc (A ∩ Set.Icc (x * g + 1) (x * g + C)).ncard
        ≤ (Set.Icc (x * g + 1) (x * g + C)).ncard :=
          Set.ncard_le_ncard Set.inter_subset_right (Set.finite_Icc _ _)
      _ = (Finset.Icc (x * g + 1) (x * g + C)).card := by
          rw [← Finset.coe_Icc, Set.ncard_coe_finset]
      _ = C := by rw [Nat.card_Icc]; omega
  refine le_trans ?_ hposCountAC
  unfold posCount
  refine Set.ncard_le_ncard_of_injOn (toA g r A)
    ?_ ?_ ((Set.finite_Icc 1 (x * g + C)).inter_of_right _)
  · rintro n ⟨hnC, hn1, hn2⟩
    obtain ⟨j, t, hn', hmemA, hfeq⟩ := toA_spec hnC
    rw [Set.mem_inter_iff, Set.mem_Icc]
    rw [hfeq]
    have hn1' : 1 ≤ encode h j t := hn' ▸ hn1
    have hn2' : encode h j t ≤ x * h := hn' ▸ hn2
    have hb := A_mem_Icc hg hh hr0 hr_inj hn1' hn2'
    exact ⟨hmemA, hb.1, hb.2⟩
  · rintro n₁ ⟨hn₁C, -, -⟩ n₂ ⟨hn₂C, -, -⟩ heq
    obtain ⟨j₁, t₁, hn₁', hmemA₁, hfeq₁⟩ := toA_spec hn₁C
    obtain ⟨j₂, t₂, hn₂', hmemA₂, hfeq₂⟩ := toA_spec hn₂C
    rw [hfeq₁, hfeq₂] at heq
    have hmod : (fun j : Fin h => r j % g) j₁ = (fun j : Fin h => r j % g) j₂ := by
      have := congrArg (· % g) heq
      simpa [Nat.add_mul_mod_self_left] using this
    have hjj : j₁ = j₂ := hr_inj hmod
    subst hjj
    have htt : t₁ = t₂ := Nat.eq_of_mul_eq_mul_left hg (by omega)
    rw [hn₁', hn₂', htt]

/-- **`A(xg) = Â(xh) + O(1)`** (Lemma 7, property (4), p. 28-29), packaged as
a single `x`-independent-constant statement: the constant `∑ⱼ r j` works
uniformly in `x`. Contrast `posCount_compressedSetZero` above, where the
analogous constant for `B` is exactly `0`. -/
theorem posCount_compressedSet_eq_add_O1 {g h : ℕ} (hg : 0 < g) (hh : 0 < h) {r : Fin h → ℕ}
    (hr0 : r ⟨0, hh⟩ = 0) (hr_inj : Function.Injective fun j : Fin h => r j % g)
    {A : Set ℕ} (hA : ∀ a ∈ A, ∃ j t, a = r j + g * t) :
    ∃ C : ℕ, ∀ x, posCount A (x * g) ≤ posCount (compressedSet g h r A) (x * h) ∧
      posCount (compressedSet g h r A) (x * h) ≤ posCount A (x * g) + C :=
  ⟨∑ j : Fin h, r j, fun x =>
    ⟨posCount_compressedSet_ge hg hh hr0 hr_inj hA x,
      posCount_compressedSet_le_add hg hh hr0 hr_inj hA x⟩⟩

end Erdos1112.Proof.Short.KneserCompression
