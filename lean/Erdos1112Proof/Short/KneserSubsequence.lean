/-
Lane's Lemma 8: `δ(A)` and `δ(A,B)` can be computed along the arithmetic
subsequence `n = x·g` alone, for any fixed `g > 0`. See
`Short/KneserDensity/README.md` for the source and page references. Used
by `Short/KneserDensityScaling.lean`'s rescaling argument (Lemma 9), which
reindexes a `liminf` from `x·g` to `x·h`.

`n = 0` is handled uniformly by the same argument (no special case):
`posCount _ 0 = 0` and the error bound is proved for *all* `n`, not merely
eventually.
-/
import Mathlib
import Erdos1112Proof.Short.KneserDensity.Defs

namespace Erdos1112.Proof.Short

open Erdos1112.Proof.Short.KneserDensity
open Filter

/-! ### The generic count lemma

Both `posCount A` and `n ↦ posCount A n + posCount B n` are monotone,
`≤ C * n` for a suitable constant `C`, and have `C`-Lipschitz window growth
(`f y - f x ≤ C * (y - x)`). That is all Lane's sandwich argument uses, so
we prove it once for an abstract `f : ℕ → ℕ` and instantiate it twice. -/

/-- **The generic arithmetic-subsequence liminf lemma.** For `f : ℕ → ℕ`
monotone, `C`-bounded (`f n ≤ C * n`) and `C`-Lipschitz on windows
(`f y - f x ≤ C * (y - x)` for `x ≤ y`), `liminf (f n / n)` over *all* `n`
equals `liminf (f (x*g) / (x*g))` over the subsequence `x*g`, `g > 0`.

Proof: (1) replace `n` by `m n := (n / g) * g` (the largest multiple of `g`
at most `n`); the two ratios differ by an explicit `O(1/n)` correction
term, handled by `liminf_add_of_tendsto_zero`. (2) `f (m n) / m n` is
literally `(f (· * g) / (· * g)) ∘ (· / g)`, and `Nat`'s
`map_div_atTop_eq_nat` gives `map (· / g) atTop = atTop` exactly (`· / g`
is onto every tail, not merely cofinal), so `liminf_comp` identifies the
two liminfs on the nose — no `ε`-argument needed for this half. -/
theorem liminf_div_eq_liminf_along_mul (f : ℕ → ℕ) {g C : ℕ} (hg : 0 < g)
    (hmono : Monotone f) (hwin : ∀ {x y : ℕ}, x ≤ y → f y - f x ≤ C * (y - x))
    (hbound : ∀ n, f n ≤ C * n) :
    liminf (fun n : ℕ => (f n : ℝ) / n) atTop =
      liminf (fun x : ℕ => (f (x * g) : ℝ) / (x * g)) atTop := by
  set m : ℕ → ℕ := fun n => (n / g) * g with hmdef
  have hmle : ∀ n, m n ≤ n := fun n => Nat.div_mul_le_self n g
  have hnm : ∀ n, n - m n < g := by
    intro n
    have hdm : n / g * g + n % g = n := by rw [mul_comm]; exact Nat.div_add_mod n g
    have hlt := Nat.mod_lt n hg
    simp only [hmdef]
    omega
  -- Step 1: `f n / n` and `f (m n) / m n` differ by a term → 0.
  have hstep1 : liminf (fun n : ℕ => (f n : ℝ) / n) atTop =
      liminf (fun n : ℕ => (f (m n) : ℝ) / m n) atTop := by
    have hterm1 : Tendsto (fun n : ℕ => ((f n : ℝ) - f (m n)) / n) atTop (nhds 0) := by
      apply tendsto_bounded_div_atTop_nhds_zero (M := (C * g : ℝ))
      filter_upwards [eventually_ge_atTop g] with n hn
      have hle : f (m n) ≤ f n := hmono (hmle n)
      have hb : f n - f (m n) ≤ C * g :=
        le_trans (hwin (hmle n)) (Nat.mul_le_mul_left C (hnm n).le)
      have hcast : (f n : ℝ) - f (m n) = ((f n - f (m n) : ℕ) : ℝ) := by
        rw [Nat.cast_sub hle]
      rw [hcast, abs_of_nonneg (by positivity)]
      exact_mod_cast hb
    have hterm2 : Tendsto (fun n : ℕ => (f (m n) : ℝ) / n - (f (m n) : ℝ) / m n)
        atTop (nhds 0) := by
      have hgdiv : Tendsto (fun n : ℕ => (C * g : ℝ) / n) atTop (nhds 0) :=
        tendsto_bounded_div_atTop_nhds_zero (u := fun _ => (C * g : ℝ)) (M := C * g)
          (Filter.Eventually.of_forall fun _ => le_of_eq (abs_of_nonneg (by positivity)))
      apply squeeze_zero_norm' (a := fun n : ℕ => (C * g : ℝ) / n)
      · filter_upwards [eventually_ge_atTop g] with n hn
        have hnpos0 : 0 < n := by omega
        have hmpos : 0 < m n := by
          have h1 : 1 ≤ n / g := (Nat.le_div_iff_mul_le hg).mpr (by omega)
          simp only [hmdef]; positivity
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hnpos0
        have hmposR : (0 : ℝ) < (m n : ℝ) := by exact_mod_cast hmpos
        have hub : (f (m n) : ℝ) / n ≤ (f (m n) : ℝ) / m n :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) hmposR (by exact_mod_cast hmle n)
        have hfm : (f (m n) : ℝ) ≤ C * m n := by exact_mod_cast hbound (m n)
        have hnm' : (n : ℝ) - m n ≤ g := by
          have h1 : (n - m n : ℕ) < g := hnm n
          have h2 : ((n - m n : ℕ) : ℝ) = (n : ℝ) - m n := by rw [Nat.cast_sub (hmle n)]
          have h3 : ((n - m n : ℕ) : ℝ) ≤ g := by exact_mod_cast h1.le
          linarith [h2 ▸ h3]
        have hlb2 : (f (m n) : ℝ) / m n ≤ (f (m n) : ℝ) / n + (C * g : ℝ) / n := by
          have hmnle : (m n : ℝ) ≤ n := by exact_mod_cast hmle n
          have hcross : (f (m n) : ℝ) * n ≤ ((f (m n) : ℝ) + C * g) * m n := by
            nlinarith [mul_le_mul hfm hnm' (by linarith) (by positivity : (0:ℝ) ≤ (C:ℝ) * m n)]
          have h := (div_le_div_iff₀ hmposR hnpos).mpr hcross
          calc (f (m n) : ℝ) / m n ≤ ((f (m n) : ℝ) + C * g) / n := h
            _ = (f (m n) : ℝ) / n + (C * g : ℝ) / n := by rw [add_div]
        rw [Real.norm_eq_abs, abs_le]
        refine ⟨by linarith, ?_⟩
        have hcg : (0:ℝ) ≤ (C * g : ℝ) / n := by positivity
        linarith
      · exact hgdiv
    have hD : Tendsto (fun n : ℕ => (f n : ℝ) / n - (f (m n) : ℝ) / m n) atTop (nhds 0) := by
      have heq : (fun n : ℕ => (f n : ℝ) / n - (f (m n) : ℝ) / m n) =
          fun n : ℕ => ((f n : ℝ) - f (m n)) / n + ((f (m n) : ℝ) / n - (f (m n) : ℝ) / m n) := by
        funext n; ring
      rw [heq]
      simpa using hterm1.add hterm2
    have hub : atTop.IsBoundedUnder (· ≥ ·) (fun n : ℕ => (f (m n) : ℝ) / m n) :=
      ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun n => by positivity)⟩
    have hub2 : atTop.IsBoundedUnder (· ≤ ·) (fun n : ℕ => (f (m n) : ℝ) / m n) := by
      refine ⟨C, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun n => ?_)⟩
      rcases Nat.eq_zero_or_pos (m n) with hz | hz
      · simp [hz]
      · rw [div_le_iff₀ (by exact_mod_cast hz : (0:ℝ) < m n)]
        exact_mod_cast hbound (m n)
    have hsplit : (fun n : ℕ => (f n : ℝ) / n) =
        (fun n : ℕ => (f (m n) : ℝ) / m n) +
          fun n : ℕ => ((f n : ℝ) / n - (f (m n) : ℝ) / m n) := by
      funext n; simp only [Pi.add_apply]; ring
    rw [hsplit]
    exact liminf_add_of_tendsto_zero hub hub2 hD
  -- Step 2: `f (m n) / m n` is `(f (·*g)/(·*g)) ∘ (·/g)`; `·/g` maps `atTop` onto `atTop`.
  have hstep2 : liminf (fun n : ℕ => (f (m n) : ℝ) / m n) atTop =
      liminf (fun x : ℕ => (f (x * g) : ℝ) / (x * g)) atTop := by
    have hcomp : (fun n : ℕ => (f (m n) : ℝ) / m n) =
        (fun x : ℕ => (f (x * g) : ℝ) / (x * g)) ∘ (fun n : ℕ => n / g) := by
      funext n
      simp only [Function.comp, hmdef]
      push_cast
      ring_nf
    rw [hcomp, liminf_comp, map_div_atTop_eq_nat g hg]
  rw [hstep1, hstep2]

/-! ### The two instantiations -/

/-- **Lane's Lemma 8, single-set form.** -/
theorem lowerDensity_eq_liminf_along_mul (A : Set ℕ) {g : ℕ} (hg : 0 < g) :
    lowerDensity A = liminf (fun x : ℕ => (posCount A (x * g) : ℝ) / (x * g)) atTop := by
  unfold lowerDensity
  exact liminf_div_eq_liminf_along_mul (posCount A) (C := 1) hg
    (fun _ _ h => posCount_mono_arg A h)
    (fun h => by simpa using posCount_window_le A h)
    (fun n => by simpa using posCount_le_self A n)

/-- **Lane's Lemma 8, two-fold form.** -/
theorem twoFoldLowerDensity_eq_liminf_along_mul (A B : Set ℕ) {g : ℕ} (hg : 0 < g) :
    twoFoldLowerDensity A B =
      liminf (fun x : ℕ => ((posCount A (x * g) : ℝ) + posCount B (x * g)) / (x * g)) atTop := by
  have hkey := liminf_div_eq_liminf_along_mul (fun n => posCount A n + posCount B n) (C := 2) hg
    (fun x y h => Nat.add_le_add (posCount_mono_arg A h) (posCount_mono_arg B h))
    (fun {x y} h => by
      dsimp only
      have h1 := posCount_window_le A h
      have h2 := posCount_window_le B h
      have h3 : posCount A x ≤ posCount A y := posCount_mono_arg A h
      have h4 : posCount B x ≤ posCount B y := posCount_mono_arg B h
      omega)
    (fun n => by
      dsimp only
      have h1 := posCount_le_self A n
      have h2 := posCount_le_self B n
      omega)
  unfold twoFoldLowerDensity
  have hcast : ∀ n : ℕ,
      (((fun n => posCount A n + posCount B n) n : ℕ) : ℝ) = (posCount A n : ℝ) + posCount B n :=
    fun n => by dsimp only; push_cast; ring
  simpa only [hcast] using hkey

end Erdos1112.Proof.Short
