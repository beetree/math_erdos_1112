/- The recurring two-letter case with zero lower zero-frequency. Periodicity or eventual balance would force positive zero-frequency; the resulting pair widths feed the sweep in Short/BinaryCore. -/
import Erdos1112Proof.Short.BinaryCore

namespace Erdos1112.Proof.Short

open Erdos1112.Proof

/-! ### Windowed counting

`onesCount h m n` counts `h`-true values in the window `h (m+1), …, h (m+n)`;
`zerosCount h m n := n - onesCount h m n` counts the complements. These are
`qCount`'s shifted/windowed cousins, needed to turn "the tail is balanced"
into a lower bound on the zero-frequency. -/

/-- Ones (`h = true`) count in the length-`n` window right after position
`m` (positions `m+1, …, m+n`). -/
def onesCount (h : ℕ → Bool) (m n : ℕ) : ℕ :=
  (Finset.range n).sum fun i => if h (m + i + 1) then 1 else 0

/-- Zeros (`h = false`) count in the same window. -/
def zerosCount (h : ℕ → Bool) (m n : ℕ) : ℕ := n - onesCount h m n

lemma onesCount_one (h : ℕ → Bool) (m : ℕ) :
    onesCount h m 1 = if h (m + 1) then 1 else 0 := by
  unfold onesCount
  rw [Finset.sum_range_one]

lemma onesCount_le (h : ℕ → Bool) (m n : ℕ) : onesCount h m n ≤ n := by
  calc onesCount h m n ≤ ∑ _i ∈ Finset.range n, 1 :=
        Finset.sum_le_sum fun i _ => by split <;> omega
    _ = n := by simp

/-- The windowed identity: `qCount` over `m+n` splits as `qCount` over `m`
plus the window count. -/
lemma qCount_add (h : ℕ → Bool) (m n : ℕ) :
    qCount h (m + n) = qCount h m + onesCount h m n := by
  induction n with
  | zero => simp [onesCount]
  | succ n ih =>
      have e1 : m + (n + 1) = (m + n) + 1 := by omega
      have e2 : onesCount h m (n + 1) = onesCount h m n + (if h (m + n + 1) then 1 else 0) :=
        Finset.sum_range_succ _ n
      rw [e1, qCount_succ, ih, e2]
      omega

lemma onesCount_add (h : ℕ → Bool) (m n1 n2 : ℕ) :
    onesCount h m (n1 + n2) = onesCount h m n1 + onesCount h (m + n1) n2 := by
  have e1 := qCount_add h m (n1 + n2)
  have e2 := qCount_add h m n1
  have e3 := qCount_add h (m + n1) n2
  have e4 : m + n1 + n2 = m + (n1 + n2) := by omega
  rw [e4] at e3
  omega

lemma zerosCount_add (h : ℕ → Bool) (m n1 n2 : ℕ) :
    zerosCount h m (n1 + n2) = zerosCount h m n1 + zerosCount h (m + n1) n2 := by
  unfold zerosCount
  have h1 := onesCount_add h m n1 n2
  have h2 := onesCount_le h m n1
  have h3 := onesCount_le h (m + n1) n2
  omega

lemma zerosCount_mono {h : ℕ → Bool} {m n1 n2 : ℕ} (hn : n1 ≤ n2) :
    zerosCount h m n1 ≤ zerosCount h m n2 := by
  have e : n2 = n1 + (n2 - n1) := by omega
  rw [e, zerosCount_add]
  omega

lemma zerosCount_false {h : ℕ → Bool} {m : ℕ} (hz : h (m + 1) = false) :
    1 ≤ zerosCount h m 1 := by
  have h0 : onesCount h m 1 = 0 := by rw [onesCount_one, hz]; simp
  unfold zerosCount
  omega

/-- Summing `r` consecutive length-`L` windows, each with a zero, gives at
least `r` zeros over the concatenated window. -/
lemma zerosCount_sum_ge {h : ℕ → Bool} {m L : ℕ}
    (hwin : ∀ i, 1 ≤ zerosCount h (m + i * L) L) :
    ∀ r, r ≤ zerosCount h m (r * L) := by
  intro r
  induction r with
  | zero => exact Nat.zero_le _
  | succ r ih =>
      have e1 : (r + 1) * L = r * L + L := by ring
      rw [e1, zerosCount_add]
      have := hwin r
      omega

/-- Exact decomposition of the global zero-count `n - qCount h n` at a base
point `m ≤ n`. -/
lemma z_eq (h : ℕ → Bool) {m n : ℕ} (hmn : m ≤ n) :
    n - qCount h n = (m - qCount h m) + zerosCount h m (n - m) := by
  unfold zerosCount
  have e1 := qCount_add h m (n - m)
  have e2 : m + (n - m) = n := by omega
  rw [e2] at e1
  have hb1 := onesCount_le h m (n - m)
  have hb2 := qCount_le h m
  omega

/-! ### Density-free hypotheses -/

/-- The letter `false` ("zero") recurs infinitely often. -/
def ZeroRecurs (h : ℕ → Bool) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ h (n + 1) = false

/-- `liminf z_n / n = 0` where `z_n = n - qCount h n` counts zeros: for
every rate `L`, arbitrarily large `n` have zero-frequency below `1/L`. -/
def ZeroFreqLiminfZero (h : ℕ → Bool) : Prop :=
  ∀ L, 0 < L → ∀ N, ∃ n, N ≤ n ∧ (n - qCount h n) * L < n

/-- If a lower bound `n ≤ z_n·L + C` holds on a tail, it contradicts
`ZeroFreqLiminfZero` (choosing the rate `L+1`, finer than `L`, at a large
enough `n`). -/
lemma false_of_density_lower_bound {h : ℕ → Bool} (hlim : ZeroFreqLiminfZero h)
    {L C Base : ℕ} (hL : 0 < L)
    (hbound : ∀ n, Base ≤ n → n ≤ (n - qCount h n) * L + C) : False := by
  obtain ⟨n, hnN, hn⟩ := hlim (L + 1) (by omega) (C * L + C + 1 + Base)
  have hb := hbound n (by omega)
  set z := n - qCount h n with hzdef
  have e1 : z * (L + 1) = z * L + z := by ring
  rw [e1] at hn
  have hzC : z + 1 ≤ C := by omega
  have hmul : (z + 1) * L ≤ C * L := Nat.mul_le_mul_right L hzC
  have e2 : (z + 1) * L = z * L + L := by ring
  rw [e2] at hmul
  omega

/-- If every length-`L` window starting at `m0 + i·L` has a zero, the
zero-count grows at rate at least `1/L` from `m0` on. -/
lemma density_ge_of_periodic_zero {h : ℕ → Bool} {m0 L : ℕ} (hL : 0 < L)
    (hwin : ∀ i, 1 ≤ zerosCount h (m0 + i * L) L) :
    ∀ n, m0 ≤ n → n ≤ (n - qCount h n) * L + (m0 + L) := by
  intro n hmn
  have hz := z_eq h hmn
  have hsum := zerosCount_sum_ge hwin
  have hdm := Nat.div_add_mod (n - m0) L
  have hrlt := Nat.mod_lt (n - m0) hL
  set r := (n - m0) / L with hrdef
  have hcomm : r * L = L * r := mul_comm r L
  have hrp_le : r * L ≤ n - m0 := by omega
  have hmono := zerosCount_mono (h := h) (m := m0) (n1 := r * L) (n2 := n - m0) hrp_le
  have hsumr := hsum r
  have hqle : qCount h m0 ≤ m0 := qCount_le h m0
  have hrZ1 : r ≤ n - qCount h n := by omega
  have hmul : r * L ≤ (n - qCount h n) * L := Nat.mul_le_mul_right L hrZ1
  have hnlt : n < m0 + r * L + L := by omega
  omega

/-! ### Discharging `sweep`'s side hypotheses -/

/-- **Paper: "a period contains a zero"**: eventual periodicity would force
a positive zero-density, contradicting `ZeroFreqLiminfZero`. -/
theorem not_eventuallyPeriodic_of_liminfZero {h : ℕ → Bool}
    (hzr : ZeroRecurs h) (hlim : ZeroFreqLiminfZero h) :
    ¬ ∃ p, 0 < p ∧ ∃ T, ∀ n, T ≤ n → h (n + p) = h n := by
  rintro ⟨p, hp, T, hper⟩
  have per_iter : ∀ j n, T ≤ n → h (n + j * p) = h n := by
    intro j
    induction j with
    | zero => intro n _; simp
    | succ j ih =>
        intro n hn
        have e1 : n + (j + 1) * p = (n + j * p) + p := by ring
        rw [e1, hper (n + j * p) (by omega), ih n hn]
  obtain ⟨w0, hw0T, hw0⟩ := hzr T
  have hwin : ∀ i, 1 ≤ zerosCount h (w0 + i * p) p := by
    intro i
    have hz1 : h (w0 + i * p + 1) = false := by
      have e2 : w0 + i * p + 1 = (w0 + 1) + i * p := by ring
      rw [e2, per_iter i (w0 + 1) (by omega)]
      exact hw0
    have h1 : 1 ≤ zerosCount h (w0 + i * p) 1 := zerosCount_false hz1
    exact le_trans h1 (zerosCount_mono (by omega))
  have hbound := density_ge_of_periodic_zero (h := h) (m0 := w0) (L := p) hp hwin
  exact false_of_density_lower_bound hlim hp hbound

/-- **Paper: "there are infinitely many `σ` with `V(σ) ≥ 2`"** (density-free
route). If only finitely many antidiagonals had width `≥ 2`, a tail of `h`
would be balanced (direct antidiagonal-pairing algebra, no Morse–Hedlund);
since zero recurs, some length-`L` window beyond the tail has two zeros,
forcing (by balance) a zero in *every* length-`L` window beyond the tail,
hence a positive zero-density — contradicting `ZeroFreqLiminfZero`. -/
theorem infinitely_many_widthTwo_of_liminfZero {h : ℕ → Bool}
    (hzr : ZeroRecurs h) (hlim : ZeroFreqLiminfZero h) :
    ∀ T, ∃ σ, T ≤ σ ∧ WidthTwoAt h σ := by
  intro T
  by_contra hcon
  push_neg at hcon
  -- tail-balance: a same-length window comparison, restricted to `i ≥ T`
  have tailBalanced : ∀ i j n, T ≤ i →
      qCount h (i + n) + qCount h j ≤ qCount h i + qCount h (j + n) + 1 := by
    intro i j n hi
    by_contra hbig
    push_neg at hbig
    exact hcon (i + j + n) (by omega) ⟨i, j + n, i + n, j, by omega, by omega, by omega⟩
  -- a length-`L` window beyond `T` with (at least) two zeros
  obtain ⟨p1, hp1T, hp1⟩ := hzr T
  obtain ⟨p2, hp2T, hp2⟩ := hzr (p1 + 1)
  set L := p2 - p1 + 1 with hLdef
  have hL2 : 2 ≤ L := by omega
  have hLpos : 0 < L := by omega
  set M := L - 2 with hMdef
  have hLM : L = M + 2 := by omega
  have hones1 : onesCount h p1 1 = 0 := by rw [onesCount_one, hp1]; simp
  have hones2 : onesCount h (p1 + 1 + M) 1 = 0 := by
    have e : p1 + 1 + M + 1 = p2 + 1 := by omega
    rw [onesCount_one, e, hp2]; simp
  have hsplit : onesCount h p1 L =
      onesCount h p1 1 + (onesCount h (p1 + 1) M + onesCount h (p1 + 1 + M) 1) := by
    rw [hLM, show M + 2 = 1 + (M + 1) from by ring, onesCount_add, onesCount_add]
  have hmid_le : onesCount h (p1 + 1) M ≤ M := onesCount_le h (p1 + 1) M
  have hones_w0 : onesCount h p1 L ≤ M := by omega
  -- balance transports this bound to every window starting at `m' ≥ T`
  have onesCompare : ∀ m', T ≤ m' → onesCount h m' L ≤ onesCount h p1 L + 1 := by
    intro m' hm'
    have hb := tailBalanced m' p1 L hm'
    have e1 := qCount_add h m' L
    have e2 := qCount_add h p1 L
    omega
  have hwin : ∀ i, 1 ≤ zerosCount h (T + i * L) L := by
    intro i
    have hc := onesCompare (T + i * L) (by omega)
    unfold zerosCount
    omega
  have hbound := density_ge_of_periodic_zero (h := h) (m0 := T) (L := L) hLpos hwin
  exact false_of_density_lower_bound hlim hLpos hbound

/-! ### The desired theorems -/

/-- **Desired theorem, width part**: a binary word with a recurring zero and
vanishing liminf zero-frequency has eventual `k`-slot width `≥ k - 1`, for
every `k ≥ 3`. Combines the two discharges above with `width_of_unbalanced`
(`Short.BinaryCore`, unmodified, density/Morse–Hedlund-free). -/
theorem binary_eventual_width {k : ℕ} (h : ℕ → Bool) (hk : 3 ≤ k)
    (hzr : ZeroRecurs h) (hlim : ZeroFreqLiminfZero h) :
    ∃ S₀, ∀ s, S₀ ≤ s → ∃ w w', w ∈ Wset h k s ∧ w' ∈ Wset h k s ∧ w + (k - 1) ≤ w' := by
  have hnp := not_eventuallyPeriodic_of_liminfZero hzr hlim
  have hunbal := infinitely_many_widthTwo_of_liminfZero hzr hlim
  obtain ⟨σ₀, _, hσ₀⟩ := hunbal 0
  exact width_of_unbalanced h hk (le_refl k) σ₀ hσ₀ hnp hunbal

/-- **Desired theorem, covering part**: for the binary alphabet
`G = {δ, k}` with `gcd(δ, k) = 1`, a recurring zero and vanishing liminf
zero-frequency give eventual tail-covering. Combines
`binary_eventual_width` with `sweep` (`Short.BinaryCore`, unmodified). -/
theorem binary_tail_covering {k d₁ : ℕ} {a : ℕ → ℕ} (hk : 3 ≤ k)
    (hgaps : HasGapsIn d₁ k a) (h : ℕ → Bool) (δ e : ℕ) (hδ : 0 < δ) (he : 0 < e)
    (hco : Nat.Coprime δ k) (hk_eq : δ + e = k)
    (hgap : ∀ n, gap a n = δ + e * (if h (n + 1) then 1 else 0))
    (hzr : ZeroRecurs h) (hlim : ZeroFreqLiminfZero h) :
    TailCovering k a := by
  obtain ⟨S₀, hS₀⟩ := binary_eventual_width h hk hzr hlim
  have hco' : Nat.Coprime δ (δ + e) := by rw [hk_eq]; exact hco
  exact sweep hk hgaps (le_refl k) h δ e hδ he hco' hk_eq.symm hgap S₀ hS₀

end Erdos1112.Proof.Short
