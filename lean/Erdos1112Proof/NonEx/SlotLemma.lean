/-
Part II, Lemma 2.12 (Slot Lemma): alphabets with ≥ 3 letters reduce to the
finite subset-sum lemma (SHARP): if `k − 1 ≥ m(G∞)` then `kA` is
tail-covering — fine slots realize an M-run of subset sums, the k-th summand
is the coarse dial. Consumes Theorem 3 (SHARP) from the Sharp/ layer.
Paper: proof/02-nonexistence.md §II.5.

The `sharp`-independent sub-lemmas live in `SlotLemmaParts.lean`; this file
holds only the final assembly, the sole part that imports `Sharp.Main`.
-/
import Erdos1112Proof.NonEx.SlotLemmaParts
import Erdos1112Proof.Sharp.Main

namespace Erdos1112
namespace Proof

open scoped Classical

/-- **Slot core (gcd 1)**: the Slot Lemma when the tail alphabet already has
gcd 1. The slot construction: build `G∞'` as a Finset with
`max = M ≤ d₂`, apply `sharp M` to get a multiset `S` with an `M`-run of
subset sums, place its `|S| ≤ M−1 ≤ k−1` letters at non-adjacent tail
positions (`exists_slot_positions`), realize `base + subsetSums S` via
`slot_realize` + `subsetSums_index`, park the remaining summands, and sweep
the last summand as the coarse dial (`slot_dial`). -/
theorem slot_core_gcd_one {k d₁ d₂ : ℕ} {a : ℕ → ℕ}
    (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hgaps : HasGapsIn d₁ d₂ a) (hd : d₂ ≤ k)
    (h3 : ∃ x y z : ℕ, x ∈ tailAlphabet a ∧ y ∈ tailAlphabet a ∧
      z ∈ tailAlphabet a ∧ x < y ∧ y < z)
    (hgcd1 : ((Finset.Icc 1 d₂).filter (· ∈ tailAlphabet a)).gcd id = 1) :
    ∃ X₀, ∀ x, X₀ ≤ x → x ∈ kFoldSumset k a := by
  classical
  set G : Finset ℕ := (Finset.Icc 1 d₂).filter (· ∈ tailAlphabet a) with hGdef
  obtain ⟨x, y, z, hx, hy, hz, hxy, hyz⟩ := h3
  have hmemG : ∀ w, w ∈ tailAlphabet a → w ∈ G := by
    intro w hw
    rw [hGdef, Finset.mem_filter, Finset.mem_Icc]
    have hb := mem_tailAlphabet_bounds hgaps hw
    exact ⟨⟨by omega, hb.2⟩, hw⟩
  have hxG := hmemG x hx; have hyG := hmemG y hy; have hzG := hmemG z hz
  have hGne : G.Nonempty := ⟨x, hxG⟩
  set M := G.max' hGne with hMdef
  have hMG : M ∈ G := Finset.max'_mem _ hGne
  have hpos : ∀ w ∈ G, 0 < w := by
    intro w hw; rw [hGdef, Finset.mem_filter, Finset.mem_Icc] at hw; omega
  have hleM : ∀ w ∈ G, w ≤ M := fun w hw => Finset.le_max' _ w hw
  have hcard3 : 3 ≤ G.card := by
    have hsub : ({x, y, z} : Finset ℕ) ⊆ G := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    have h3c : ({x, y, z} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton]; omega), Finset.card_singleton]
    exact h3c ▸ Finset.card_le_card hsub
  -- the §II.5 ↔ Part III seam: SharpAt hands `|S| ≤ M − 1`, and `M ≤ d₂ ≤ k`
  -- gives `|S| ≤ k − 1`, with the binding corner `k = d₂ = M`.
  obtain ⟨S, hSmem, hScard, hSrun⟩ := sharp M G hpos hcard3 hgcd1 hleM hMG
  have hMd2 : M ≤ d₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hGdef ▸ hMG)).1).2
  have hSk : S.card ≤ k - 1 := le_trans hScard (by omega)
  obtain ⟨c, hc⟩ := hSrun
  -- tail index (for the dial step bound)
  obtain ⟨T, hT⟩ := exists_tail_index hgaps
  -- enumerate `S` as `δ : Fin S.card → ℕ`
  have hlen : S.toList.length = S.card := Multiset.length_toList S
  set δ : Fin S.card → ℕ := fun t => S.toList.get (t.cast hlen.symm) with hδdef
  have hδmem : ∀ t, δ t ∈ S := fun t => (Multiset.mem_toList).mp (List.get_mem _ _)
  have hδtail : ∀ t, δ t ∈ tailAlphabet a := fun t =>
    (Finset.mem_filter.mp (hGdef ▸ hSmem _ (hδmem t))).2
  have hδS : Multiset.map δ Finset.univ.val = S := by
    have hlist : List.ofFn δ = S.toList := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i h1 h2
        simp only [hδdef, List.getElem_ofFn, List.get_eq_getElem, Fin.val_cast]
    rw [Fin.univ_val_map, hlist, Multiset.coe_toList]
  -- non-adjacent positions realizing each letter as a gap
  obtain ⟨p, -, -, hpgap⟩ := exists_slot_positions δ 0 hδtail
  have hM0 : 0 < M := hpos M hMG
  -- dial data: `a` is strictly increasing, and steps by `≤ M` in the tail
  have hgrow : ∀ n, T ≤ n → a n < a (n + 1) := by
    intro n _; have := hgaps.le_gap n; rw [hgaps.succ_eq_add_gap]; omega
  have hstep : ∀ n, T ≤ n → a (n + 1) ≤ a n + M := by
    intro n hn
    have hgm : gap a n ≤ M := hleM _ (hmemG _ (hT n hn))
    rw [hgaps.succ_eq_add_gap]; omega
  -- base = slot bases + parked summands; the dial sweeps
  set base : ℕ := (∑ t, a (p t)) + (k - 1 - S.card) * a 0 with hbasedef
  have hmem : ∀ n v, T ≤ n → c ≤ v → v ≤ c + (M - 1) →
      base + a n + v ∈ kFoldSumset k a := by
    intro n v _ hcv hvc
    have hvrun : v ∈ subsetSums S := by
      have hveq : v = c + (v - c) := by omega
      rw [hveq]; exact hc (v - c) (by omega)
    rw [← hδS] at hvrun
    obtain ⟨Tset, hTsum⟩ := subsetSums_index δ hvrun
    have hgapsum : (∑ t ∈ Tset, gap a (p t)) = v := by
      rw [Finset.sum_congr rfl (fun t _ => hpgap t)]; exact hTsum
    have hslot := slot_realize hgaps p Tset
    rw [hgapsum] at hslot
    have hpark : (k - 1 - S.card) * a 0 ∈ kFoldSumset (k - 1 - S.card) a := by
      refine ⟨fun _ => 0, ?_⟩
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hcomb := add_mem_kFoldSumset (add_mem_kFoldSumset hslot hpark)
      (single_mem_kFoldSumset (a := a) n)
    have hkeq : S.card + (k - 1 - S.card) + 1 = k := by omega
    rw [hkeq] at hcomb
    have hval : (∑ t, a (p t)) + v + (k - 1 - S.card) * a 0 + a n
        = base + a n + v := by rw [hbasedef]; ring
    rwa [hval] at hcomb
  exact slot_dial hM0 hgrow hstep hmem

/-- **Lemma 2.12 + (SHARP)**: a tail alphabet with at least 3 letters is
tail-covering for every `k ≥ d₂`. Rescales to gcd 1 (`exists_rescale`), runs
the slot core, and lifts back (`tailCoveringN_of_rescaled`). -/
theorem tailCovering_of_three_letters {k d₁ d₂ : ℕ} {a : ℕ → ℕ}
    (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hgaps : HasGapsIn d₁ d₂ a) (hd : d₂ ≤ k)
    (h3 : ∃ x y z : ℕ, x ∈ tailAlphabet a ∧ y ∈ tailAlphabet a ∧
      z ∈ tailAlphabet a ∧ x < y ∧ y < z) :
    TailCoveringN k a := by
  -- rescale to a gcd-1 tail alphabet
  obtain ⟨a', T, g, c, hg0, haffine, h3', hgcd1⟩ := exists_rescale hd₁ hgaps h3
  -- the rescaled sequence has the same gap-band structure (gaps of `a'` divide
  -- those of `a`, so lie in `[1, d₂]`); the slot core applies, then lift.
  suffices hcov' : TailCoveringN k a' by
    exact tailCoveringN_of_rescaled T g c hg0 a' haffine hcov'
  -- `HasGapsIn` requires `0 < a 0` (the problem's `A` is a set of positive
  -- integers). This is unneeded by the internal slot construction, which the
  -- gcd-rescaled `a' n = (a T − a T)/g` (with `a' 0 = 0`) exposes. Handle it at
  -- the interface: run the slot core on `a'' := a' + 1` (`a'' 0 = 1`, same gaps
  -- ⇒ same gcd-1 tail alphabet, so `HasGapsIn 1 d₂ a''` holds), then shift
  -- `a'' → a'` (the `k`-fold sums differ by exactly `k`).
  set a'' : ℕ → ℕ := fun n => a' n + 1 with ha''def
  have hmono' : ∀ n, a' n ≤ a' (n + 1) := by
    intro n
    have h1 := haffine n; have h2 := haffine (n + 1)
    have hm : a (T + n) ≤ a (T + (n + 1)) := hgaps.monotone (by omega)
    rw [h1, h2] at hm
    exact Nat.le_of_mul_le_mul_left (le_of_add_le_add_left hm) hg0
  have hband' : ∀ n, a' n + 1 ≤ a' (n + 1) ∧ a' (n + 1) ≤ a' n + d₂ := by
    intro n
    have h1 := haffine n; have h2 := haffine (n + 1)
    have he : T + (n + 1) = (T + n) + 1 := by omega
    have hga : a (T + (n + 1)) = a (T + n) + gap a (T + n) := by
      rw [he, hgaps.succ_eq_add_gap]
    have hle : 1 ≤ gap a (T + n) := le_trans hd₁ (hgaps.le_gap _)
    have hge : gap a (T + n) ≤ d₂ := hgaps.gap_le _
    have hd2g : d₂ ≤ g * d₂ := Nat.le_mul_of_pos_left d₂ hg0
    rw [h1, h2, Nat.add_assoc] at hga
    have hkey : g * a' (n + 1) = g * a' n + gap a (T + n) := Nat.add_left_cancel hga
    refine ⟨?_, ?_⟩
    · have hlt : g * a' n < g * a' (n + 1) := by omega
      have := Nat.lt_of_mul_lt_mul_left hlt; omega
    · have hle2 : g * a' (n + 1) ≤ g * (a' n + d₂) := by rw [Nat.mul_add]; omega
      have := Nat.le_of_mul_le_mul_left hle2 hg0; omega
  have hgaps'' : HasGapsIn 1 d₂ a'' := by
    refine ⟨Nat.succ_pos _, fun i => ⟨?_, ?_⟩⟩
    · have := (hband' i).1; simp only [ha''def]; omega
    · have := (hband' i).2; simp only [ha''def]; omega
  have hgapeq : ∀ n, gap a'' n = gap a' n := by
    intro n; simp only [gap, ha''def]; have := hmono' n; omega
  have htail_eq : tailAlphabet a'' = tailAlphabet a' := by
    ext d; simp only [tailAlphabet, Set.mem_setOf_eq, hgapeq]
  have h3'' : ∃ x y z : ℕ, x ∈ tailAlphabet a'' ∧ y ∈ tailAlphabet a'' ∧
      z ∈ tailAlphabet a'' ∧ x < y ∧ y < z := htail_eq ▸ h3'
  have hgcd1'' : ((Finset.Icc 1 d₂).filter (· ∈ tailAlphabet a'')).gcd id = 1 := by
    simp only [htail_eq]; exact hgcd1
  obtain ⟨X₀, hX₀⟩ := slot_core_gcd_one hk (le_refl 1) hgaps'' hd h3'' hgcd1''
  -- shift: `y ∈ kA'` ⇐ `y + k ∈ kA''`
  refine ⟨1, one_pos, 0, one_pos, X₀, fun y hy _ => ?_⟩
  obtain ⟨f, hf⟩ := hX₀ (y + k) (by omega)
  refine ⟨f, ?_⟩
  simp only [ha''def, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at hf
  omega

end Proof
end Erdos1112
