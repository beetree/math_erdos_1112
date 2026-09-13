/- Short paper `lem:eta`, odd `a = 2n+1`, the `η = 2`, `λ = 0` exceptional
constructions ("For `g = 1` ..." / "For `g = 2` ...", explicit `n+1, 1, n`
and `n+3, 1, n` witnesses). No SHARP table/lift/staircase machinery. -/
import Erdos1112Proof.Short.SharpDefs
import Erdos1112Proof.Short.Intervals

namespace Erdos1112.Proof.Short

/-- Any `m ≤ 2n+1` splits as `j + 2*k` with `j ≤ 1` and `k ≤ n`: the
"offsets fill `[0,a]`" fact used at every selection level below. -/
lemma split_two (n m : ℕ) (hm : m ≤ 2 * n + 1) :
    ∃ j k, j ≤ 1 ∧ k ≤ n ∧ j + 2 * k = m := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨0, k, by omega, by omega, by omega⟩
  · exact ⟨1, k, by omega, by omega, by omega⟩

lemma three_support {a b M I J K x : ℕ}
    (hx : x ∈ Multiset.replicate I a + Multiset.replicate J b + Multiset.replicate K M) :
    x = a ∨ x = b ∨ x = M := by
  rcases Multiset.mem_add.mp hx with hx | hx
  · rcases Multiset.mem_add.mp hx with hx | hx
    · exact Or.inl (Multiset.eq_of_mem_replicate hx)
    · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hx))
  · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hx))

lemma three_mem (p q r I J K i j k : ℕ) (hi : i ≤ I) (hj : j ≤ J) (hk : k ≤ K) :
    i * p + j * q + k * r ∈
      subsetSums (Multiset.replicate I p + Multiset.replicate J q + Multiset.replicate K r) :=
  add_mem_subsetSums_add
    (add_mem_subsetSums_add (replicate_sum_mem p i I hi) (replicate_sum_mem q j J hj))
    (replicate_sum_mem r k K hk)

/-- Paper `lem:eta`, `η = 2`, `λ = 0`, `g = 1`: `n+1` copies of `a`, one of
`a+1`, `n` of `a+2`. Selection level `n+1` fills offsets `[0,a]`, level
`n+2` supplies the last offset `a+1`; the run reaches length `a+2`. -/
theorem spacing_one (n : ℕ) (hn : 2 ≤ n) :
    SharpTriple (2 * n + 1) (2 * n + 2) (2 * n + 3) := by
  refine ⟨Multiset.replicate (n + 1) (2 * n + 1) + Multiset.replicate 1 (2 * n + 2) +
    Multiset.replicate n (2 * n + 3), fun x hx => three_support hx, ?_, ?_⟩
  · have hcard : (Multiset.replicate (n + 1) (2 * n + 1) + Multiset.replicate 1 (2 * n + 2) +
        Multiset.replicate n (2 * n + 3)).card = (n + 1) + 1 + n := by simp; omega
    rw [hcard]; omega
  · refine ⟨(n + 1) * (2 * n + 1), fun r hr => ?_⟩
    by_cases hr1 : r ≤ 2 * n + 1
    · obtain ⟨j, k, hj, hk, hjk⟩ := split_two n r hr1
      obtain ⟨i, hi⟩ := Nat.le.dest (show j + k ≤ n + 1 by omega)
      have hijk : i + j + k = n + 1 := by omega
      have hmem := three_mem (2 * n + 1) (2 * n + 2) (2 * n + 3) (n + 1) 1 n i j k
        (by omega) hj hk
      have heq : i * (2 * n + 1) + j * (2 * n + 2) + k * (2 * n + 3) =
          (n + 1) * (2 * n + 1) + r := by
        calc i * (2 * n + 1) + j * (2 * n + 2) + k * (2 * n + 3)
            = (i + j + k) * (2 * n + 1) + (j + 2 * k) := by ring
          _ = (n + 1) * (2 * n + 1) + r := by rw [hijk, hjk]
      rwa [heq] at hmem
    · have hreq : r = 2 * n + 2 := by omega
      have hmem := three_mem (2 * n + 1) (2 * n + 2) (2 * n + 3) (n + 1) 1 n (n + 1) 1 0
        le_rfl le_rfl (by omega)
      have heq : (n + 1) * (2 * n + 1) + 1 * (2 * n + 2) + 0 * (2 * n + 3) =
          (n + 1) * (2 * n + 1) + r := by rw [hreq]; ring
      rwa [heq] at hmem

/-- Paper `lem:eta`, `η = 2`, `λ = 0`, `g = 2`: `n+3` copies of `a`, one of
`a+2`, `n` of `a+4`. Levels `n+1, n+2, n+3` each fill an "offsets `[0,a]`"
range in steps of `2`, of alternating parity; combined they reach a run of
length `a+4`. -/
theorem spacing_two (n : ℕ) (hn : 2 ≤ n) :
    SharpTriple (2 * n + 1) (2 * n + 3) (2 * n + 5) := by
  refine ⟨Multiset.replicate (n + 3) (2 * n + 1) + Multiset.replicate 1 (2 * n + 3) +
    Multiset.replicate n (2 * n + 5), fun x hx => three_support hx, ?_, ?_⟩
  · have hcard : (Multiset.replicate (n + 3) (2 * n + 1) + Multiset.replicate 1 (2 * n + 3) +
        Multiset.replicate n (2 * n + 5)).card = (n + 3) + 1 + n := by simp; omega
    rw [hcard]; omega
  · refine ⟨(n + 2) * (2 * n + 1), fun r hr => ?_⟩
    rcases Nat.even_or_odd r with ⟨t, ht⟩ | ⟨t, ht⟩
    · -- level n+2, offset m = t
      have htn : t ≤ 2 * n + 1 := by omega
      obtain ⟨j, k, hj, hk, hjk⟩ := split_two n t htn
      obtain ⟨i, hi⟩ := Nat.le.dest (show j + k ≤ n + 2 by omega)
      have hijk : i + j + k = n + 2 := by omega
      have hmem := three_mem (2 * n + 1) (2 * n + 3) (2 * n + 5) (n + 3) 1 n i j k
        (by omega) hj hk
      have heq : i * (2 * n + 1) + j * (2 * n + 3) + k * (2 * n + 5) =
          (n + 2) * (2 * n + 1) + r := by
        calc i * (2 * n + 1) + j * (2 * n + 3) + k * (2 * n + 5)
            = (i + j + k) * (2 * n + 1) + 2 * (j + 2 * k) := by ring
          _ = (n + 2) * (2 * n + 1) + 2 * t := by rw [hijk, hjk]
          _ = (n + 2) * (2 * n + 1) + r := by rw [ht]; ring
      rwa [heq] at hmem
    · by_cases htn : t ≤ n
      · -- level n+1, offset m = t+n+1
        have hmn : t + n + 1 ≤ 2 * n + 1 := by omega
        obtain ⟨j, k, hj, hk, hjk⟩ := split_two n (t + n + 1) hmn
        obtain ⟨i, hi⟩ := Nat.le.dest (show j + k ≤ n + 1 by omega)
        have hijk : i + j + k = n + 1 := by omega
        have hmem := three_mem (2 * n + 1) (2 * n + 3) (2 * n + 5) (n + 3) 1 n i j k
          (by omega) hj hk
        have heq : i * (2 * n + 1) + j * (2 * n + 3) + k * (2 * n + 5) =
            (n + 2) * (2 * n + 1) + r := by
          calc i * (2 * n + 1) + j * (2 * n + 3) + k * (2 * n + 5)
              = (i + j + k) * (2 * n + 1) + 2 * (j + 2 * k) := by ring
            _ = (n + 1) * (2 * n + 1) + 2 * (t + n + 1) := by rw [hijk, hjk]
            _ = (n + 2) * (2 * n + 1) + r := by rw [ht]; ring
        rwa [heq] at hmem
      · -- level n+3, offset m = 1 (the only remaining case, t = n+1)
        have ht1 : t = n + 1 := by omega
        have hmem := three_mem (2 * n + 1) (2 * n + 3) (2 * n + 5) (n + 3) 1 n (n + 2) 1 0
          (by omega) le_rfl (by omega)
        have heq : (n + 2) * (2 * n + 1) + 1 * (2 * n + 3) + 0 * (2 * n + 5) =
            (n + 2) * (2 * n + 1) + r := by rw [ht, ht1]; ring
        rwa [heq] at hmem

end Erdos1112.Proof.Short
