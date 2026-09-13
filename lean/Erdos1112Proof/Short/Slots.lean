/- Short paper: toggled slots and the final summand as a dial. -/
import Erdos1112Proof.Short.Intervals
import Erdos1112Proof.Short.Kit

namespace Erdos1112.Proof.Short

/-- Each multiset element supplies a summand that can be toggled across its gap.
Induction on the multiset avoids any need to distinguish equal summands. -/
lemma toggle_slots {P : ℕ → ℕ} {S : Multiset ℕ}
    (hocc : ∀ δ ∈ S, ∃ n, P (n+1) = P n+δ) :
    ∃ base, ∀ v ∈ subsetSums S, base+v ∈ kFoldSumset S.card P := by
  induction S using Multiset.induction with
  | empty =>
    refine ⟨0,fun v hv => ?_⟩
    have hv0 : v=0 := by simpa using hv
    subst v
    exact ⟨Fin.elim0,by simp⟩
  | cons δ S ih =>
    obtain ⟨n,hn⟩ := hocc δ (Multiset.mem_cons_self _ _)
    obtain ⟨base,hbase⟩ := ih (fun v hv => hocc v (Multiset.mem_cons_of_mem hv))
    refine ⟨P n+base, fun v hv => ?_⟩
    rw [subsetSums_cons] at hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have hc := add_mem_kFoldSumset (single_mem_kFoldSumset (a := P) n) (hbase v hv)
      simpa [Multiset.card_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hc
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      have hc := add_mem_kFoldSumset (single_mem_kFoldSumset (a := P) (n+1)) (hbase w hw)
      simpa [Multiset.card_cons,hn,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hc

/-- An interval at least as long as every gap can be swept by one summand. -/
lemma dial {P : ℕ → ℕ} {k M base c : ℕ} (hmono : StrictMono P)
    (hM : 0 < M) (hstep : ∀ n, P (n+1) ≤ P n+M)
    (hmem : ∀ n i, i < M → base+P n+c+i ∈ kFoldSumset k P) :
    ∃ X, ∀ x ≥ X, x ∈ kFoldSumset k P := by
  refine ⟨base+P 0+c,fun x hx => ?_⟩
  have hex : ∃ n, x ≤ base+P n+c+(M-1) := by
    refine ⟨x,?_⟩
    have : x ≤ P x := hmono.id_le x
    omega
  let n := Nat.find hex
  have hn : x ≤ base+P n+c+(M-1) := Nat.find_spec hex
  have hlo : base+P n+c ≤ x := by
    cases hn0 : n with
    | zero => simpa [hn0] using hx
    | succ j =>
      have hj : ¬ x ≤ base+P j+c+(M-1) := Nat.find_min hex (by omega : j < n)
      have hst := hstep j
      omega
  have heq : x = base+P n+c+(x-(base+P n+c)) := by omega
  rw [heq]
  exact hmem n _ (by omega)

/-- The slot lemma in the exact form needed after obtaining SHARP's multiset. -/
theorem slots_from_run {P : ℕ → ℕ} {S : Multiset ℕ} {k M : ℕ}
    (hzero : P 0=0) (hmono : StrictMono P) (hM : 0 < M)
    (hstep : ∀ n, P (n+1) ≤ P n+M)
    (hocc : ∀ δ ∈ S, ∃ n, P (n+1)=P n+δ)
    (hcard : S.card ≤ k-1) (hk : 0 < k)
    (hrun : HasRun (subsetSums S) M) :
    ∃ X, ∀ x ≥ X, x ∈ kFoldSumset k P := by
  obtain ⟨base,hbase⟩ := toggle_slots hocc
  obtain ⟨c,hc⟩ := hrun
  apply dial hmono hM hstep (base := base) (c := c)
  intro n i hi
  have hpark : 0 ∈ kFoldSumset (k-1-S.card) P := by
    refine ⟨fun _ => 0,?_⟩
    simp [hzero]
  have hs := add_mem_kFoldSumset
    (add_mem_kFoldSumset (hbase (c+i) (hc i hi)) hpark)
    (single_mem_kFoldSumset (a := P) n)
  have hk' : S.card+(k-1-S.card)+1=k := by omega
  rw [hk'] at hs
  simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hs

end Erdos1112.Proof.Short
