/- Short paper Appendix A: the inductive funnel (`prop:funnel`).

Reduces `SharpAt M` to the pairwise coprime dense triples `a < b < M`,
`gcd(a,b) = gcd(a,M) = gcd(b,M) = 1`, `a + b ≥ M + 2`, given `SharpAt` below
`M` (the outer strong induction) and a solver for that dense-triple case
(supplied elsewhere, via movers/residue-path arguments).

No imports of the old `Sharp/Graham.lean` case analysis, tables, or
staircase; only the definitions from `Sharp/Defs.lean` and the elementary
constructions of `Short/Intervals.lean`. -/
import Erdos1112Proof.Short.SharpDefs
import Erdos1112Proof.Short.Intervals

namespace Erdos1112.Proof.Short

open Erdos1112.Proof

/-- If `G` has overall gcd `1` and `M ∈ G`, the gcd of the rest of `G` is
coprime to `M`. -/
private lemma coprime_gcd_erase_self {G : Finset ℕ} {M : ℕ}
    (hgcd : G.gcd id = 1) (hMG : M ∈ G) :
    Nat.Coprime ((G.erase M).gcd id) M := by
  have hdvd : Nat.gcd ((G.erase M).gcd id) M ∣ G.gcd id := by
    apply Finset.dvd_gcd
    intro x hx
    rcases eq_or_ne x M with rfl | hne
    · exact Nat.gcd_dvd_right _ _
    · exact (Nat.gcd_dvd_left _ M).trans
        (Finset.gcd_dvd (Finset.mem_erase.mpr ⟨hne, hx⟩))
  rw [hgcd] at hdvd
  exact Nat.dvd_one.mp hdvd

/-! ### The `|H| ≥ 3` branch: the outer strong induction. -/

private lemma funnel_ge_three {M : ℕ} (hind : ∀ M' < M, SharpAt M')
    {G : Finset ℕ} (hpos : ∀ g ∈ G, 0 < g) (hgcd : G.gcd id = 1)
    (hmax : ∀ g ∈ G, g ≤ M) (hMG : M ∈ G) (hHcard : 3 ≤ (G.erase M).card) :
    ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ G) ∧ S.card ≤ M - 1 ∧
      HasRun (subsetSums S) M := by
  classical
  set H := G.erase M with hHdef
  have hHsub : H ⊆ G := Finset.erase_subset _ _
  have hHpos : ∀ h ∈ H, 0 < h := fun h hh => hpos h (hHsub hh)
  have hHlt : ∀ h ∈ H, h < M := by
    intro h hh
    have h1 := (Finset.mem_erase.mp hh).1
    have h2 := hmax h (hHsub hh)
    omega
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a0, ha0⟩ := hHne
  have ha0pos : (0 : ℕ) < a0 := hHpos a0 ha0
  set d := H.gcd id with hddef
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      have hz := Finset.gcd_eq_zero_iff.mp h0 a0 ha0
      simp only [id] at hz
      omega
    · exact h0
  have hddvd : ∀ h ∈ H, d ∣ h := fun h hh => Finset.gcd_dvd hh
  set H' := H.image (fun x => x / d) with hH'def
  have hinj : Set.InjOn (fun x => x / d) H := by
    intro x hx y hy hxy
    have hdx := hddvd x hx
    have hdy := hddvd y hy
    have ex : d * (x / d) = x := Nat.mul_div_cancel' hdx
    have ey : d * (y / d) = y := Nat.mul_div_cancel' hdy
    simp only at hxy
    rw [← ex, ← ey, hxy]
  have hH'card : H'.card = H.card := Finset.card_image_of_injOn hinj
  have hH'pos : ∀ x ∈ H', 0 < x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hdy := hddvd y hy
    have hypos := hHpos y hy
    have hex : d * (y / d) = y := Nat.mul_div_cancel' hdy
    rcases Nat.eq_zero_or_pos (y / d) with h0 | h0
    · rw [h0, mul_zero] at hex; omega
    · exact h0
  have hH'gcd : H'.gcd id = 1 := by
    have key := Finset.gcd_div_id_eq_one ha0 (show a0 ≠ 0 by omega)
    rwa [← hddef, Finset.gcd_eq_gcd_image, ← hH'def] at key
  have hH'ne : H'.Nonempty := ⟨a0 / d, Finset.mem_image_of_mem _ ha0⟩
  set e := H'.max' hH'ne with hedef
  have heH' : e ∈ H' := Finset.max'_mem _ _
  have heub : ∀ x ∈ H', x ≤ e := fun x hx => Finset.le_max' _ x hx
  have he3 : 3 ≤ e := by
    have hsub : H' ⊆ Finset.Icc 1 e := by
      intro x hx
      have h1 := hH'pos x hx
      have h2 := heub x hx
      simp only [Finset.mem_Icc]
      omega
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    omega
  obtain ⟨y0, hy0, hey0⟩ := Finset.mem_image.mp heH'
  have hde0 : d * e = y0 := by
    have hh := Nat.mul_div_cancel' (hddvd y0 hy0)
    rw [hey0] at hh
    exact hh
  have hy0M : y0 < M := hHlt y0 hy0
  have heltM : e < M := by
    have hle := Nat.div_le_self y0 d
    omega
  obtain ⟨S', hS'sub, hS'card, hS'run⟩ :=
    hind e heltM H' hH'pos (by omega : 3 ≤ H'.card) hH'gcd heub heH'
  have hextend := extend_run (le_refl e) hS'run ((M - 1) / e)
  have hMle : M ≤ e + (M - 1) / e * e := by
    have h1 := Nat.div_add_mod (M - 1) e
    have h2 := Nat.mod_lt (M - 1) (show 0 < e by omega)
    have h3 : (M - 1) / e * e = e * ((M - 1) / e) := by ring
    omega
  have hrunM : HasRun (subsetSums (Multiset.replicate ((M - 1) / e) e + S')) M :=
    HasRun.of_le hMle hextend
  have hcopM : Nat.Coprime d M := coprime_gcd_erase_self hgcd hMG
  have hinterlace := interlacing hdpos hcopM (le_refl M) hrunM
  refine ⟨(Multiset.replicate ((M - 1) / e) e + S').map (d * ·) +
    Multiset.replicate (d - 1) M, ?_, ?_, hinterlace⟩
  · intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      rcases Multiset.mem_add.mp hy with hy | hy
      · have hye : y = e := Multiset.eq_of_mem_replicate hy
        rw [hye, hde0]
        exact hHsub hy0
      · have hyH' := hS'sub y hy
        obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hyH'
        have hdz : d * y = z := by
          have hh := Nat.mul_div_cancel' (hddvd z hz)
          rw [hzy] at hh
          exact hh
        rw [hdz]
        exact hHsub hz
    · have := Multiset.eq_of_mem_replicate hx
      rw [this]
      exact hMG
  · rw [Multiset.card_add, Multiset.card_map, Multiset.card_add,
      Multiset.card_replicate, Multiset.card_replicate]
    have hdeltM : e * d < M := by rw [mul_comm, hde0]; exact hy0M
    have heq : (M - 1) / e = d + (M - 1 - e * d) / e := by
      have heq2 : M - 1 = (M - 1 - e * d) + e * d := by omega
      conv_lhs => rw [heq2]
      rw [Nat.add_mul_div_left _ _ (show 0 < e by omega)]
      omega
    have hle : (M - 1 - e * d) / e ≤ M - 1 - e * d := Nat.div_le_self _ _
    have hkey2 : 2 * d + e ≤ e * d + 2 := by
      nlinarith [Nat.mul_le_mul (show 1 ≤ d by omega) (show 1 ≤ e by omega)]
    omega

/-! ### The `|H| = 2` branch: the coprime rectangle and target lemmas. -/

private lemma funnel_pair {M a b : ℕ}
    (hdense : ∀ a b : ℕ, a < b → b < M → Nat.Coprime a b → Nat.Coprime a M →
      Nat.Coprime b M → M + 2 ≤ a + b → SharpTriple a b M)
    {G : Finset ℕ} (hpos : ∀ g ∈ G, 0 < g) (hgcd : G.gcd id = 1)
    (hmax : ∀ g ∈ G, g ≤ M) (hMG : M ∈ G)
    (hHeq : G.erase M = {a, b}) (hab : a < b) :
    ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ G) ∧ S.card ≤ M - 1 ∧
      HasRun (subsetSums S) M := by
  classical
  have ha' : a ∈ G.erase M := by rw [hHeq]; simp
  have hb' : b ∈ G.erase M := by rw [hHeq]; simp
  have haG : a ∈ G := (Finset.mem_erase.mp ha').2
  have hbG : b ∈ G := (Finset.mem_erase.mp hb').2
  have hapos : 0 < a := hpos a haG
  have hbpos : 0 < b := hpos b hbG
  have hbneM : b ≠ M := (Finset.mem_erase.mp hb').1
  have hbltM : b < M := by have := hmax b hbG; omega
  have haltM : a < M := lt_trans hab hbltM
  have hgcdab : Nat.Coprime (Nat.gcd a b) M := by
    have h1 := coprime_gcd_erase_self hgcd hMG
    rw [hHeq] at h1
    simpa [Finset.gcd_insert, Finset.gcd_singleton] using h1
  by_cases hcoab : Nat.Coprime a b
  · -- gcd(a,b) = 1
    by_cases hb2 : 2 * b ≤ M
    · -- b ≤ M/2 : direct two-generator target
      obtain ⟨S0, hS0mem, hS0card, hS0run⟩ := two_generator_target hapos hab hcoab hb2
      have hMb : 2 ≤ M / b := (Nat.le_div_iff_mul_le hbpos).mpr (by omega)
      refine ⟨S0, fun x hx => ?_, ?_, hS0run⟩
      · rcases hS0mem x hx with rfl | rfl
        · exact haG
        · exact hbG
      · omega
    · push_neg at hb2
      rcases lt_trichotomy (a + b) (M + 1) with hlt1 | heq1 | hgt1
      · -- a + b ≤ M : extend the rectangle by one more copy of b
        have hrect := coprime_rectangle hapos hab hcoab
        have hextend := extend_run (show b ≤ a + b - 1 by omega) hrect 1
        have hlen : M ≤ a + b - 1 + 1 * b := by omega
        have hrun := HasRun.of_le hlen hextend
        refine ⟨_, ?_, ?_, hrun⟩
        · intro x hx
          rcases Multiset.mem_add.mp hx with hx | hx
          · rw [Multiset.eq_of_mem_replicate hx]; exact hbG
          · rcases Multiset.mem_add.mp hx with hx | hx
            · rw [Multiset.eq_of_mem_replicate hx]; exact haG
            · rw [Multiset.eq_of_mem_replicate hx]; exact hbG
        · have hc : (Multiset.replicate 1 b +
              (Multiset.replicate (b - 1) a + Multiset.replicate (a - 1) b)).card
              = 1 + ((b - 1) + (a - 1)) := by
            simp [Multiset.card_add]; omega
          rw [hc]; omega
      · -- a + b = M + 1 : the rectangle itself suffices
        have hrect := coprime_rectangle hapos hab hcoab
        have hlen : a + b - 1 = M := by omega
        rw [hlen] at hrect
        refine ⟨_, ?_, ?_, hrect⟩
        · intro x hx
          rcases Multiset.mem_add.mp hx with hx | hx
          · rw [Multiset.eq_of_mem_replicate hx]; exact haG
          · rw [Multiset.eq_of_mem_replicate hx]; exact hbG
        · have hc : (Multiset.replicate (b - 1) a +
              Multiset.replicate (a - 1) b).card = (b - 1) + (a - 1) := by
            simp [Multiset.card_add]
          rw [hc]; omega
      · -- a + b ≥ M + 2 : dense, unless a or b shares a factor with M
        have hdense_ge : M + 2 ≤ a + b := by omega
        by_cases hcoaM : Nat.Coprime a M
        · by_cases hcobM : Nat.Coprime b M
          · obtain ⟨S0, hS0mem, hS0card, hS0run⟩ :=
              hdense a b hab hbltM hcoab hcoaM hcobM hdense_ge
            exact ⟨S0, fun x hx => by
              rcases hS0mem x hx with rfl | rfl | rfl
              exacts [haG, hbG, hMG], hS0card, hS0run⟩
          · -- gcd(b,M) = e > 1
            set e := Nat.gcd b M with hedef
            have hepos : 0 < e := Nat.gcd_pos_of_pos_left M hbpos
            have he2 : 2 ≤ e := by
              have hne1 : e ≠ 1 := hcobM
              omega
            have heb : e ∣ b := Nat.gcd_dvd_left b M
            have heM : e ∣ M := Nat.gcd_dvd_right b M
            have hp : 0 < b / e := by
              rcases Nat.eq_zero_or_pos (b / e) with h0 | h0
              · exfalso
                have hh := Nat.mul_div_cancel' heb
                rw [h0, mul_zero] at hh; omega
              · exact h0
            have hph : b / e < M / e := by
              have hbe : e * (b / e) = b := Nat.mul_div_cancel' heb
              have hMe : e * (M / e) = M := Nat.mul_div_cancel' heM
              by_contra hc
              push_neg at hc
              have hmm : e * (M / e) ≤ e * (b / e) := Nat.mul_le_mul_left e hc
              omega
            have hco : Nat.Coprime (b / e) (M / e) := by
              have := Nat.coprime_div_gcd_div_gcd (show 0 < Nat.gcd b M by omega)
              simpa [hedef] using this
            have hN : 2 * (M / e) ≤ M := by
              have hMe : (M / e) * e = M := Nat.div_mul_cancel heM
              have hmm : (M / e) * 2 ≤ (M / e) * e := Nat.mul_le_mul_left (M / e) he2
              omega
            obtain ⟨S0, hS0mem, hS0card, hS0run⟩ := two_generator_target hp hph hco hN
            have hcoea : Nat.Coprime e a := (Nat.Coprime.coprime_dvd_left heb hcoab.symm)
            have hinterlace :=
              interlacing (show 0 < e by omega) hcoea (show a ≤ M by omega) hS0run
            have hMee : M / (M / e) = e := by
              have hMe : (M / e) * e = M := Nat.div_mul_cancel heM
              have hMepos : 0 < M / e := lt_trans hp hph
              exact Nat.div_eq_of_eq_mul_left hMepos (by rw [mul_comm]; exact hMe.symm)
            refine ⟨_, ?_, ?_, hinterlace⟩
            · intro x hx
              rcases Multiset.mem_add.mp hx with hx | hx
              · obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hx
                rcases hS0mem v hv with rfl | rfl
                · rw [Nat.mul_div_cancel' heb]; exact hbG
                · rw [Nat.mul_div_cancel' heM]; exact hMG
              · rw [Multiset.eq_of_mem_replicate hx]; exact haG
            · rw [Multiset.card_add, Multiset.card_map, Multiset.card_replicate]
              rw [hMee] at hS0card
              have heM' : e ≤ M := by
                have := Nat.le_of_dvd hbpos heb
                omega
              omega
        · -- gcd(a,M) = d > 1
          set d := Nat.gcd a M with hddef
          have hdpos : 0 < d := Nat.gcd_pos_of_pos_left M hapos
          have hd2 : 2 ≤ d := by
            have hne1 : d ≠ 1 := hcoaM
            omega
          have hda : d ∣ a := Nat.gcd_dvd_left a M
          have hdM : d ∣ M := Nat.gcd_dvd_right a M
          have hp : 0 < a / d := by
            rcases Nat.eq_zero_or_pos (a / d) with h0 | h0
            · exfalso
              have hh := Nat.mul_div_cancel' hda
              rw [h0, mul_zero] at hh; omega
            · exact h0
          have hph : a / d < M / d := by
            have hae : d * (a / d) = a := Nat.mul_div_cancel' hda
            have hMe : d * (M / d) = M := Nat.mul_div_cancel' hdM
            by_contra hc
            push_neg at hc
            have hmm : d * (M / d) ≤ d * (a / d) := Nat.mul_le_mul_left d hc
            omega
          have hco : Nat.Coprime (a / d) (M / d) := by
            have := Nat.coprime_div_gcd_div_gcd (show 0 < Nat.gcd a M by omega)
            simpa [hddef] using this
          have hN : 2 * (M / d) ≤ M := by
            have hMe : (M / d) * d = M := Nat.div_mul_cancel hdM
            have hmm : (M / d) * 2 ≤ (M / d) * d := Nat.mul_le_mul_left (M / d) hd2
            omega
          obtain ⟨S0, hS0mem, hS0card, hS0run⟩ := two_generator_target hp hph hco hN
          have hcodb : Nat.Coprime d b := Nat.Coprime.coprime_dvd_left hda hcoab
          have hinterlace :=
            interlacing (show 0 < d by omega) hcodb (show b ≤ M by omega) hS0run
          have hMdd : M / (M / d) = d := by
            have hMe : (M / d) * d = M := Nat.div_mul_cancel hdM
            have hMdpos : 0 < M / d := lt_trans hp hph
            exact Nat.div_eq_of_eq_mul_left hMdpos (by rw [mul_comm]; exact hMe.symm)
          refine ⟨_, ?_, ?_, hinterlace⟩
          · intro x hx
            rcases Multiset.mem_add.mp hx with hx | hx
            · obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hx
              rcases hS0mem v hv with rfl | rfl
              · rw [Nat.mul_div_cancel' hda]; exact haG
              · rw [Nat.mul_div_cancel' hdM]; exact hMG
            · rw [Multiset.eq_of_mem_replicate hx]; exact hbG
          · rw [Multiset.card_add, Multiset.card_map, Multiset.card_replicate]
            rw [hMdd] at hS0card
            have hdM' : d ≤ M := by
              have := Nat.le_of_dvd hapos hda
              omega
            omega
  · -- gcd(a,b) = d > 1
    set d := Nat.gcd a b with hddef
    have hdpos : 0 < d := Nat.gcd_pos_of_pos_left b hapos
    have hd2 : 2 ≤ d := by
      have hne1 : d ≠ 1 := hcoab
      omega
    have hda : d ∣ a := Nat.gcd_dvd_left a b
    have hdb : d ∣ b := Nat.gcd_dvd_right a b
    have hp : 0 < a / d := by
      rcases Nat.eq_zero_or_pos (a / d) with h0 | h0
      · exfalso
        have hh := Nat.mul_div_cancel' hda
        rw [h0, mul_zero] at hh; omega
      · exact h0
    have hph : a / d < b / d := by
      have hae : d * (a / d) = a := Nat.mul_div_cancel' hda
      have hbe : d * (b / d) = b := Nat.mul_div_cancel' hdb
      by_contra hc
      push_neg at hc
      have hmm : d * (b / d) ≤ d * (a / d) := Nat.mul_le_mul_left d hc
      omega
    have hco : Nat.Coprime (a / d) (b / d) := by
      have := Nat.coprime_div_gcd_div_gcd (show 0 < Nat.gcd a b by omega)
      simpa [hddef] using this
    have hN : 2 * (b / d) ≤ M := by
      have hbdb : (b / d) * d = b := Nat.div_mul_cancel hdb
      have hmm : (b / d) * 2 ≤ (b / d) * d := Nat.mul_le_mul_left (b / d) hd2
      omega
    obtain ⟨S0, hS0mem, hS0card, hS0run⟩ := two_generator_target hp hph hco hN
    have hinterlace := interlacing (show 0 < d by omega) hgcdab (le_refl M) hS0run
    have hdle : d ≤ M / (b / d) := by
      have hbdpos : 0 < b / d := lt_trans hp hph
      have h1 : (b / d) * d = b := Nat.div_mul_cancel hdb
      have h2 : d * (b / d) ≤ M := by rw [mul_comm]; omega
      exact (Nat.le_div_iff_mul_le hbdpos).mpr h2
    refine ⟨_, ?_, ?_, hinterlace⟩
    · intro x hx
      rcases Multiset.mem_add.mp hx with hx | hx
      · obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hx
        rcases hS0mem v hv with rfl | rfl
        · rw [Nat.mul_div_cancel' hda]; exact haG
        · rw [Nat.mul_div_cancel' hdb]; exact hbG
      · rw [Multiset.eq_of_mem_replicate hx]; exact hMG
    · rw [Multiset.card_add, Multiset.card_map, Multiset.card_replicate]
      have hdM' : d ≤ M := by
        have := Nat.le_of_dvd hbpos hdb
        omega
      omega

private lemma funnel_eq_two {M : ℕ}
    (hdense : ∀ a b : ℕ, a < b → b < M → Nat.Coprime a b → Nat.Coprime a M →
      Nat.Coprime b M → M + 2 ≤ a + b → SharpTriple a b M)
    {G : Finset ℕ} (hpos : ∀ g ∈ G, 0 < g) (hgcd : G.gcd id = 1)
    (hmax : ∀ g ∈ G, g ≤ M) (hMG : M ∈ G) (hHcard : (G.erase M).card = 2) :
    ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ G) ∧ S.card ≤ M - 1 ∧
      HasRun (subsetSums S) M := by
  classical
  obtain ⟨x, y, hxy, hHeq⟩ := Finset.card_eq_two.mp hHcard
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · exact funnel_pair hdense hpos hgcd hmax hMG hHeq hlt
  · have hHeq' : G.erase M = {y, x} := by rw [hHeq]; ext z; simp; tauto
    exact funnel_pair hdense hpos hgcd hmax hMG hHeq' hlt

/-- **Inductive funnel** (paper `prop:funnel`): assuming `SharpAt` below the
maximum `M`, it suffices at `M` to solve the pairwise coprime dense triples
`a < b < M`, `gcd(a,b) = gcd(a,M) = gcd(b,M) = 1`, `a + b ≥ M + 2`. -/
theorem sharpAt_of_funnel {M : ℕ} (hind : ∀ M' < M, SharpAt M')
    (hdense : ∀ a b : ℕ, a < b → b < M → Nat.Coprime a b → Nat.Coprime a M →
      Nat.Coprime b M → M + 2 ≤ a + b → SharpTriple a b M) :
    SharpAt M := by
  intro G hpos hcard hgcd hmax hMG
  have hHcard2 : 2 ≤ (G.erase M).card := by
    rw [Finset.card_erase_of_mem hMG]; omega
  rcases eq_or_lt_of_le hHcard2 with h2 | h3
  · exact funnel_eq_two hdense hpos hgcd hmax hMG h2.symm
  · exact funnel_ge_three hind hpos hgcd hmax hMG (by omega)

end Erdos1112.Proof.Short
