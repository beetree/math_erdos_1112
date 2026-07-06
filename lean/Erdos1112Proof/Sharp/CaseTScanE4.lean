/-
Part III, Case T scan blocks (Lemma 3.18(i)), lines `e = 4`:
kernel-decided verification of `TlineGo 4 h a` for `a ≤ 3000`, chunked in
three per-line blocks of ≤ 1001 values each (cacheable, failure-localizing).
-/
import Erdos1112Proof.Sharp.CaseTCore

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_1_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 1 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_1_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 1 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_1_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 1 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,1)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_1 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 1 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_1_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_1_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_1_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_2_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 2 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_2_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 2 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_2_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 2 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,2)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_2 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 2 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_2_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_2_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_2_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_3_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 3 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_3_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 3 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_3_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 3 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,3)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_3 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 3 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_3_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_3_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_3_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_5_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 5 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_5_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 5 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_5_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 5 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,5)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_5 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 5 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_5_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_5_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_5_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_6_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 6 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_6_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 6 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_6_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 6 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,6)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_6 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 6 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_6_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_6_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_6_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_7_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 7 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_7_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 7 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_7_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 7 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,7)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_7 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 7 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_7_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_7_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_7_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

end Proof
end Erdos1112
