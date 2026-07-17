/-
Case T scan blocks (T-tail, part (i)), lines `e = 7`:
kernel-decided verification of `TlineGo 7 h a` for `a ≤ 3000`, chunked in
three per-line blocks of ≤ 1001 values each (cacheable, failure-localizing).
-/
import Erdos1112Proof.Sharp.CaseTCore

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_1_b0 : ∀ a : ℕ, a < 1000 → TlineGo 7 1 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_1_b1 : ∀ d : ℕ, d < 1000 → TlineGo 7 1 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_1_b2 : ∀ d : ℕ, d < 1001 → TlineGo 7 1 (2000 + d) = true := by decide

/-- Line `(e,h) = (7,1)`: the full scan `a ≤ 3000`. -/
theorem T_scan_7_1 : ∀ a : ℕ, a ≤ 3000 → TlineGo 7 1 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_7_1_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_7_1_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_7_1_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_2_b0 : ∀ a : ℕ, a < 1000 → TlineGo 7 2 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_2_b1 : ∀ d : ℕ, d < 1000 → TlineGo 7 2 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_2_b2 : ∀ d : ℕ, d < 1001 → TlineGo 7 2 (2000 + d) = true := by decide

/-- Line `(e,h) = (7,2)`: the full scan `a ≤ 3000`. -/
theorem T_scan_7_2 : ∀ a : ℕ, a ≤ 3000 → TlineGo 7 2 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_7_2_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_7_2_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_7_2_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_3_b0 : ∀ a : ℕ, a < 1000 → TlineGo 7 3 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_3_b1 : ∀ d : ℕ, d < 1000 → TlineGo 7 3 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_3_b2 : ∀ d : ℕ, d < 1001 → TlineGo 7 3 (2000 + d) = true := by decide

/-- Line `(e,h) = (7,3)`: the full scan `a ≤ 3000`. -/
theorem T_scan_7_3 : ∀ a : ℕ, a ≤ 3000 → TlineGo 7 3 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_7_3_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_7_3_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_7_3_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_4_b0 : ∀ a : ℕ, a < 1000 → TlineGo 7 4 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_4_b1 : ∀ d : ℕ, d < 1000 → TlineGo 7 4 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_4_b2 : ∀ d : ℕ, d < 1001 → TlineGo 7 4 (2000 + d) = true := by decide

/-- Line `(e,h) = (7,4)`: the full scan `a ≤ 3000`. -/
theorem T_scan_7_4 : ∀ a : ℕ, a ≤ 3000 → TlineGo 7 4 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_7_4_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_7_4_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_7_4_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

end Proof
end Erdos1112
