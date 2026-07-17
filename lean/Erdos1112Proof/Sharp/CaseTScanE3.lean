/-
Case T scan blocks (T-tail, part (i)), lines `e = 3`:
kernel-decided verification of `TlineGo 3 h a` for `a ≤ 3000`, chunked in
three per-line blocks of ≤ 1001 values each (cacheable, failure-localizing).
-/
import Erdos1112Proof.Sharp.CaseTCore

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_1_b0 : ∀ a : ℕ, a < 1000 → TlineGo 3 1 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_1_b1 : ∀ d : ℕ, d < 1000 → TlineGo 3 1 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_1_b2 : ∀ d : ℕ, d < 1001 → TlineGo 3 1 (2000 + d) = true := by decide

/-- Line `(e,h) = (3,1)`: the full scan `a ≤ 3000`. -/
theorem T_scan_3_1 : ∀ a : ℕ, a ≤ 3000 → TlineGo 3 1 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_3_1_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_3_1_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_3_1_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_2_b0 : ∀ a : ℕ, a < 1000 → TlineGo 3 2 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_2_b1 : ∀ d : ℕ, d < 1000 → TlineGo 3 2 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_2_b2 : ∀ d : ℕ, d < 1001 → TlineGo 3 2 (2000 + d) = true := by decide

/-- Line `(e,h) = (3,2)`: the full scan `a ≤ 3000`. -/
theorem T_scan_3_2 : ∀ a : ℕ, a ≤ 3000 → TlineGo 3 2 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_3_2_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_3_2_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_3_2_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_4_b0 : ∀ a : ℕ, a < 1000 → TlineGo 3 4 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_4_b1 : ∀ d : ℕ, d < 1000 → TlineGo 3 4 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_4_b2 : ∀ d : ℕ, d < 1001 → TlineGo 3 4 (2000 + d) = true := by decide

/-- Line `(e,h) = (3,4)`: the full scan `a ≤ 3000`. -/
theorem T_scan_3_4 : ∀ a : ℕ, a ≤ 3000 → TlineGo 3 4 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_3_4_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_3_4_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_3_4_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_5_b0 : ∀ a : ℕ, a < 1000 → TlineGo 3 5 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_5_b1 : ∀ d : ℕ, d < 1000 → TlineGo 3 5 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_5_b2 : ∀ d : ℕ, d < 1001 → TlineGo 3 5 (2000 + d) = true := by decide

/-- Line `(e,h) = (3,5)`: the full scan `a ≤ 3000`. -/
theorem T_scan_3_5 : ∀ a : ℕ, a ≤ 3000 → TlineGo 3 5 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_3_5_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_3_5_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_3_5_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_6_b0 : ∀ a : ℕ, a < 1000 → TlineGo 3 6 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_6_b1 : ∀ d : ℕ, d < 1000 → TlineGo 3 6 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_6_b2 : ∀ d : ℕ, d < 1001 → TlineGo 3 6 (2000 + d) = true := by decide

/-- Line `(e,h) = (3,6)`: the full scan `a ≤ 3000`. -/
theorem T_scan_3_6 : ∀ a : ℕ, a ≤ 3000 → TlineGo 3 6 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_3_6_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_3_6_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_3_6_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_7_b0 : ∀ a : ℕ, a < 1000 → TlineGo 3 7 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_7_b1 : ∀ d : ℕ, d < 1000 → TlineGo 3 7 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_7_b2 : ∀ d : ℕ, d < 1001 → TlineGo 3 7 (2000 + d) = true := by decide

/-- Line `(e,h) = (3,7)`: the full scan `a ≤ 3000`. -/
theorem T_scan_3_7 : ∀ a : ℕ, a ≤ 3000 → TlineGo 3 7 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_3_7_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_3_7_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_3_7_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_8_b0 : ∀ a : ℕ, a < 1000 → TlineGo 3 8 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_8_b1 : ∀ d : ℕ, d < 1000 → TlineGo 3 8 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_8_b2 : ∀ d : ℕ, d < 1001 → TlineGo 3 8 (2000 + d) = true := by decide

/-- Line `(e,h) = (3,8)`: the full scan `a ≤ 3000`. -/
theorem T_scan_3_8 : ∀ a : ℕ, a ≤ 3000 → TlineGo 3 8 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_3_8_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_3_8_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_3_8_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

end Proof
end Erdos1112
