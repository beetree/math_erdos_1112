/-
Part III, Case T scan blocks (Lemma 3.18(i)), lines `e = 1`:
kernel-decided verification of `TlineGo 1 h a` for `a ≤ 3000`, chunked in
three per-line blocks of ≤ 1001 values each (cacheable, failure-localizing).
-/
import Erdos1112Proof.Sharp.CaseTCore

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_2_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 2 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_2_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 2 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_2_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 2 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,2)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_2 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 2 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_2_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_2_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_2_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_3_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 3 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_3_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 3 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_3_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 3 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,3)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_3 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 3 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_3_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_3_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_3_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_4_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 4 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_4_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 4 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_4_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 4 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,4)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_4 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 4 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_4_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_4_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_4_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_5_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 5 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_5_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 5 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_5_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 5 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,5)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_5 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 5 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_5_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_5_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_5_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_6_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 6 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_6_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 6 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_6_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 6 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,6)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_6 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 6 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_6_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_6_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_6_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_7_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 7 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_7_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 7 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_7_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 7 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,7)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_7 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 7 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_7_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_7_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_7_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_8_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 8 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_8_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 8 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_8_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 8 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,8)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_8 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 8 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_8_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_8_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_8_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_9_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 9 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_9_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 9 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_9_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 9 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,9)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_9 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 9 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_9_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_9_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_9_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_10_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 10 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_10_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 10 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_10_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 10 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,10)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_10 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 10 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_10_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_10_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_10_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

end Proof
end Erdos1112
