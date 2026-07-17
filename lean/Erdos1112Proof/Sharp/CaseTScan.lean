/-
Case T scan dispatch (T-tail, part (i)): the 50 per-line scans
assembled into one statement over the line parameters. GENERATED FILE.
-/
import Erdos1112Proof.Sharp.CaseTScanE1
import Erdos1112Proof.Sharp.CaseTScanE2
import Erdos1112Proof.Sharp.CaseTScanE3
import Erdos1112Proof.Sharp.CaseTScanE4
import Erdos1112Proof.Sharp.CaseTScanE5
import Erdos1112Proof.Sharp.CaseTScanE6
import Erdos1112Proof.Sharp.CaseTScanE7
import Erdos1112Proof.Sharp.CaseTScanE8
import Erdos1112Proof.Sharp.CaseTScanE9
import Erdos1112Proof.Sharp.CaseTScanE10

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
/-- **T-tail, part (i)**, decided: on every T-line (`1 ≤ e, h`, `e+h ≤ 11`,
`e ≠ h`) and every `a ≤ 3000`, side conditions imply budget-or-table. -/
theorem T_scan_all {e h a : ℕ} (he : 1 ≤ e) (hh : 1 ≤ h)
    (hμ : e + h ≤ 11) (hne : e ≠ h) (ha : a ≤ 3000) :
    TlineGo e h a = true := by
  have he10 : e ≤ 10 := by omega
  have hh10 : h ≤ 10 := by omega
  interval_cases e <;> interval_cases h <;>
    first
      | exact absurd rfl hne
      | exact T_scan_1_2 a ha
      | exact T_scan_1_3 a ha
      | exact T_scan_1_4 a ha
      | exact T_scan_1_5 a ha
      | exact T_scan_1_6 a ha
      | exact T_scan_1_7 a ha
      | exact T_scan_1_8 a ha
      | exact T_scan_1_9 a ha
      | exact T_scan_1_10 a ha
      | exact T_scan_2_1 a ha
      | exact T_scan_2_3 a ha
      | exact T_scan_2_4 a ha
      | exact T_scan_2_5 a ha
      | exact T_scan_2_6 a ha
      | exact T_scan_2_7 a ha
      | exact T_scan_2_8 a ha
      | exact T_scan_2_9 a ha
      | exact T_scan_3_1 a ha
      | exact T_scan_3_2 a ha
      | exact T_scan_3_4 a ha
      | exact T_scan_3_5 a ha
      | exact T_scan_3_6 a ha
      | exact T_scan_3_7 a ha
      | exact T_scan_3_8 a ha
      | exact T_scan_4_1 a ha
      | exact T_scan_4_2 a ha
      | exact T_scan_4_3 a ha
      | exact T_scan_4_5 a ha
      | exact T_scan_4_6 a ha
      | exact T_scan_4_7 a ha
      | exact T_scan_5_1 a ha
      | exact T_scan_5_2 a ha
      | exact T_scan_5_3 a ha
      | exact T_scan_5_4 a ha
      | exact T_scan_5_6 a ha
      | exact T_scan_6_1 a ha
      | exact T_scan_6_2 a ha
      | exact T_scan_6_3 a ha
      | exact T_scan_6_4 a ha
      | exact T_scan_6_5 a ha
      | exact T_scan_7_1 a ha
      | exact T_scan_7_2 a ha
      | exact T_scan_7_3 a ha
      | exact T_scan_7_4 a ha
      | exact T_scan_8_1 a ha
      | exact T_scan_8_2 a ha
      | exact T_scan_8_3 a ha
      | exact T_scan_9_1 a ha
      | exact T_scan_9_2 a ha
      | exact T_scan_10_1 a ha
      | exact absurd hμ (by decide)

end Proof
end Erdos1112
