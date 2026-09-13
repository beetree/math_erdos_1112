/- The paper's table-free finite interval lemma, with every branch discharged. -/
import Erdos1112Proof.Short.SharpAssembly
import Erdos1112Proof.Short.EtaOdd

namespace Erdos1112.Proof.Short

/-- SHARP: at most `M-1` alphabet elements yield `M` consecutive subset sums. -/
theorem sharp_all : ∀ M, SharpAt M :=
  sharp_all_of_odd (fun _ _ _ hn hab hbM hcab hcaM hcbM hdense hnodiv =>
    eta_odd hn hab hbM hcab hcaM hcbM hdense hnodiv)

end Erdos1112.Proof.Short
