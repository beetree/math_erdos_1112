/-
Root of the `Erdos1112Proof` library: the proof development that proves the
three target theorems stated against the definitions in the frozen statement
file `Erdos1112.lean`.

The Short/ modules implement the replacement paper proof. The legacy Sharp/ and
NonEx/ imports remain during migration because Final still uses their non-existence
proof. See PROGRESS.md for the exact verification boundary.
-/
import Erdos1112Proof.Basic
import Erdos1112Proof.SubsetSums
import Erdos1112Proof.Short.Intervals
import Erdos1112Proof.Short.Slots
import Erdos1112Proof.Short.Normalization
import Erdos1112Proof.Short.Assembly
import Erdos1112Proof.Short.Binary
import Erdos1112Proof.Short.Density
import Erdos1112Proof.Short.ResidueFrame
import Erdos1112Proof.Short.EvenBudget
import Erdos1112Proof.Short.OddBudget
import Erdos1112Proof.Short.DensityLimit
import Erdos1112Proof.Short.KneserSequence
import Erdos1112Proof.Short.Funnel
import Erdos1112Proof.Short.OddSpacing
import Erdos1112Proof.Short.Movers
import Erdos1112Proof.Short.BinaryGrowth
import Erdos1112Proof.Short.KneserFinite.FinsetKneserTheorem
import Erdos1112Proof.Existence.Beatty
import Erdos1112Proof.Existence.Reciprocal
import Erdos1112Proof.Sharp.Defs
import Erdos1112Proof.Sharp.TwoGen
import Erdos1112Proof.Sharp.Frame
import Erdos1112Proof.Sharp.Staircase
import Erdos1112Proof.Sharp.Tables
import Erdos1112Proof.Sharp.TablesData
import Erdos1112Proof.Sharp.Lift
import Erdos1112Proof.Sharp.Graham
import Erdos1112Proof.Sharp.CaseD
import Erdos1112Proof.Sharp.CaseP
import Erdos1112Proof.Sharp.CaseL
import Erdos1112Proof.Sharp.CaseE
import Erdos1112Proof.Sharp.CaseT
import Erdos1112Proof.Sharp.CaseB
import Erdos1112Proof.Sharp.Main
import Erdos1112Proof.NonEx.TailCovering
import Erdos1112Proof.NonEx.Certificate
import Erdos1112Proof.NonEx.GapWord
import Erdos1112Proof.NonEx.TwoLetter.Core
import Erdos1112Proof.NonEx.TwoLetter.Balanced
import Erdos1112Proof.NonEx.TwoLetter.Sturmian
import Erdos1112Proof.NonEx.SlotLemmaParts
import Erdos1112Proof.NonEx.SlotLemma
import Erdos1112Proof.NonEx.Main
import Erdos1112Proof.Final
import Erdos1112Proof.AxiomsCheck
