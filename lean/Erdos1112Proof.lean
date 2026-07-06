/-
Root of the `Erdos1112Proof` library: the proof development that proves the
three target theorems stated against the definitions in the frozen statement
file `Erdos1112.lean`.

Layer plan:
  Layer 0  — Basic, SubsetSums
  Layer I  — Existence/ (Part I of the paper)
  Layer II — NonEx/ (Part II, reduction + two-letter core + slot lemma)
  Layer III — Sharp/ (Part III, the SHARP theorem)
  Layer IV — Final, AxiomsCheck
-/
import Erdos1112Proof.Basic
import Erdos1112Proof.SubsetSums
import Erdos1112Proof.Existence.Beatty
import Erdos1112Proof.Existence.FreeGap
import Erdos1112Proof.Existence.Nested
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
