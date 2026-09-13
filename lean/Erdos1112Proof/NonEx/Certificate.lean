/-
Compatibility shim: the diagonal certificate lemma moved to
`Short/Certificate.lean` (same namespace, same declarations). Kept as an
import-only re-export so existing `import Erdos1112Proof.NonEx.Certificate`
lines keep working; root will delete this path once every caller has been
repointed. Do not add declarations here.
-/
import Erdos1112Proof.Short.Certificate
