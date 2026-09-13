/-
Compatibility shim: the shared non-existence toolkit moved to
`Short/Kit.lean` (same namespace, same declarations). Kept as an import-only
re-export so existing `import Erdos1112Proof.NonEx.Kit` lines keep working;
root will delete this path once every caller has been repointed. Do not add
declarations here.
-/
import Erdos1112Proof.Short.Kit
