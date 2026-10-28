module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.Action

/-!
# Blocks for the finite Held extension certificate

Split the 1024 literal normal-form indices into 32 blocks of 32. This lets the
kernel share reductions within a block while bounding the cost of each checked
declaration. The quotient-and-remainder argument covers every index exactly as
it appears in `Action.branchAction`; no subgroup membership premise is used.

Source: the ATLAS word computation and proposed transitions in
`IntrinsicEnumeration/source/extension_discovery.json`.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.Branches

/-- The original normal-form index in a block of 32 consecutive indices. -/
@[expose] public def index (b k : Fin 32) : Fin 1024 :=
  ⟨32 * b.val + k.val, by omega⟩

/-- Block certificates exhaust all 1024 original normal-form indices. -/
public theorem forall_of_blocks {p : Fin 1024 → Prop}
    (h : ∀ b k : Fin 32, p (index b k)) (n : Fin 1024) : p n := by
  let b : Fin 32 := ⟨n.val / 32, by omega⟩
  let k : Fin 32 := ⟨n.val % 32, by omega⟩
  have hn : index b k = n := by
    apply Fin.ext
    dsimp [index, b, k]
    omega
  exact hn ▸ h b k

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.Branches
