module

public import Theory.AlgebraicGroup.RootSystems.OrthogonalRootSubgroupsCommute
public import Theory.AlgebraicGroup.Semisimple.RootBlocks

universe u

/-!
The closure-level root-block commutator theorem for distinct irreducible
orthogonal components.  The root-system module proves the required pointwise
Chevalley commutation, and `RootBlocks` lifts it through generated subgroups
and their connected Zariski closures.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem connectedRootBlockSubgroup_commutator_eq_bot_of_orthogonalParts
    {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
    (D : RootGroupData G T) (C : ChevalleyData G D)
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hC : IsChevalleySystem D C P e base)
    (d : P.OrthogonalDecomposition)
    (hd : d.IsIrreducible)
    {s t : Set ι} (hs : s ∈ d.parts) (ht : t ∈ d.parts) (hst : s ≠ t) :
    ⁅(connectedRootBlockSubgroup D (e.symm '' s)).toSubgroup,
      (connectedRootBlockSubgroup D (e.symm '' t)).toSubgroup⁆ = ⊥ := by
  apply connectedRootBlockSubgroup_commutator_eq_bot_of_rootFactor_commute
  intro α hα β hβ
  obtain ⟨i, hi, rfl⟩ := hα
  obtain ⟨j, hj, rfl⟩ := hβ
  have hi' : e (e.symm i) ∈ s := by simpa using hi
  have hj' : e (e.symm j) ∈ t := by simpa using hj
  exact rootSubgroups_commute_of_distinct_orthogonal_parts
    D C P e base hC d hd hs ht hst hi' hj'

end Theory.AlgebraicGroup
