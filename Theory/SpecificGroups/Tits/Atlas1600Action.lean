module

public import Theory.SpecificGroups.Tits.Atlas1600
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Canonical action of the Atlas degree-1600 group

The subgroup of permutations acts faithfully by evaluation. The first generator
moves point 0, so the group is nontrivial. The generators are the point maps from
`refs/original/n-group-global/atlas-tits-p1600-{a,b}.g`.
-/

namespace Tits

public instance atlas1600MulAction : MulAction Atlas1600Group (Fin 1600) :=
  inferInstanceAs (MulAction atlas1600Subgroup (Fin 1600))

@[simp] public theorem atlas1600_smul (g : Atlas1600Group) (x : Fin 1600) :
    g • x = g.1 x := rfl

public instance atlas1600FaithfulSMul : FaithfulSMul Atlas1600Group (Fin 1600) :=
  inferInstanceAs (FaithfulSMul atlas1600Subgroup (Fin 1600))

public instance atlas1600Nontrivial : Nontrivial Atlas1600Group := by
  refine ⟨⟨⟨atlas1600A, atlas1600A_mem⟩, 1, ?_⟩⟩
  intro h
  have heq := congrArg (fun g : Atlas1600Group => g.val 0) h
  have hne : atlas1600A 0 ≠ 0 := by decide +kernel
  exact hne heq

end Tits
