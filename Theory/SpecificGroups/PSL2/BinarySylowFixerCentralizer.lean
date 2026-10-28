module
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.SpecificGroups.PSL2.RankOneRoots
public import GorensteinWalter.PSL2Center
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Fixed subgroups of binary PSL₂ Sylow fixers

An involutory automorphism fixing a full Sylow two-subgroup pointwise is
inner. Triviality of the projective center identifies its conjugating element
as an involution, whose centralizer is the root two-group. Thus no cubic
subgroup can be fixed by such an automorphism.

This supplies the binary linear-two exclusion in the rank-one component
inspection of Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
open Subgroup
namespace Theory.PSL2
open BenderSuzuki.MatrixGroups
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- An involutory Sylow fixer in binary PSL2 has a two-group of fixed points. -/
theorem sylow_fixed_involution_isTwoGroup (P : Sylow 2 (PSL2MatrixGroup F))
    (a : MulAut (PSL2MatrixGroup F)) (ha : orderOf a = 2)
    (hfix : ∀ x ∈ P, a x = x) : IsPGroup 2 a.fixedSubgroup := by
  obtain ⟨t,_,rfl⟩ := aut_fixing_sylow_inner P a hfix
  have ht : orderOf t = 2 :=
    (orderOf_injective MulAut.conj (Theory.GroupTheory.conj_injective_of_center_eq_bot
      (GorensteinWalter.psl2_center_eq_bot F)) t).symm.trans ha
  rw [MulAut.fixedSubgroup_conj]
  exact (involution_root_geometry t ht).choose_spec.choose_spec.2.2.2
end Theory.PSL2
