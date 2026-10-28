module
public import Theory.SpecificGroups.BinaryFiveAffine.ResidualFixedFour
public import Theory.SpecificGroups.BinaryFiveAffine.SylowInvolutions
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public section
/-!
# The marked moved vector of the affine involution centralizer

The product of the selected pair vector with the central Sylow vector is a
commutator of a natural module vector with an even permutation in the residual
A₄. Two-perfect commutator idempotence supplies the exact moved module needed
in the ordinary involution-centralizer continuation of 2.4.29.

Source: Aschbacher--Smith, printed pp.545--546.
-/
namespace BinaryFiveAffine
open Subgroup
open scoped commutatorElement

theorem t_standardZ_commutator : t * standardZ∈⁅vectorGroup,residualImage⁆ := by
  let g : alternatingGroup (Fin 4) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2,by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
  have hg : ⁅(SemidirectProduct.inl (tailVector 2) : W),symmetricEmbedding g.val⁆=t*standardZ := by
    apply SemidirectProduct.ext <;> decide +kernel
  rw [←hg]
  exact commutator_mem_commutator (by exact ⟨tailVector 2,rfl⟩)
    (by rw [residualImage_eq]; exact mem_map_of_mem _ g.property)

theorem standardZ_eq_centralSingular : standardZ=(SemidirectProduct.inl centralSingular : W) := by
  rw [standardZ_value,centralSingular_value]

theorem residual_commutator_idempotent :
    ⁅⁅vectorGroup,residualImage⁆,residualImage⁆=⁅vectorGroup,residualImage⁆ := by
  have hP : IsPGroup 2 vectorGroup := by
    rw [←pCore_eq_vectorGroup]
    exact pCore_isPGroup
  have hn : vectorGroup.Normal := by
    rw [←pCore_eq_vectorGroup]
    infer_instance
  let := hn
  apply commutator_isPPerfect_idempotent (p:=2) residualImage vectorGroup
  · rw [residualImage_def]
    exact isPPerfect_embedded_pResidual 2 centralizer
  · exact hP
  · exact le_normalizer_of_normal

end BinaryFiveAffine
