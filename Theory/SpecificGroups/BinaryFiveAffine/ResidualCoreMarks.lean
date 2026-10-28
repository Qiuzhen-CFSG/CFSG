module
public import Theory.SpecificGroups.BinaryFiveAffine.ResidualMovement
public import Theory.GroupTheory.PCoreLocalSetup
/-!
# The residual-core mark in the affine pair centralizer

The product of the marked pair with the Sylow center is a nonidentity
translation in the residual A₄. The normal vector subgroup shows that this
translation lies in its two-core, retaining the coordinate needed for the
faithful residual action in the original involution-centralizer argument.

Source: Aschbacher--Smith 2.4.29, printed pp.545--546.
-/
public section
namespace BinaryFiveAffine
open Subgroup

theorem t_standardZ_mem_residual_core : t*standardZ∈residualImage.pCoreIn 2 := by
  have hn : vectorGroup.Normal := by rw [←pCore_eq_vectorGroup]; infer_instance
  let := hn
  have hp : IsPGroup 2 vectorGroup := by rw [←pCore_eq_vectorGroup]; exact pCore_isPGroup
  have hc : residualImage ⊓ vectorGroup ≤ residualImage.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (hp.to_le inf_le_right) inf_le_left
      ((le_inf residualImage.le_normalizer le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf)
  apply hc
  constructor
  · rw [residualImage_eq]
    let g : alternatingGroup (Fin 4) :=
      ⟨Equiv.swap 0 3 * Equiv.swap 1 2,by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
    have he : symmetricEmbedding g.val=t*standardZ := by
      apply SemidirectProduct.ext <;> decide +kernel
    rw [←he]
    exact mem_map_of_mem _ g.property
  · rw [standardZ_eq_centralSingular]
    exact vectorGroup.mul_mem t_mem_vectorGroup ⟨centralSingular,rfl⟩

theorem t_standardZ_ne_one : t*standardZ≠1 := by
  intro h
  have he := congrArg SemidirectProduct.left h
  have hn : (t*standardZ).left≠(1:W).left := by decide +kernel
  exact hn he
end BinaryFiveAffine
