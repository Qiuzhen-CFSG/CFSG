module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.Coordinates
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The explicit basis of the thirteen-point augmentation module

Evaluation on the first twelve projective points identifies the augmentation
kernel with twelve coordinates. In characteristic two its inverse sends the
standard coordinate vectors to `eᵢ + e₁₂`. The two literal projective actors
therefore have entries read directly from the checked point permutations.

This connects the density certificate to the native PSL₃(3) representation
used for Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.2,
manuscript pp.9--10.
-/

@[expose] public section

open scoped BigOperators Matrix
namespace Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.PointSimplicity
open Coordinates
variable (F : Type*) [Field F] [CharP F 2]
noncomputable def basisVector (i : Fin 12) : (pointCore F).toSubmodule :=
  ⟨Pi.single (pointAt i.castSucc) 1 + Pi.single (pointAt 12) 1, by
    change (augmentation F) _ = 0
    simp [augmentation, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩
noncomputable def coord : (pointCore F).toSubmodule →ₗ[F] (Fin 12 → F) where
  toFun v i := v.val (pointAt i.castSucc)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma coord_basisVector (i : Fin 12) : coord F (basisVector F i) = Pi.single i 1 := by
  classical
  funext j
  have hj : (j.castSucc : Fin 13) ≠ 12 := Fin.castSucc_ne_last j
  simp [coord, basisVector, Pi.single_apply, pointAt_injective.eq_iff,
    Fin.castSucc_inj, Ne.symm hj]
omit [CharP F 2] in
lemma coord_injective : Function.Injective (coord F) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  change v = 0
  have hz (i : Fin 12) : v.val (pointAt i.castSucc) = 0 := congrFun hv i
  have hs : ∑ i : Fin 13, v.val (pointAt i) = 0 := by
    change ∑ i : Fin 13, v.val (pointEquiv i) = 0
    rw [_root_.Equiv.sum_comp]
    exact v.property
  rw [Fin.sum_univ_castSucc] at hs
  simp only [hz, Finset.sum_const_zero, zero_add] at hs
  apply Subtype.ext
  funext p
  obtain ⟨i, rfl⟩ := pointEquiv.surjective p
  exact Fin.lastCases hs hz i
lemma coord_surjective : Function.Surjective (coord F) := by
  intro v
  refine ⟨∑ i, v i • basisVector F i, ?_⟩
  simp only [map_sum, map_smul, coord_basisVector]
  ext i
  simp [Pi.single_apply]
noncomputable def coordinates : (pointCore F).toSubmodule ≃ₗ[F] (Fin 12 → F) :=
  LinearEquiv.ofBijective (coord F) ⟨coord_injective F, coord_surjective F⟩
noncomputable def pointBasis : Module.Basis (Fin 12) F (pointCore F).toSubmodule :=
  Module.Basis.ofEquivFun (coordinates F)
lemma pointBasis_apply (i : Fin 12) : pointBasis F i = basisVector F i := by
  apply (coordinates F).injective
  change (coordinates F) ((Module.Basis.ofEquivFun (coordinates F)) i) = _
  rw [Module.Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply]
  exact (coord_basisVector F i).symm
omit [CharP F 2] in
lemma permutation_single (g : Group) (p : PrincipalModels.PG) :
    permutation F pointPerm g (Pi.single p 1) = Pi.single (pointPerm g p) 1 := by
  classical
  funext q
  simp [permutation_apply, Pi.single_apply, _root_.Equiv.symm_apply_eq]
lemma action_entry (a : Fin 2) (i j : Fin 12) :
    LinearMap.toMatrixAlgEquiv (pointBasis F) ((pointCore F).toRepresentation (actor a)) i j =
      (if pointImage a j.castSucc = i.castSucc then 1 else 0) +
      (if pointImage a 12 = i.castSucc then 1 else 0) := by
  classical
  rw [LinearMap.toMatrixAlgEquiv_apply, pointBasis_apply]
  change coord F ((pointCore F).toRepresentation (actor a) (basisVector F j)) i = _
  change (permutation F pointPerm (actor a)
    (Pi.single (pointAt j.castSucc) 1 + Pi.single (pointAt 12) 1)) (pointAt i.castSucc) = _
  rw [map_add, permutation_single, permutation_single, pointPerm_actor, pointPerm_actor]
  simp [Pi.single_apply, pointAt_injective.eq_iff, eq_comm]
end Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.PointSimplicity
