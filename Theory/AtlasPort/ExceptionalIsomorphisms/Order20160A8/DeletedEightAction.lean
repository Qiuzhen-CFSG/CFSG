module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.DeletedEightSplit

/-!
Adapted from `Atlas/Comparisons/Exceptional/DeletedEightAction.lean`.
Coordinate permutations descend through the constant line and preserve the form.
-/

@[expose] public noncomputable section
namespace Atlas.Order20160A8.DeletedEight
open Atlas.Codes Atlas.Order20160A8.HalfWeight
open scoped BigOperators

def evenPerm (p : Equiv.Perm (Fin 8)) : evenCode ≃ₗ[Bit] evenCode where
  toFun x := ⟨fun i => x.val (p.symm i), by
    change (∑ i, x.val (p.symm i)) = 0
    rw [Equiv.sum_comp p.symm]
    exact x.property⟩
  invFun x := ⟨fun i => x.val (p i), by
    change (∑ i, x.val (p i)) = 0
    rw [Equiv.sum_comp p]
    exact x.property⟩
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' x y := by ext i; rfl
  map_smul' a x := by ext i; rfl

@[simp] theorem evenPerm_apply (p : Equiv.Perm (Fin 8)) (x : evenCode) (i : Fin 8) :
    (evenPerm p x).val i = x.val (p.symm i) := rfl

@[simp] theorem evenPerm_oneWord (p : Equiv.Perm (Fin 8)) : evenPerm p oneWord = oneWord := rfl

theorem evenPerm_constants (p : Equiv.Perm (Fin 8)) :
    constants ≤ constants.comap (evenPerm p).toLinearMap := by
  apply Submodule.span_le.mpr
  intro x hx
  have he : x = oneWord := Set.mem_singleton_iff.mp hx
  subst x
  change evenPerm p oneWord ∈ constants
  rw [evenPerm_oneWord]
  exact Submodule.subset_span (Set.mem_singleton oneWord)

def quotientPermMap (p : Equiv.Perm (Fin 8)) : W →ₗ[Bit] W :=
  constants.mapQ constants (evenPerm p).toLinearMap (evenPerm_constants p)

@[simp] theorem quotientPermMap_mk (p : Equiv.Perm (Fin 8)) (x : evenCode) :
    quotientPermMap p (Submodule.Quotient.mk x) = Submodule.Quotient.mk (evenPerm p x) := rfl

def quotientPerm (p : Equiv.Perm (Fin 8)) : W ≃ₗ[Bit] W where
  __ := quotientPermMap p
  invFun := quotientPermMap p⁻¹
  left_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk (evenPerm p⁻¹ (evenPerm p x)) = Submodule.Quotient.mk x
      congr 1
      ext i
      simp [Equiv.Perm.inv_def]
  right_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk (evenPerm p (evenPerm p⁻¹ x)) = Submodule.Quotient.mk x
      congr 1
      ext i
      simp [Equiv.Perm.inv_def]

theorem evenPerm_halfWeight (p : Equiv.Perm (Fin 8)) (x : evenCode) :
    binaryHalfWeight (evenPerm p x).val = binaryHalfWeight x.val := by
  unfold binaryHalfWeight
  congr 1
  congr 1
  rw [hammingNorm_eq_sum, hammingNorm_eq_sum]
  exact Equiv.sum_comp p.symm (fun i => if x.val i = 0 then 0 else 1)

def permutationIsometry (p : Equiv.Perm (Fin 8)) : quotientQuadratic.IsometryEquiv quotientQuadratic where
  __ := quotientPerm p
  map_app' x := by
    induction x using Submodule.Quotient.induction_on with
    | H x => exact evenPerm_halfWeight p x

end Atlas.Order20160A8.DeletedEight
