module

public import Theory.AlgebraicGroup.RootSystems.TypeE6RootPairing
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# The pinned E6 diagram permutation on roots

In the standard numbering the two length-two arms are `0–1–2` and
`5–4–2`, with the remaining vertex `3` attached to `2`. We exchange the two
arms and fix `2,3`. Cartan-matrix invariance extends this permutation to the
root pairing. The extension is involutive because its square fixes a basis.

This supplies the root permutation for the graph-field construction of
GLS3, §§2.1–2.3 (`refs/KGroup/GLS3/chapter2.tex`); lifting it to the integral
root operators is a separate step.
-/

@[expose] public section

namespace Theory.AlgebraicGroup.StandardRootSystem

/-- The nontrivial symmetry of the standard E6 diagram. -/
def typeE6DiagramPermutation : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 2, 3, 1, 0]
  invFun := ![5, 4, 2, 3, 1, 0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp] theorem typeE6DiagramPermutation_twice (i : Fin 6) :
    typeE6DiagramPermutation (typeE6DiagramPermutation i) = i := by
  fin_cases i <;> rfl

theorem typeE6DiagramPermutation_cartan (i j : Fin 6) :
    typeE6CartanMatrix (typeE6DiagramPermutation i) (typeE6DiagramPermutation j) =
      typeE6CartanMatrix i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The same permutation on the actual support of the standard base. -/
noncomputable def typeE6DiagramBasePermutation :
    Equiv.Perm typeE6RootPairing_base.support :=
  typeE6RootPairing_baseEquiv.symm.trans
    (typeE6DiagramPermutation.trans typeE6RootPairing_baseEquiv)

@[simp] theorem typeE6DiagramBasePermutation_numbered (i : Fin 6) :
    typeE6DiagramBasePermutation (typeE6RootPairing_baseEquiv i) =
      typeE6RootPairing_baseEquiv (typeE6DiagramPermutation i) := by
  simp [typeE6DiagramBasePermutation]

@[simp] theorem typeE6DiagramBasePermutation_twice
    (i : typeE6RootPairing_base.support) :
    typeE6DiagramBasePermutation (typeE6DiagramBasePermutation i) = i := by
  obtain ⟨i, rfl⟩ := typeE6RootPairing_baseEquiv.surjective i
  simp

theorem typeE6DiagramBasePermutation_cartan
    (i j : typeE6RootPairing_base.support) :
    typeE6RootPairing_base.cartanMatrix
        (typeE6DiagramBasePermutation i) (typeE6DiagramBasePermutation j) =
      typeE6RootPairing_base.cartanMatrix i j := by
  obtain ⟨i, rfl⟩ := typeE6RootPairing_baseEquiv.surjective i
  obtain ⟨j, rfl⟩ := typeE6RootPairing_baseEquiv.surjective j
  simpa only [typeE6DiagramBasePermutation_numbered, typeE6RootPairing_base_cartan_apply]
    using typeE6DiagramPermutation_cartan i j

/-- The specified diagram symmetry extended to the entire root pairing. -/
noncomputable def typeE6DiagramEquiv : typeE6RootPairing.Equiv typeE6RootPairing :=
  typeE6RootPairing_base.equivOfCartanMatrixEq typeE6RootPairing_base
    typeE6DiagramBasePermutation typeE6DiagramBasePermutation_cartan

private theorem typeE6DiagramEquiv_weight_simple
    (i : typeE6RootPairing_base.support) :
    typeE6DiagramEquiv.weightMap (typeE6RootPairing.root i) =
      typeE6RootPairing.root (typeE6DiagramBasePermutation i) := by
  change (typeE6RootPairing_base.toWeightBasis.equiv
    typeE6RootPairing_base.toWeightBasis typeE6DiagramBasePermutation)
      (typeE6RootPairing.root i) = _
  simpa using Module.Basis.equiv_apply typeE6RootPairing_base.toWeightBasis i
    typeE6RootPairing_base.toWeightBasis typeE6DiagramBasePermutation

@[simp] theorem typeE6DiagramEquiv_simple (i : typeE6RootPairing_base.support) :
    typeE6DiagramEquiv.indexEquiv i = typeE6DiagramBasePermutation i := by
  apply typeE6RootPairing.root.injective
  rw [← RootPairing.Hom.root_weightMap_apply]
  exact typeE6DiagramEquiv_weight_simple i

private theorem typeE6DiagramEquiv_weight_twice (x : typeE6RootSpan) :
    typeE6DiagramEquiv.weightMap (typeE6DiagramEquiv.weightMap x) = x := by
  have h : typeE6DiagramEquiv.weightMap.comp typeE6DiagramEquiv.weightMap =
      LinearMap.id := by
    apply typeE6RootPairing_base.toWeightBasis.ext
    intro i
    simp only [LinearMap.comp_apply, RootPairing.Base.toWeightBasis_apply,
      typeE6DiagramEquiv_weight_simple, typeE6DiagramBasePermutation_twice,
      LinearMap.id_apply]
  exact LinearMap.congr_fun h x

@[simp] theorem typeE6DiagramEquiv_twice (r : typeE6Roots) :
    typeE6DiagramEquiv.indexEquiv (typeE6DiagramEquiv.indexEquiv r) = r := by
  apply typeE6RootPairing.root.injective
  rw [← RootPairing.Hom.root_weightMap_apply, ← RootPairing.Hom.root_weightMap_apply]
  exact typeE6DiagramEquiv_weight_twice _

@[simp] theorem typeE6DiagramEquiv_numbered (i : Fin 6) :
    typeE6DiagramEquiv.indexEquiv (typeE6SimpleRootIndex i) =
      typeE6SimpleRootIndex (typeE6DiagramPermutation i) := by
  simpa only [typeE6DiagramBasePermutation_numbered, typeE6RootPairing_baseEquiv_val]
    using typeE6DiagramEquiv_simple (typeE6RootPairing_baseEquiv i)

/-- The diagram involution is nontrivial, not merely of order dividing two. -/
theorem typeE6DiagramEquiv_moves_zero :
    typeE6DiagramEquiv.indexEquiv (typeE6SimpleRootIndex 0) ≠
      typeE6SimpleRootIndex 0 := by
  rw [typeE6DiagramEquiv_numbered]
  intro h
  have := typeE6SimpleRootIndex_injective h
  change (5 : Fin 6) = 0 at this
  exact (by decide : (5 : Fin 6) ≠ 0) this

end Theory.AlgebraicGroup.StandardRootSystem
