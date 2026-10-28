module

public import Theory.AlgebraicGroup.RootSystems.Classical
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# Triality on the standard D4 root pairing

The standard D4 diagram has central vertex `1` and arms `0, 2, 3`.
Cycling those arms preserves the Cartan matrix and hence extends to an
automorphism of the root pairing. Its cube fixes a weight basis, so it fixes
every root. Its action on the first simple root proves it is nontrivial.

This is the diagram component in the graph-field construction of GLS3,
§§2.1–2.3 (`refs/KGroup/GLS3/chapter2.tex`). It acts on the actual D4 root
pairing; lifting this action to the integral root matrices is a separate step.
-/

@[expose] public section

namespace Theory.AlgebraicGroup.StandardRootSystem

/-- Cycle the three arms and fix the central vertex of D4. -/
def typeD4DiagramPermutation : Equiv.Perm (Fin 4) where
  toFun := ![2, 1, 3, 0]
  invFun := ![3, 1, 0, 2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp] theorem typeD4DiagramPermutation_three (i : Fin 4) :
    typeD4DiagramPermutation (typeD4DiagramPermutation (typeD4DiagramPermutation i)) = i := by
  fin_cases i <;> rfl

theorem typeD4DiagramPermutation_cartan (i j : Fin 4) :
    typeDCartanMatrix 2 (typeD4DiagramPermutation i) (typeD4DiagramPermutation j) =
      typeDCartanMatrix 2 i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The arm cycle on the actual support of the standard base. -/
noncomputable def typeD4DiagramBasePermutation :
    Equiv.Perm (typeDRootPairing_base 2).support :=
  (typeDRootPairing_baseEquiv 2).symm.trans
    (typeD4DiagramPermutation.trans (typeDRootPairing_baseEquiv 2))

@[simp] theorem typeD4DiagramBasePermutation_numbered (i : Fin 4) :
    typeD4DiagramBasePermutation (typeDRootPairing_baseEquiv 2 i) =
      typeDRootPairing_baseEquiv 2 (typeD4DiagramPermutation i) := by
  simp [typeD4DiagramBasePermutation]

@[simp] theorem typeD4DiagramBasePermutation_three
    (i : (typeDRootPairing_base 2).support) :
    typeD4DiagramBasePermutation
      (typeD4DiagramBasePermutation (typeD4DiagramBasePermutation i)) = i := by
  obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective i
  simp

theorem typeD4DiagramBasePermutation_cartan
    (i j : (typeDRootPairing_base 2).support) :
    (typeDRootPairing_base 2).cartanMatrix
        (typeD4DiagramBasePermutation i) (typeD4DiagramBasePermutation j) =
      (typeDRootPairing_base 2).cartanMatrix i j := by
  obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective i
  obtain ⟨j, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective j
  simpa only [typeD4DiagramBasePermutation_numbered, typeDRootPairing_base_cartanMatrix]
    using typeD4DiagramPermutation_cartan i j

/-- The order-three diagram symmetry extended to the entire root pairing. -/
noncomputable def typeD4DiagramEquiv : (typeDRootPairing 2).Equiv (typeDRootPairing 2) :=
  (typeDRootPairing_base 2).equivOfCartanMatrixEq (typeDRootPairing_base 2)
    typeD4DiagramBasePermutation typeD4DiagramBasePermutation_cartan

theorem typeD4DiagramEquiv_weight_simple
    (i : (typeDRootPairing_base 2).support) :
    typeD4DiagramEquiv.weightMap ((typeDRootPairing 2).root i) =
      (typeDRootPairing 2).root (typeD4DiagramBasePermutation i) := by
  change ((typeDRootPairing_base 2).toWeightBasis.equiv
    (typeDRootPairing_base 2).toWeightBasis typeD4DiagramBasePermutation)
      ((typeDRootPairing 2).root i) = _
  simpa using Module.Basis.equiv_apply (typeDRootPairing_base 2).toWeightBasis i
    (typeDRootPairing_base 2).toWeightBasis typeD4DiagramBasePermutation

@[simp] theorem typeD4DiagramEquiv_simple (i : (typeDRootPairing_base 2).support) :
    typeD4DiagramEquiv.indexEquiv i = typeD4DiagramBasePermutation i := by
  apply (typeDRootPairing 2).root.injective
  rw [← RootPairing.Hom.root_weightMap_apply]
  exact typeD4DiagramEquiv_weight_simple i

theorem typeD4DiagramEquiv_weight_three (x : typeDRootSpan 4) :
    typeD4DiagramEquiv.weightMap
      (typeD4DiagramEquiv.weightMap (typeD4DiagramEquiv.weightMap x)) = x := by
  have h : typeD4DiagramEquiv.weightMap.comp
      (typeD4DiagramEquiv.weightMap.comp typeD4DiagramEquiv.weightMap) = LinearMap.id := by
    apply (typeDRootPairing_base 2).toWeightBasis.ext
    intro i
    simp only [LinearMap.comp_apply, RootPairing.Base.toWeightBasis_apply,
      typeD4DiagramEquiv_weight_simple, typeD4DiagramBasePermutation_three,
      LinearMap.id_apply]
  exact LinearMap.congr_fun h x

@[simp] theorem typeD4DiagramEquiv_three (r : TypeDRootIndex 4) :
    typeD4DiagramEquiv.indexEquiv
      (typeD4DiagramEquiv.indexEquiv (typeD4DiagramEquiv.indexEquiv r)) = r := by
  apply (typeDRootPairing 2).root.injective
  rw [← RootPairing.Hom.root_weightMap_apply, ← RootPairing.Hom.root_weightMap_apply,
    ← RootPairing.Hom.root_weightMap_apply]
  exact typeD4DiagramEquiv_weight_three _

@[simp] theorem typeD4DiagramEquiv_numbered (i : Fin 4) :
    typeD4DiagramEquiv.indexEquiv (typeDSimpleRootIndex 2 i) =
      typeDSimpleRootIndex 2 (typeD4DiagramPermutation i) := by
  simpa only [typeD4DiagramBasePermutation_numbered, typeDRootPairing_baseEquiv_val]
    using typeD4DiagramEquiv_simple (typeDRootPairing_baseEquiv 2 i)

/-- This root permutation is nontrivial, so its period is exactly three. -/
theorem typeD4DiagramEquiv_moves_zero :
    typeD4DiagramEquiv.indexEquiv (typeDSimpleRootIndex 2 0) ≠
      typeDSimpleRootIndex 2 0 := by
  rw [typeD4DiagramEquiv_numbered]
  intro h
  have := typeDSimpleRootIndex_injective 2 h
  change (2 : Fin 4) = 0 at this
  exact (by decide : (2 : Fin 4) ≠ 0) this

end Theory.AlgebraicGroup.StandardRootSystem
