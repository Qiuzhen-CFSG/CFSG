module

public import Theory.AlgebraicGroup.RootSystems.TypeD4DiagramTriality
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.SumExchange.CanonicalCoefficients.SimpleReflection

/-!
# Finite root calculations for the diagram-fixed D₄ Weyl group

The reflection tables are those already identified with the literal D₄ root
reflections. The diagram table is identified with the actual triality map by
expanding each root in the simple-root basis. We check the twelve folded words,
their multiplication and their distinctness using their actions on all 24 roots.

The last finite certificate classifies possible images of the first and central
simple roots. Besides the dot product it uses the relation of having the same
pair of coordinate axes. The simple reflections preserve this relation, whereas
the outer diagram automorphism does not. The generated-group argument and the
proof that these two images determine a fixed Weyl element are in `DiagramFixed`.
All finite certificates are checked by kernel reduction.

Source: GLS3 §§2.3.1–3 and 2.4.4 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
open scoped BigOperators
namespace Triality.Standard.ConcreteBruhat.DiagramFixed

/-- The arm cycle in the published 24-root enumeration. -/
def diagramTable : Fin 24 → Fin 24 :=
  ![0,21,22,3,4,17,18,7,9,12,15,10,8,13,14,11,5,16,19,6,1,20,23,2]

/-- The usual integral dot product of the root coordinate vectors. -/
def scalar (r s : Fin 24) : ℤ := ∑ k : Fin 4, rootCoords r k * rootCoords s k

/-- The two roots have support on the same pair of coordinate axes. -/
def sameAxes (r s : Fin 24) : Prop := r.val / 4 = s.val / 4
instance (r s : Fin 24) : Decidable (sameAxes r s) := inferInstanceAs (Decidable (_ = _))

def reflection (i : Fin 4) : Equiv.Perm (Fin 24) where
  toFun := reflectionTable i
  invFun := reflectionTable i
  left_inv := reflectionTable_involutive i
  right_inv := reflectionTable_involutive i

def diagram : Equiv.Perm (Fin 24) where
  toFun := diagramTable
  invFun := diagramTable ∘ diagramTable
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def arm : Equiv.Perm (Fin 24) := reflection 0 * reflection 2 * reflection 3

def representative : DihedralGroup 6 → Equiv.Perm (Fin 24)
  | .r i => (arm * reflection 1) ^ i.val
  | .sr i => arm * (arm * reflection 1) ^ i.val


/-- Cached actions of the twelve folded words, checked by `representative_apply`. -/
def representativeTable : DihedralGroup 6 → Fin 24 → Fin 24
  | .r i => ![
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    ![13, 12, 15, 14, 0, 2, 1, 3, 17, 16, 19, 18, 5, 7, 4, 6, 23, 22, 21, 20, 9, 8, 11, 10],
    ![7, 5, 6, 4, 13, 15, 12, 14, 22, 23, 20, 21, 2, 3, 0, 1, 10, 11, 8, 9, 16, 17, 18, 19],
    ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20],
    ![14, 15, 12, 13, 3, 1, 2, 0, 18, 19, 16, 17, 6, 4, 7, 5, 20, 21, 22, 23, 10, 11, 8, 9],
    ![4, 6, 5, 7, 14, 12, 15, 13, 21, 20, 23, 22, 1, 0, 3, 2, 9, 8, 11, 10, 19, 18, 17, 16]] i
  | .sr i => ![
    ![0, 2, 1, 3, 13, 12, 15, 14, 17, 16, 19, 18, 5, 4, 7, 6, 9, 8, 11, 10, 23, 22, 21, 20],
    ![4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 14, 13, 15, 20, 21, 22, 23, 16, 17, 18, 19],
    ![14, 12, 15, 13, 4, 6, 5, 7, 21, 20, 23, 22, 1, 3, 0, 2, 19, 18, 17, 16, 9, 8, 11, 10],
    ![3, 1, 2, 0, 14, 15, 12, 13, 18, 19, 16, 17, 6, 7, 4, 5, 10, 11, 8, 9, 20, 21, 22, 23],
    ![7, 6, 5, 4, 3, 2, 1, 0, 11, 10, 9, 8, 15, 13, 14, 12, 23, 22, 21, 20, 19, 18, 17, 16],
    ![13, 15, 12, 14, 7, 5, 6, 4, 22, 23, 20, 21, 2, 0, 3, 1, 16, 17, 18, 19, 10, 11, 8, 9]] i

lemma representative_apply (x : DihedralGroup 6) (r : Fin 24) :
    representative x r = representativeTable x r := by
  revert x r
  decide +kernel

set_option maxRecDepth 4000 in
lemma reflection_scalar (i : Fin 4) (r s : Fin 24) :
    scalar (reflection i r) (reflection i s) = scalar r s := by
  revert i r s
  decide +kernel

lemma reflection_sameAxes (i : Fin 4) (r s : Fin 24) :
    sameAxes (reflection i r) (reflection i s) ↔ sameAxes r s := by
  revert i r s
  decide +kernel

lemma scalar_separates (r s : Fin 24) :
    (∀ i : Fin 4, scalar r (simpleIndex i) = scalar s (simpleIndex i)) → r = s := by
  revert r s
  decide +kernel

lemma representative_mul (x y : DihedralGroup 6) :
    representative (x * y) = representative x * representative y := by
  ext r
  simp only [Equiv.Perm.mul_apply, representative_apply]
  revert x y r
  decide +kernel

lemma representative_injective : Function.Injective representative := by
  have h : Function.Injective (fun x => (representativeTable x 1, representativeTable x 13)) := by
    decide +kernel
  intro x y hxy
  apply h
  simpa only [representative_apply] using congrArg (fun p : Equiv.Perm (Fin 24) => (p 1, p 13)) hxy

lemma representative_commutes (x : DihedralGroup 6) :
    diagram * representative x = representative x * diagram := by
  ext r
  simp only [Equiv.Perm.mul_apply, representative_apply]
  revert x r
  decide +kernel

lemma pair_coverage (a b : Fin 24)
    (hb : diagram b = b) (hab : scalar a b = -1)
    (ha : scalar a (diagram a) = 0)
    (hs : sameAxes (diagram a) (diagram (diagram a))) :
    ∃ x : DihedralGroup 6,
      representative x (simpleIndex 0) = a ∧ representative x (simpleIndex 1) = b := by
  simp only [representative_apply]
  revert a b
  decide +kernel

lemma diagramTable_coords (r : Fin 24) :
    rootCoords (diagramTable r) =
      ∑ j : Fin 4, simpleCoefficients r j • rootCoords (simpleIndex (typeD4DiagramPermutation j)) := by
  revert r
  decide +kernel

lemma root_expansion (r : Fin 24) :
    (typeDRootPairing 2).root (rootEnumeration r) =
      ∑ j : Fin 4, (simpleCoefficients r j : ℝ) •
        (typeDRootPairing 2).root (rootEnumeration (simpleIndex j)) := by
  apply Subtype.ext
  ext k
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, rootCoords_spec]
  have h := congrFun (simpleCoefficients_spec r) k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  exact_mod_cast h

lemma rootEnumeration_diagram (r : Fin 24) :
    rootEnumeration (diagram r) = typeD4DiagramEquiv.indexEquiv (rootEnumeration r) := by
  apply (typeDRootPairing 2).root.injective
  rw [← RootPairing.Hom.root_weightMap_apply, root_expansion r, map_sum]
  simp only [map_smul, rootEnumeration_simpleIndex,
    RootPairing.Hom.root_weightMap_apply, typeD4DiagramEquiv_numbered]
  apply Subtype.ext
  ext k
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, ← rootEnumeration_simpleIndex, rootCoords_spec]
  have h := congrFun (diagramTable_coords r) k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  exact_mod_cast h

end Triality.Standard.ConcreteBruhat.DiagramFixed
