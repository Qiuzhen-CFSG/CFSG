module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.Relations
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Geometry
/-!
# Common signed simple-root routes for non-sum positive D4 pairs

The 24 roots are the existing coordinate enumeration of ±e_a ±e_b. The four
simple reflections are checked against their integral coordinate formulas.
The displayed route table then sends two distinct, oppositely signed simple
roots to each of the 100 ordered distinct positive pairs whose sum is absent.
The table was obtained by breadth-first search in the simultaneous reflection
action; the finite coordinate and endpoint identities are checked by the kernel.

The exported theorem concerns the actual root indices and reflection words,
with no matrix or curve identity assumed. `Transport` supplies the corresponding
operator argument on the canonical integral Geck lattice.

Source: the D4 root geometry behind GLS3 §§2.4–2.6 and 2.3.6–7
(`refs/KGroup/GLS3/chapter2.tex`).
-/

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Triality.Standard.Parabolics.RankOneMatrices
namespace Triality.Standard.PositiveCoordinates.NonsumGeometry
noncomputable section

def positiveNumber : Fin 12 → Fin 24 := ![1, 21, 20, 13, 5, 17, 16, 9, 12, 8, 4, 0]
lemma positiveNumber_spec (i : Fin 12) :
    rootEnumeration (positiveNumber i) = rootIndex i := by
  fin_cases i <;> rfl

def simpleNumber : Fin 4 → Fin 24 := ![1, 13, 21, 20]
lemma simpleNumber_spec (i : Fin 4) :
    rootEnumeration (simpleNumber i) = typeDSimpleRootIndex 2 i := by
  fin_cases i <;> rfl

def reflectNumber : Fin 4 → Fin 24 → Fin 24 :=
  ![![0, 2, 1, 3, 12, 13, 14, 15, 16, 17, 18, 19, 4, 5, 6, 7, 8, 9, 10, 11, 20, 21, 22, 23],
    ![4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 14, 13, 15, 20, 21, 22, 23, 16, 17, 18, 19],
    ![0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 16, 17, 18, 19, 12, 13, 14, 15, 20, 22, 21, 23],
    ![0, 1, 2, 3, 9, 8, 11, 10, 5, 4, 7, 6, 17, 16, 19, 18, 13, 12, 15, 14, 23, 21, 22, 20]]

lemma reflectNumber_coords (i : Fin 4) (r : Fin 24) :
    rootCoords (reflectNumber i r) = rootCoords r -
      (∑ k : Fin 4, rootCoords (simpleNumber i) k * rootCoords r k) •
        rootCoords (simpleNumber i) := by
  revert i r
  decide +kernel

lemma reflectNumber_spec (i : Fin 4) (r : Fin 24) :
    (typeDRootPairing 2).reflectionPerm (typeDSimpleRootIndex 2 i)
      (rootEnumeration r) = rootEnumeration (reflectNumber i r) := by
  apply (typeDRootPairing 2).root.injective
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    ← simpleNumber_spec]
  apply Subtype.ext
  ext k
  have hc := congrFun (reflectNumber_coords i r) k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hc
  rw [Submodule.coe_sub, Submodule.coe_smul_of_tower]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rootCoords_spec]
  rw [typeDRootPairing_pairing]
  change (rootCoords r k : ℝ) -
    (∑ l : Fin 4, ((typeDRootPairing 2).root (rootEnumeration (simpleNumber i)) : Vec 4) l *
      ((typeDRootPairing 2).root (rootEnumeration r) : Vec 4) l) *
      (rootCoords (simpleNumber i) k : ℝ) = _
  simp only [rootCoords_spec]
  exact_mod_cast hc.symm

def reflectNumbers : List (Fin 4) → Fin 24 → Fin 24
  | [], r => r
  | i :: w, r => reflectNumber i (reflectNumbers w r)

lemma reflectNumbers_spec (w : List (Fin 4)) (r : Fin 24) :
    reflectionWord (w.map (typeDRootPairing_baseEquiv 2)) (rootEnumeration r) =
      rootEnumeration (reflectNumbers w r) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.map_cons, reflectionWord, ih, reflectNumbers,
      typeDRootPairing_baseEquiv_val, reflectNumber_spec]

def pairRoute : Fin 12 → Fin 12 → List (Fin 4) × Fin 4 × Fin 4 :=
  ![![([], 0, 0), ([2], 0, 2), ([3], 0, 3), ([], 0, 0), ([1, 0], 1, 0), ([], 0, 0), ([], 0, 0), ([2, 1, 0], 1, 0), ([], 0, 0), ([3, 1, 0], 1, 0), ([3, 2, 1, 0], 1, 0), ([1, 2, 0, 1, 3], 2, 3)],
    ![([0], 2, 0), ([], 0, 0), ([3], 2, 3), ([], 0, 0), ([], 0, 0), ([1, 2], 1, 2), ([], 0, 0), ([0, 1, 2], 1, 2), ([3, 1, 2], 1, 2), ([], 0, 0), ([3, 0, 1, 2], 1, 2), ([1, 2, 0, 1, 3], 0, 3)],
    ![([0], 3, 0), ([2], 3, 2), ([], 0, 0), ([], 0, 0), ([], 0, 0), ([], 0, 0), ([1, 3], 1, 3), ([], 0, 0), ([2, 1, 3], 1, 3), ([0, 1, 3], 1, 3), ([2, 0, 1, 3], 1, 3), ([1, 3, 0, 1, 2], 0, 2)],
    ![([], 0, 0), ([], 0, 0), ([], 0, 0), ([], 0, 0), ([0, 1], 0, 1), ([2, 1], 2, 1), ([3, 1], 3, 1), ([0, 1, 2], 0, 2), ([2, 1, 3], 2, 3), ([0, 1, 3], 0, 3), ([], 0, 0), ([0, 1, 3, 2, 1, 0], 1, 0)],
    ![([0], 1, 0), ([], 0, 0), ([], 0, 0), ([1], 0, 1), ([], 0, 0), ([1, 2], 0, 2), ([1, 3], 0, 3), ([2, 0, 1], 2, 1), ([], 0, 0), ([3, 0, 1], 3, 1), ([2, 0, 1, 3], 2, 3), ([1, 3, 2, 1, 0], 1, 0)],
    ![([], 0, 0), ([2], 1, 2), ([], 0, 0), ([1], 2, 1), ([1, 0], 2, 0), ([], 0, 0), ([1, 3], 2, 3), ([2, 0, 1], 0, 1), ([3, 2, 1], 3, 1), ([], 0, 0), ([2, 0, 1, 3], 0, 3), ([1, 3, 0, 1, 2], 1, 2)],
    ![([], 0, 0), ([], 0, 0), ([3], 1, 3), ([1], 3, 1), ([1, 0], 3, 0), ([1, 2], 3, 2), ([], 0, 0), ([], 0, 0), ([3, 2, 1], 2, 1), ([3, 0, 1], 0, 1), ([3, 0, 1, 2], 0, 2), ([1, 2, 0, 1, 3], 1, 3)],
    ![([2, 0], 1, 0), ([2, 0], 1, 2), ([], 0, 0), ([1, 2, 1], 0, 2), ([0, 1], 2, 1), ([2, 1], 0, 1), ([], 0, 0), ([], 0, 0), ([2, 1, 3], 0, 3), ([0, 1, 3], 2, 3), ([3, 2, 0, 1], 3, 1), ([1, 3, 2, 0, 1], 3, 1)],
    ![([], 0, 0), ([3, 2], 1, 2), ([3, 2], 1, 3), ([1, 3, 1], 2, 3), ([], 0, 0), ([2, 1], 3, 1), ([3, 1], 2, 1), ([2, 1, 0], 3, 0), ([], 0, 0), ([3, 1, 0], 2, 0), ([3, 2, 0, 1], 0, 1), ([1, 3, 2, 0, 1], 0, 1)],
    ![([3, 0], 1, 0), ([], 0, 0), ([3, 0], 1, 3), ([1, 3, 1], 0, 3), ([0, 1], 3, 1), ([], 0, 0), ([3, 1], 0, 1), ([0, 1, 2], 3, 2), ([3, 1, 2], 0, 2), ([], 0, 0), ([3, 2, 0, 1], 2, 1), ([1, 3, 2, 0, 1], 2, 1)],
    ![([3, 2, 0], 1, 0), ([3, 2, 0], 1, 2), ([3, 2, 0], 1, 3), ([], 0, 0), ([0, 1, 3, 1], 2, 3), ([2, 1, 3, 1], 0, 3), ([3, 1, 2, 1], 0, 2), ([2, 0, 1], 3, 1), ([3, 2, 1], 0, 1), ([3, 0, 1], 2, 1), ([], 0, 0), ([0, 1, 3, 2, 0, 1], 0, 1)],
    ![([0, 1, 3, 0, 1], 2, 3), ([2, 1, 3, 2, 1], 0, 3), ([1, 3, 1, 2, 1], 0, 2), ([0, 1, 3, 2, 0], 1, 0), ([1, 3, 2, 0], 1, 0), ([1, 3, 2, 0], 1, 2), ([1, 3, 2, 0], 1, 3), ([1, 2, 0, 1], 3, 1), ([1, 3, 2, 1], 0, 1), ([1, 3, 0, 1], 2, 1), ([0, 1, 3, 2, 1], 0, 1), ([], 0, 0)]]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma pairRoute_checked (i j : Fin 12) (hne : i ≠ j)
    (hns : ¬ ∃ k : Fin 12, rootCoords (positiveNumber k) =
      rootCoords (positiveNumber i) + rootCoords (positiveNumber j)) :
    let (w, l, r) := pairRoute i j
    l ≠ r ∧ reflectNumbers w (simpleNumber l) = positiveNumber i ∧
      reflectNumbers (w ++ [r]) (simpleNumber r) = positiveNumber j := by
  revert i j
  decide +kernel

public theorem common_signed_route (i j : Fin 12) (hne : i ≠ j)
    (hns : ¬ ∃ k : Fin 12, (typeDRootPairing 2).root (rootIndex k) =
      (typeDRootPairing 2).root (rootIndex i) + (typeDRootPairing 2).root (rootIndex j)) :
    ∃ (w : List (typeDRootPairing_base 2).support)
      (l r : (typeDRootPairing_base 2).support), l ≠ r ∧
      reflectionWord w (l : TypeDRootIndex 4) = rootIndex i ∧
      reflectionWord (w ++ [r]) (r : TypeDRootIndex 4) = rootIndex j := by
  have hns' : ¬ ∃ k : Fin 12, rootCoords (positiveNumber k) =
      rootCoords (positiveNumber i) + rootCoords (positiveNumber j) := by
    rintro ⟨k, hk⟩
    apply hns
    refine ⟨k, ?_⟩
    simp only [← positiveNumber_spec]
    apply Subtype.ext
    ext l
    have hc := congrFun hk l
    simp only [Pi.add_apply] at hc
    simp only [Submodule.coe_add, Pi.add_apply, rootCoords_spec]
    exact_mod_cast hc
  obtain ⟨hneq, hl, hr⟩ := pairRoute_checked i j hne hns'
  let w := (pairRoute i j).1
  let l := (pairRoute i j).2.1
  let r := (pairRoute i j).2.2
  change l ≠ r at hneq
  change reflectNumbers w (simpleNumber l) = positiveNumber i at hl
  change reflectNumbers (w ++ [r]) (simpleNumber r) = positiveNumber j at hr
  refine ⟨w.map (typeDRootPairing_baseEquiv 2), typeDRootPairing_baseEquiv 2 l,
    typeDRootPairing_baseEquiv 2 r, ?_, ?_, ?_⟩
  · exact (typeDRootPairing_baseEquiv 2).injective.ne hneq
  · rw [typeDRootPairing_baseEquiv_val, ← simpleNumber_spec, reflectNumbers_spec, hl,
      positiveNumber_spec]
  · rw [show w.map (typeDRootPairing_baseEquiv 2) ++ [typeDRootPairing_baseEquiv 2 r] =
      (w ++ [r]).map (typeDRootPairing_baseEquiv 2) by simp]
    rw [typeDRootPairing_baseEquiv_val, ← simpleNumber_spec, reflectNumbers_spec, hr,
      positiveNumber_spec]
end
end Triality.Standard.PositiveCoordinates.NonsumGeometry
