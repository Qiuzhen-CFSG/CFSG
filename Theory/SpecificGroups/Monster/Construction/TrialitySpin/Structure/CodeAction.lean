/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Generators

/-!
# The faithful marked Golay action

Coordinate permutations restrict to linear automorphisms of the concrete Golay
code. Minimum weight eight implies that its coordinate evaluations separate
points, so this code action is faithful. This is the concrete quotient action
used for the standard automorphisms in Aschbacher, Sections 14 and 27.

Adapted from Gerald Höhn, ATLAS, `Atlas/Fischer/ParkerCodeAction.lean`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Changes: CFSG module imports, local triality namespace, Lean 4.33 proof syntax,
and compatibility with the existing concrete `IsStandard` predicate.
-/

@[expose] public section

namespace Sporadic.Monster.Construction.TrialitySpin
open Atlas.Fischer Atlas.Codes
open scoped BigOperators

def parkerCodeEquiv (g : Mathieu24CodeModel) : golay ≃ₗ[Bit] golay where
  toFun a := ⟨coordinatePermutation g.val a.val, (g.property a.val).mp a.property⟩
  invFun a := ⟨coordinatePermutation g.val⁻¹ a.val,
    ((g⁻¹).property a.val).mp a.property⟩
  left_inv a := by
    apply Subtype.ext
    change coordinatePermutation g.val⁻¹ (coordinatePermutation g.val a.val) = a.val
    rw [← coordinatePermutation_mul, inv_mul_cancel, coordinatePermutation_one]
  right_inv a := by
    apply Subtype.ext
    change coordinatePermutation g.val (coordinatePermutation g.val⁻¹ a.val) = a.val
    rw [← coordinatePermutation_mul, mul_inv_cancel, coordinatePermutation_one]
  map_add' a b := by apply Subtype.ext; exact map_add _ _ _
  map_smul' r a := by apply Subtype.ext; exact map_smul _ _ _

@[simp] theorem parkerCodeEquiv_coe (g : Mathieu24CodeModel) (a : golay) :
    (parkerCodeEquiv g a : BinaryWord) = coordinatePermutation g.val a.val := rfl

theorem parkerCodeEquiv_weight (g : Mathieu24CodeModel) (a : golay) :
    hammingNorm (parkerCodeEquiv g a : BinaryWord) = hammingNorm a.val :=
  coordinatePermutation_weight g.val a.val

theorem parkerCodeEquiv_triple (g : Mathieu24CodeModel) (a b c : golay) :
    parkerTripleIntersection (parkerCodeEquiv g a) (parkerCodeEquiv g b)
      (parkerCodeEquiv g c) = parkerTripleIntersection a b c := by
  exact Equiv.sum_comp g.val.symm (fun p => a.val p * b.val p * c.val p)

@[simp] theorem parkerCodeEquiv_one (a : golay) : parkerCodeEquiv 1 a = a := by
  apply Subtype.ext
  rfl

theorem parkerCodeEquiv_mul (g h : Mathieu24CodeModel) (a : golay) :
    parkerCodeEquiv (g * h) a = parkerCodeEquiv g (parkerCodeEquiv h a) := by
  apply Subtype.ext
  rfl

theorem parkerGolay_coordinates_separate (p q : Omega)
    (h : ∀ a : golay, a.val p = a.val q) : p = q := by
  classical
  by_contra hpq
  let w : BinaryWord := Pi.single p 1 + Pi.single q 1
  have hw : w ∈ golay := by
    rw [golay_selfDual]
    intro a ha
    have he := h ⟨a, ha⟩
    change a p = a q at he
    have hb : ∀ x : Bit, x + x = 0 := by decide
    simp [w, binaryDot_apply, mul_add, Pi.single_apply, mul_ite,
      Finset.sum_add_distrib, he, hb]
  have hw0 : w ≠ 0 := by
    intro hz
    have he := congrFun hz p
    simp [w, hpq] at he
  have hbound := binary_weight_add (Pi.single p 1 : BinaryWord) (Pi.single q 1)
  have hsingle : ∀ r : Omega, hammingNorm (Pi.single r (1 : Bit) : BinaryWord) = 1 := by
    intro r
    simp [hammingNorm, Pi.single_apply]
    have he : (Finset.univ.filter (fun x : Omega => x = r)) = {r} := by ext; simp
    rw [he]
    rfl
  rw [hsingle p, hsingle q] at hbound
  have hmin := golay_minimum w hw hw0
  change 8 ≤ hammingNorm ((Pi.single p (1 : Bit) : BinaryWord) + Pi.single q 1) at hmin
  omega

theorem parkerCodeEquiv_faithful (g h : Mathieu24CodeModel)
    (he : ∀ a, parkerCodeEquiv g a = parkerCodeEquiv h a) : g = h := by
  apply Subtype.ext
  apply inv_injective
  apply Equiv.ext
  intro p
  apply parkerGolay_coordinates_separate
  intro a
  exact congrArg (fun z : golay => z.val p) (he a)

/-- The actual Golay permutation group is faithful even after dividing out the
all-ones line, as required by the hypothesis of Aschbacher's Section 14. -/
theorem parkerCodeEquiv_faithful_mod_golayOne (g h : Mathieu24CodeModel)
    (he : ∀ a : golay, ∃ t : Bit, parkerCodeEquiv g a = parkerCodeEquiv h a + t • golayOne) :
    g = h := by
  have hb (i : Fin 12) : parkerCodeEquiv g (golayBasis i) = parkerCodeEquiv h (golayBasis i) := by
    obtain ⟨t,ht⟩ := he (golayBasis i)
    have hbit : ∀ t : Bit, t = 0 ∨ t = 1 := by decide
    rcases hbit t with rfl | rfl
    · simpa using ht
    · have hwg := parkerCodeEquiv_weight g (golayBasis i)
      have hwh := parkerCodeEquiv_weight h (golayBasis i)
      have hcomp := complement_weight (parkerCodeEquiv h (golayBasis i)).val
      have hbase := golay_octad_basis.2 i
      have hv : (parkerCodeEquiv g (golayBasis i)).val =
          (parkerCodeEquiv h (golayBasis i)).val + allOnes := by
        simpa only [one_smul, Submodule.coe_add, golayOne] using congrArg Subtype.val ht
      rw [← hv] at hcomp
      omega
  apply parkerCodeEquiv_faithful
  intro a
  calc
    parkerCodeEquiv g a = parkerCodeEquiv g (∑ i, golayBasis.repr a i • golayBasis i) :=
      congrArg (parkerCodeEquiv g) (golayBasis.sum_repr a).symm
    _ = parkerCodeEquiv h (∑ i, golayBasis.repr a i • golayBasis i) := by
      simp only [map_sum, map_smul, hb]
    _ = parkerCodeEquiv h a := congrArg (parkerCodeEquiv h) (golayBasis.sum_repr a)

end Sporadic.Monster.Construction.TrialitySpin
