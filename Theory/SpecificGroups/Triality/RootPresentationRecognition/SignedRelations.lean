module

public import Theory.SpecificGroups.Triality.RootPresentationRecognition.PositiveEvaluation

/-!
# Signed rank-one interface for the triality presentation

The positive presentation is map-free.  This file adds the signed simple-root
words used by the Bruhat step, still without putting a model homomorphism in the
input.  The only algebra needed here is the characteristic-two rank-one
calculation: once the two simple Weyl words are involutions, every nonzero
negative simple root has its torus--Weyl factorisation.  The calculation is
kept at the literal cubic and fixed fields, so later transport cannot replace
the source embedding by a cardinality argument.

Source: GLS3 2.3.5 and the rank-one calculation in
`ConcreteBruhat/SplitNormalForm/RankOne.lean`.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.RootPresentationRecognition
open Parabolics PositiveCoordinates RadicalCoordinates.LeviCommutators

variable {n : ℕ} {hn : 0 < n}
local notation "P" => binaryParameters n hn

/-- Positive and negative maps for the six folded relative roots.  The negative
maps are supplied independently: no map to `BinaryCarrier` is hidden in this
presentation contract. -/
structure SignedRoots (Y : Type*) [Group Y] where
  positive : PositiveRoots n hn Y
  negativeShort : Fin 3 → Multiplicative (ExtensionField P) →* Y
  negativeLong : Fin 3 → Multiplicative (fixedField P) →* Y

namespace SignedRoots

variable {Y : Type*} [Group Y]

abbrev shortValue (L : SignedRoots (n := n) (hn := hn) Y)
    (i : Fin 3) (t : ExtensionField P) : Y := L.positive.shortValue i t

abbrev longValue (L : SignedRoots (n := n) (hn := hn) Y)
    (i : Fin 3) (t : fixedField P) : Y := L.positive.longValue i t

abbrev negativeShortValue (L : SignedRoots (n := n) (hn := hn) Y)
    (i : Fin 3) (t : ExtensionField P) : Y := L.negativeShort i (.ofAdd t)

abbrev negativeLongValue (L : SignedRoots (n := n) (hn := hn) Y)
    (i : Fin 3) (t : fixedField P) : Y := L.negativeLong i (.ofAdd t)

/-- The rank-one word at a nonzero scalar.  Units are used so that the inverse
parameter is present in the definition rather than as a side condition. -/
def nA (L : SignedRoots (n := n) (hn := hn) Y) (t : (ExtensionField P)ˣ) : Y :=
  L.shortValue 0 t.val * L.negativeShortValue 0 (t⁻¹).val *
    L.shortValue 0 t.val

def nB (L : SignedRoots (n := n) (hn := hn) Y) (t : (fixedField P)ˣ) : Y :=
  L.longValue 0 t.val * L.negativeLongValue 0 (t⁻¹).val *
    L.longValue 0 t.val

def hA (L : SignedRoots (n := n) (hn := hn) Y) (t : (ExtensionField P)ˣ) : Y :=
  L.nA t * L.nA 1

def hB (L : SignedRoots (n := n) (hn := hn) Y) (t : (fixedField P)ˣ) : Y :=
  L.nB t * L.nB 1

/-- The finite Weyl part of the signed presentation.  Conjugation and torus
characters are deliberately left as explicit hypotheses for the Bruhat owner;
these are the two finite relations that are consumed by the rank-one step. -/
structure WeylRelations (L : SignedRoots (n := n) (hn := hn) Y) : Prop where
  positiveRelations : L.positive.Relations
  nA_sq : L.nA 1 ^ 2 = 1
  nB_sq : L.nB 1 ^ 2 = 1
  braid : (L.nA 1 * L.nB 1) ^ 6 = 1

private theorem short_self (L : SignedRoots (n := n) (hn := hn) Y)
    (i : Fin 3) (t : ExtensionField P) : L.shortValue i t * L.shortValue i t = 1 := by
  calc
    L.shortValue i t * L.shortValue i t = L.shortValue i (t + t) := by
      simp only [shortValue, ← map_mul, ← ofAdd_add]
    _ = 1 := by
      rw [CharTwo.add_self_eq_zero]
      exact (L.positive.shortRoot i).map_one

private theorem long_self (L : SignedRoots (n := n) (hn := hn) Y)
    (i : Fin 3) (t : fixedField P) : L.longValue i t * L.longValue i t = 1 := by
  calc
    L.longValue i t * L.longValue i t = L.longValue i (t + t) := by
      simp only [longValue, ← map_mul, ← ofAdd_add]
    _ = 1 := by
      rw [CharTwo.add_self_eq_zero]
      exact (L.positive.longRoot i).map_one

private theorem reassoc (a b c d e : Y) :
    a * (b * c) * d * e = a * (b * c * d) * e := by
  simp only [mul_assoc]

private theorem reassoc₂ (a b c d e : Y) :
    a * b * (c * d) * e = a * (b * c) * d * e := by
  simp only [mul_assoc]

/-- The subgroup used by the rank-two Bruhat step: the collected positive
roots together with all parameterised simple Weyl words. -/
def weylClosure (L : SignedRoots (n := n) (hn := hn) Y) : Subgroup Y :=
  L.positive.positiveClosure ⊔
    Subgroup.closure (Set.range L.nA ∪ Set.range L.nB)

private theorem nA_mem_weylClosure (L : SignedRoots (n := n) (hn := hn) Y)
    (t : (ExtensionField P)ˣ) : L.nA t ∈ L.weylClosure := by
  apply Subgroup.mem_sup_right
  exact Subgroup.subset_closure (Set.mem_union_left _ ⟨t, rfl⟩)

private theorem nB_mem_weylClosure (L : SignedRoots (n := n) (hn := hn) Y)
    (t : (fixedField P)ˣ) : L.nB t ∈ L.weylClosure := by
  apply Subgroup.mem_sup_right
  exact Subgroup.subset_closure (Set.mem_union_right _ ⟨t, rfl⟩)

private theorem short_mem_positiveClosure (L : SignedRoots (n := n) (hn := hn) Y)
    (h : L.WeylRelations) (i : Fin 3) (t : ExtensionField P) :
    L.shortValue i t ∈ L.positive.positiveClosure := by
  rw [PositiveRoots.mem_positiveClosure_iff _ h.positiveRelations]
  exact ⟨(Function.update 0 i t, 0),
    L.positive.product_single_short i t⟩

private theorem long_mem_positiveClosure (L : SignedRoots (n := n) (hn := hn) Y)
    (h : L.WeylRelations) (i : Fin 3) (t : fixedField P) :
    L.longValue i t ∈ L.positive.positiveClosure := by
  rw [PositiveRoots.mem_positiveClosure_iff _ h.positiveRelations]
  exact ⟨(0, Function.update 0 i t), L.positive.product_single_long i t⟩

private theorem hA_mem_weylClosure (L : SignedRoots (n := n) (hn := hn) Y)
    (t : (ExtensionField P)ˣ) : L.hA t ∈ L.weylClosure := by
  apply Subgroup.mul_mem _ (nA_mem_weylClosure L t) (nA_mem_weylClosure L 1)

private theorem hB_mem_weylClosure (L : SignedRoots (n := n) (hn := hn) Y)
    (t : (fixedField P)ˣ) : L.hB t ∈ L.weylClosure := by
  apply Subgroup.mul_mem _ (nB_mem_weylClosure L t) (nB_mem_weylClosure L 1)

/-- Rank-one factorisation for the first short relative root. -/
theorem negativeShort_factorization (L : SignedRoots (n := n) (hn := hn) Y)
    (h : L.WeylRelations) (t : (ExtensionField P)ˣ) :
    L.negativeShortValue 0 t.val =
      L.shortValue 0 (t⁻¹).val * L.hA (t⁻¹) * L.nA 1 *
        L.shortValue 0 (t⁻¹).val := by
  let p : Y := L.shortValue 0 (t⁻¹).val
  have hp : p * p = 1 := short_self L 0 (t⁻¹).val
  have hn : L.nA 1 * L.nA 1 = 1 := by
    simpa only [pow_two] using h.nA_sq
  have hw : L.nA (t⁻¹) = p * L.negativeShortValue 0 t.val * p := by
    simp only [nA, p, inv_inv]
  calc
    L.negativeShortValue 0 t.val = p * L.nA (t⁻¹) * p := by
      rw [hw]
      simp only [← mul_assoc, hp, one_mul]
      rw [mul_assoc, hp, mul_one]
    _ = p * (L.hA (t⁻¹) * L.nA 1) * p := by
      simp only [hA]
      calc
        p * L.nA (t⁻¹) * p =
            p * L.nA (t⁻¹) * (L.nA 1 * L.nA 1) * p := by rw [hn, mul_one]
        _ = p * (L.nA (t⁻¹) * L.nA 1) * L.nA 1 * p := by
          exact reassoc₂ p (L.nA (t⁻¹)) (L.nA 1) (L.nA 1) p
        _ = p * (L.nA (t⁻¹) * L.nA 1 * L.nA 1) * p := by
          exact reassoc p (L.nA (t⁻¹)) (L.nA 1) (L.nA 1) p
    _ = p * L.hA (t⁻¹) * L.nA 1 * p := by simp only [mul_assoc]
    _ = _ := rfl

/-- The two negative simple-root ranges lie in the positive--Weyl closure.
This is the exact local input needed when a Bruhat collector changes sign. -/
theorem negativeShort_mem_weylClosure (L : SignedRoots (n := n) (hn := hn) Y)
    (h : L.WeylRelations) (t : (ExtensionField P)ˣ) :
    L.negativeShortValue 0 t.val ∈ L.weylClosure := by
  rw [negativeShort_factorization L h t]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (Subgroup.mem_sup_left (short_mem_positiveClosure L h 0 (t⁻¹).val))
        (hA_mem_weylClosure L (t⁻¹)))
      (nA_mem_weylClosure L 1))
    (Subgroup.mem_sup_left (short_mem_positiveClosure L h 0 (t⁻¹).val))

/-- Rank-one factorisation for the first long relative root. -/
theorem negativeLong_factorization (L : SignedRoots (n := n) (hn := hn) Y)
    (h : L.WeylRelations) (t : (fixedField P)ˣ) :
    L.negativeLongValue 0 t.val =
      L.longValue 0 (t⁻¹).val * L.hB (t⁻¹) * L.nB 1 *
        L.longValue 0 (t⁻¹).val := by
  let p : Y := L.longValue 0 (t⁻¹).val
  have hp : p * p = 1 := long_self L 0 (t⁻¹).val
  have hn : L.nB 1 * L.nB 1 = 1 := by
    simpa only [pow_two] using h.nB_sq
  have hw : L.nB (t⁻¹) = p * L.negativeLongValue 0 t.val * p := by
    simp only [nB, p, inv_inv]
  calc
    L.negativeLongValue 0 t.val = p * L.nB (t⁻¹) * p := by
      rw [hw]
      simp only [← mul_assoc, hp, one_mul]
      rw [mul_assoc, hp, mul_one]
    _ = p * (L.hB (t⁻¹) * L.nB 1) * p := by
      simp only [hB]
      calc
        p * L.nB (t⁻¹) * p =
            p * L.nB (t⁻¹) * (L.nB 1 * L.nB 1) * p := by rw [hn, mul_one]
        _ = p * (L.nB (t⁻¹) * L.nB 1) * L.nB 1 * p := by
          exact reassoc₂ p (L.nB (t⁻¹)) (L.nB 1) (L.nB 1) p
        _ = p * (L.nB (t⁻¹) * L.nB 1 * L.nB 1) * p := by
          exact reassoc p (L.nB (t⁻¹)) (L.nB 1) (L.nB 1) p
    _ = p * L.hB (t⁻¹) * L.nB 1 * p := by simp only [mul_assoc]
    _ = _ := rfl

theorem negativeLong_mem_weylClosure (L : SignedRoots (n := n) (hn := hn) Y)
    (h : L.WeylRelations) (t : (fixedField P)ˣ) :
    L.negativeLongValue 0 t.val ∈ L.weylClosure := by
  rw [negativeLong_factorization L h t]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (Subgroup.mem_sup_left (long_mem_positiveClosure L h 0 (t⁻¹).val))
        (hB_mem_weylClosure L (t⁻¹)))
      (nB_mem_weylClosure L 1))
    (Subgroup.mem_sup_left (long_mem_positiveClosure L h 0 (t⁻¹).val))

end SignedRoots
end Triality.Standard.RootPresentationRecognition
