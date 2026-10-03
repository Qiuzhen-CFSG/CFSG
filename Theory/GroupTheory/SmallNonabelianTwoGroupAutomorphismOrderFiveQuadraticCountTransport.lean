module

public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Pi

namespace SmallNonabelianTwoGroup

open scoped IsMulCommutative

private theorem binary_coordinates
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (dimension : ℕ) (hcard : Nat.card V = 2 ^ dimension) :
    Nonempty (Additive V ≃ₗ[ZMod 2] (Fin dimension → ZMod 2)) := by
  classical
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive V) = 2 ^ dimension := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    change Nat.card V = _ at hsize
    simpa only [Nat.card_zmod, hcard] using hsize.symm
  have hdim : Module.finrank (ZMod 2) (Additive V) = dimension :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  exact ⟨(Module.finBasisOfFinrankEq (ZMod 2) (Additive V) hdim).equivFun⟩

public theorem exists_quadratic_coordinate_model
    {V W : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hV : Nat.card V = 16) (hW : Nat.card W = 2)
    (square : V → W) (polar : V → V → W)
    (hone : square 1 = 1)
    (hquadratic : ∀ left right,
      square (left * right) = square left * square right * polar left right)
    (hbilinear : ∀ left right other,
      polar (left * right) other = polar left other * polar right other)
    (hnonzero : ∃ left right, polar left right ≠ 1)
    (singular : Subgroup V) (hsingularCard : 4 ≤ Nat.card singular)
    (hsingular : ∀ vector ∈ singular, square vector = 1) :
    ∃ (coordinateSquare : (Fin 4 → ZMod 2) → ZMod 2)
      (coordinatePolar : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) → ZMod 2)
      (coordinateSingular : AddSubgroup (Fin 4 → ZMod 2)),
      coordinateSquare 0 = 0 ∧
      (∀ left right, coordinateSquare (left + right) =
        coordinateSquare left + coordinateSquare right + coordinatePolar left right) ∧
      (∀ left right other, coordinatePolar (left + right) other =
        coordinatePolar left other + coordinatePolar right other) ∧
      (∃ left right, coordinatePolar left right ≠ 0) ∧
      4 ≤ Nat.card coordinateSingular ∧
      (∀ vector ∈ coordinateSingular, coordinateSquare vector = 0) ∧
      Nat.card {vector : V // square vector = 1} =
        Nat.card {vector : Fin 4 → ZMod 2 // coordinateSquare vector = 0} := by
  classical
  obtain ⟨domainCoordinates⟩ := binary_coordinates 4 hV
  obtain ⟨codomainBasis⟩ := binary_coordinates 1 (by simpa using hW)
  let codomainCoordinates : Additive W ≃ₗ[ZMod 2] ZMod 2 :=
    codomainBasis.trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) (ZMod 2))
  let coordinateSquare : (Fin 4 → ZMod 2) → ZMod 2 :=
    fun vector => codomainCoordinates (Additive.ofMul (square (domainCoordinates.symm vector).toMul))
  let coordinatePolar : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) → ZMod 2 :=
    fun left right => codomainCoordinates
      (Additive.ofMul (polar (domainCoordinates.symm left).toMul
        (domainCoordinates.symm right).toMul))
  let coordinateSingular : AddSubgroup (Fin 4 → ZMod 2) :=
    singular.toAddSubgroup.map domainCoordinates.toAddEquiv.toAddMonoidHom
  refine ⟨coordinateSquare, coordinatePolar, coordinateSingular, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [coordinateSquare, map_zero, toMul_zero, hone, ofMul_one]
  · intro left right
    simp only [coordinateSquare, coordinatePolar, map_add, toMul_add,
      hquadratic, ofMul_mul]
  · intro left right other
    simp only [coordinatePolar, map_add, toMul_add, hbilinear, ofMul_mul]
  · obtain ⟨left, right, hpair⟩ := hnonzero
    refine ⟨domainCoordinates (Additive.ofMul left), domainCoordinates (Additive.ofMul right), ?_⟩
    simp only [coordinatePolar, LinearEquiv.symm_apply_apply, toMul_ofMul]
    exact fun heq => hpair (codomainCoordinates.map_eq_zero_iff.mp heq)
  · have hcard := Nat.card_congr
      (singular.toAddSubgroup.equivMapOfInjective
        domainCoordinates.toAddEquiv.toAddMonoidHom domainCoordinates.injective).toEquiv
    change Nat.card singular = Nat.card coordinateSingular at hcard
    omega
  · intro vector hvector
    obtain ⟨original, horiginal, rfl⟩ := hvector
    change codomainCoordinates (Additive.ofMul
      (square (domainCoordinates.symm (domainCoordinates original)).toMul)) = 0
    rw [LinearEquiv.symm_apply_apply, hsingular original.toMul horiginal, ofMul_one]
    exact map_zero codomainCoordinates
  · let zeroEquiv : {vector : V // square vector = 1} ≃
        {vector : Fin 4 → ZMod 2 // coordinateSquare vector = 0} :=
      (Additive.ofMul.trans domainCoordinates.toEquiv).subtypeEquiv (by
        intro vector
        change square vector = 1 ↔
          codomainCoordinates (Additive.ofMul (square
            (domainCoordinates.symm (domainCoordinates (Additive.ofMul vector))).toMul)) = 0
        rw [LinearEquiv.symm_apply_apply, toMul_ofMul]
        exact codomainCoordinates.map_eq_zero_iff.symm)
    exact Nat.card_congr zeroEquiv

end SmallNonabelianTwoGroup
