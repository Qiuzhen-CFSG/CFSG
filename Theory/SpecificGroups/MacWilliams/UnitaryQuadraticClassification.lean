module

public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticCoordinates
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticCertificate
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# The balanced anisotropic quadratic normal form

Cardinalities sixteen and four identify the two elementary abelian groups with
binary coordinate spaces. The quadratic laws give ten coefficients, and an
explicit equivalence of fibres preserves the balanced five-to-one condition.
A frame for the coefficient polynomial then transports to the original groups,
including both generation requirements and every square and polar equation.

`exists_unitaryQuadraticFrame_of_coefficient_classification` isolates the finite
classification premise. The kernel-checked coordinate certificate discharges
this premise in `exists_unitaryQuadraticFrame`, establishing the normal form
with no additional classification hypothesis.

This is the quadratic normal-form step for MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3, used in Janko–Thompson,
Math. Z. 113 (1970), Theorem 1.3(b), printed p.386.
-/

open scoped IsMulCommutative

namespace MacWilliamsSylow

private theorem coordinates_equiv {V : Type*} [Group V] [Finite V]
    [IsElementaryAbelian 2 V] {n : ℕ} (hV : Nat.card V = 2 ^ n) :
    Nonempty (V ≃* BinaryCoordinates n) := by
  classical
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive V) = 2 ^ n := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    change Nat.card V = _ at hsize
    simpa only [Nat.card_zmod, hV] using hsize.symm
  have hdim : Module.finrank (ZMod 2) (Additive V) = n :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive V) hdim
  exact ⟨b.equivFun.toAddEquiv.toMultiplicativeRight⟩

private theorem closure_range_equiv {G H : Type*} [Group G] [Group H]
    {n : ℕ} (e : G ≃* H) (v : Fin n → G)
    (hv : Subgroup.closure (Set.range v) = ⊤) :
    Subgroup.closure (Set.range fun i => e (v i)) = ⊤ := by
  rw [Set.range_comp']
  change Subgroup.closure (e.toMonoidHom '' Set.range v) = ⊤
  rw [← MonoidHom.map_closure, hv]
  exact Subgroup.map_top_of_surjective _ e.surjective

/-- Transport a quadratic frame through compatible group equivalences. -/
public def UnitaryQuadraticFrame.of_mulEquiv
    {V₀ W₀ V W : Type*} [Group V₀] [Group W₀] [Group V] [Group W]
    {square₀ : V₀ → W₀} {polar₀ : V₀ → V₀ → W₀}
    {square : V → W} {polar : V → V → W}
    (f : UnitaryQuadraticFrame square₀ polar₀)
    (eV : V₀ ≃* V) (eW : W₀ ≃* W)
    (hs : ∀ x, square (eV x) = eW (square₀ x))
    (hp : ∀ x y, polar (eV x) (eV y) = eW (polar₀ x y)) :
    UnitaryQuadraticFrame square polar where
  quotientGenerator i := eV (f.quotientGenerator i)
  centralGenerator i := eW (f.centralGenerator i)
  quotient_last i hi := by rw [f.quotient_last i hi, map_one]
  central_first i hi := by rw [f.central_first i hi, map_one]
  quotient_closure := closure_range_equiv eV _ f.quotient_closure
  central_closure := closure_range_equiv eW _ f.central_closure
  square_eq i := by
    rw [hs, f.square_eq]
    exact map_word eW.toMonoidHom _ _
  polar_eq i j hij := by
    rw [hp, f.polar_eq i j hij]
    exact map_word eW.toMonoidHom _ _

/-- The normal form for arbitrary elementary abelian groups follows from the
finite classification of the ten-coefficient coordinate polynomials. -/
public theorem exists_unitaryQuadraticFrame_of_coefficient_classification
    (hclassification : ∀ c : QuadraticCoefficients,
      (∀ x, coordinateSquare c x = 1 → x = 1) →
      (∀ z : BinaryCoordinates 2, z ≠ 1 →
        Nat.card {v : BinaryCoordinates 4 // coordinateSquare c v = z} = 5) →
      Nonempty (UnitaryQuadraticFrame (coordinateSquare c) (coordinatePolar c)))
    {V W : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hV : Nat.card V = 16) (hW : Nat.card W = 4)
    (square : V → W) (polar : V → V → W)
    (hone : square 1 = 1)
    (hquadratic : ∀ x y, square (x * y) = square x * square y * polar x y)
    (hbilinear : ∀ x y z, polar (x * y) z = polar x z * polar y z)
    (hanisotropic : ∀ x, square x = 1 → x = 1)
    (hbalanced : ∀ z : W, z ≠ 1 → Nat.card {v : V // square v = z} = 5) :
    Nonempty (UnitaryQuadraticFrame square polar) := by
  obtain ⟨eV⟩ := coordinates_equiv (n := 4) hV
  obtain ⟨eW⟩ := coordinates_equiv (n := 2) hW
  let q : BinaryCoordinates 4 → BinaryCoordinates 2 := fun x => eW (square (eV.symm x))
  let p : BinaryCoordinates 4 → BinaryCoordinates 4 → BinaryCoordinates 2 :=
    fun x y => eW (polar (eV.symm x) (eV.symm y))
  have hq1 : q 1 = 1 := by simp [q, hone]
  have hqp (x y : BinaryCoordinates 4) : q (x * y) = q x * q y * p x y := by
    simp only [q, p, map_mul, hquadratic]
  have hpp (x y z : BinaryCoordinates 4) : p (x * y) z = p x z * p y z := by
    simp only [p, map_mul, hbilinear]
  have hqa (x : BinaryCoordinates 4) (hx : q x = 1) : x = 1 := by
    have h := hanisotropic (eV.symm x) (eW.map_eq_one_iff.mp hx)
    exact eV.symm.map_eq_one_iff.mp h
  have hqb (z : BinaryCoordinates 2) (hz : z ≠ 1) :
      Nat.card {v : BinaryCoordinates 4 // q v = z} = 5 := by
    have hcard : Nat.card {v : V // square v = eW.symm z} = 5 :=
      hbalanced _ (fun h => hz (eW.symm.map_eq_one_iff.mp h))
    let e : {v : BinaryCoordinates 4 // q v = z} ≃ {v : V // square v = eW.symm z} :=
      eV.symm.toEquiv.subtypeEquiv (fun x => by
        change eW (square (eV.symm x)) = z ↔ square (eV.symm x) = eW.symm z
        exact eW.eq_symm_apply.symm)
    exact (Nat.card_congr e).trans hcard
  obtain ⟨c, hqc, hpc⟩ := exists_quadratic_coefficients q p hq1 hqp hpp
  obtain ⟨f⟩ := hclassification c (hqc ▸ hqa) (hqc ▸ hqb)
  refine ⟨f.of_mulEquiv eV.symm eW.symm ?_ ?_⟩
  · intro x
    rw [← hqc]
    exact (eW.symm_apply_apply _).symm
  · intro x y
    rw [← hpc]
    exact (eW.symm_apply_apply _).symm

/-- Every balanced anisotropic quadratic map from an elementary abelian group
of order sixteen to one of order four admits the unitary frame. The frame
includes the exact six-generator square and polar equations and generation
of both groups. -/
public theorem exists_unitaryQuadraticFrame
    {V W : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hV : Nat.card V = 16) (hW : Nat.card W = 4)
    (square : V → W) (polar : V → V → W)
    (hone : square 1 = 1)
    (hquadratic : ∀ x y, square (x * y) = square x * square y * polar x y)
    (hbilinear : ∀ x y z, polar (x * y) z = polar x z * polar y z)
    (hanisotropic : ∀ x, square x = 1 → x = 1)
    (hbalanced : ∀ z : W, z ≠ 1 → Nat.card {v : V // square v = z} = 5) :
    Nonempty (UnitaryQuadraticFrame square polar) :=
  exists_unitaryQuadraticFrame_of_coefficient_classification
    coordinate_unitaryQuadraticFrame hV hW square polar hone hquadratic hbilinear
    hanisotropic hbalanced

end MacWilliamsSylow
