module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ChevalleyCorootWords
public import Theory.AlgebraicGroup.ClosedSubgroup.Maximal
public import Theory.AlgebraicGroup.Morphism.ClosedEmbedding
public import Theory.AlgebraicGroup.Tori.Character.Image
public import Theory.AlgebraicGroup.Tori.Character.Laurent
public import Theory.AlgebraicGroup.Tori.Character.Regular
public import Theory.AlgebraicGroup.Tori.Power

/-!
# The concrete rank-four split torus of F4

The integral Chevalley diagonal matrices give a regular morphism from `D₄`.
Their simple-coroot factors are root words, so this morphism lands in the
closed root-generated F4 carrier. The inverse Cartan matrix recovers all four
parameters regularly from the simple-root diagonal entries. This proves an
isomorphism onto the closed image, including in characteristics two and three.
Characters and cocharacters are exported in these coordinates, as is a maximal
torus containing the image.

Source: Steinberg, *Lectures on Chevalley Groups*, Theorem 1 and Lemmas 5–6;
the algebraic-group construction follows `G2ChevalleyCarrier`.
-/

open scoped BigOperators Matrix
universe u
@[expose] public noncomputable section
namespace Theory.AlgebraicGroup.F4Chevalley
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
variable {k : Type u} [Field k] [IsAlgClosed k]

abbrev carrierBasis := RootPairing.IntegralGeckConstruction.carrierBasis
  (P := typeF4RootPairing) (b := typeF4RootPairing_base) (k := k)
abbrev carrierIndexEquiv := RootPairing.IntegralGeckConstruction.carrierIndexEquiv
  (P := typeF4RootPairing) (b := typeF4RootPairing_base) (k := k)

/-- Numbered simple-coroot parameters, in the standard F4 base order. -/
def torusParameter (u : Fin 4 → kˣ) : typeF4RootPairing_base.support → kˣ :=
  fun q => u (typeF4RootPairing_baseEquiv.symm q)

abbrev torusElement (u : Fin 4 → kˣ) :=
  integralChevalleyTorusElement (P := typeF4RootPairing) (torusParameter u)
abbrev basisTorusUnit (u : Fin 4 → kˣ) (a : BasisIndex) :=
  chevalleyBasisTorusUnit (P := typeF4RootPairing) (torusParameter u) a

def basisWeight (a : BasisIndex) (i : Fin 4) : ℤ :=
  chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4RootPairing_baseEquiv i)

def torusWeightExponent (a : BasisIndex) (i : Fin 4) : ℤ := -basisWeight a i

omit [IsAlgClosed k] in
lemma basisTorusUnit_formula (u : Fin 4 → kˣ) (a : BasisIndex) :
    basisTorusUnit u a = ∏ i, u i ^ (-basisWeight a i) := by
  rw [basisTorusUnit, chevalleyBasisTorusUnit, ← typeF4RootPairing_baseEquiv.prod_comp]
  simp only [torusParameter, Equiv.symm_apply_apply, basisWeight]

omit [IsAlgClosed k] in
lemma torusElement_one : torusElement (k := k) 1 = 1 :=
  integralChevalleyTorusElement_one

omit [IsAlgClosed k] in
lemma torusElement_mul (u v : Fin 4 → kˣ) :
    torusElement (u * v) = torusElement u * torusElement v :=
  integralChevalleyTorusElement_mul _ _

public noncomputable def torusPointRepresentation :
    Variety.Point (dVariety k 4) →* LinearMap.GeneralLinearGroup k (BasisIndex → k) where
  toFun := fun x => Matrix.GeneralLinearGroup.toLin (torusElement (dPointEquiv 4 x))
  map_one' := by
    simp [dPointEquiv_one, torusElement_one]
  map_mul' := by
    intro x y
    simp only [dPointEquiv_mul, torusElement_mul, map_mul]

public noncomputable def torusCharacter (b : BasisIndex) : TorusCharacter (dVariety k 4) :=
  dLaurentCharacter 4 (torusWeightExponent b)

public noncomputable def torusInverseCharacter (b : BasisIndex) : TorusCharacter (dVariety k 4) :=
  dLaurentCharacter 4 (basisWeight b)

omit [IsAlgClosed k] in
public lemma torusCharacter_scalar_apply (b : BasisIndex)
    (x : Variety.Point (dVariety k 4)) :
    (torusCharacter b).scalarPolynomialFunction x =
      (basisTorusUnit (dPointEquiv 4 x) b : k) := by
  rw [TorusCharacter.scalarPolynomialFunction_apply]
  rw [torusCharacter, TorusCharacter.pointCharacter_dLaurentCharacter]
  exact congrArg Units.val (basisTorusUnit_formula _ _).symm

omit [IsAlgClosed k] in
public lemma torusInverseCharacter_scalar_apply (b : BasisIndex)
    (x : Variety.Point (dVariety k 4)) :
    (torusInverseCharacter b).scalarPolynomialFunction x =
      ((basisTorusUnit (dPointEquiv 4 x) b)⁻¹ : kˣ) := by
  rw [TorusCharacter.scalarPolynomialFunction_apply]
  rw [torusInverseCharacter, TorusCharacter.pointCharacter_dLaurentCharacter]
  rw [basisTorusUnit_formula]
  change (↑(∏ i, (dPointEquiv 4 x i) ^ basisWeight b i) : k) =
    (↑((∏ i, (dPointEquiv 4 x i) ^ (-basisWeight b i))⁻¹) : k)
  apply congrArg Units.val
  calc
    ∏ i, (dPointEquiv 4 x i) ^ basisWeight b i =
        ∏ i, ((dPointEquiv 4 x i) ^ (-basisWeight b i))⁻¹ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [zpow_neg, inv_inv]
    _ = (∏ i, (dPointEquiv 4 x i) ^ (-basisWeight b i))⁻¹ := by
      simpa only [Finset.mem_univ, and_true] using
        (Finset.prod_inv_distrib
          (s := Finset.univ) (fun i => (dPointEquiv 4 x i) ^ (-basisWeight b i)))

public noncomputable def torusMatrixCoefficient
    (i j : Fin (Module.finrank k (BasisIndex → k))) :
    (dVariety k 4).PolynomialFunction :=
  if i = j then
    (torusCharacter ((carrierIndexEquiv (k := k)).symm.toFun i)).scalarPolynomialFunction
  else 0

public noncomputable def torusInverseMatrixCoefficient
    (i j : Fin (Module.finrank k (BasisIndex → k))) :
    (dVariety k 4).PolynomialFunction :=
  if i = j then
    (torusInverseCharacter
      ((carrierIndexEquiv (k := k)).symm.toFun i)).scalarPolynomialFunction
  else 0

omit [IsAlgClosed k] in
public lemma torusMatrixCoefficient_apply
    (i j : Fin (Module.finrank k (BasisIndex → k))) (x : Variety.Point (dVariety k 4)) :
    torusMatrixCoefficient i j x =
      (carrierBasis (k := k)).repr
        (((torusPointRepresentation x : LinearMap.GeneralLinearGroup k (BasisIndex → k)) :
          Module.End k (BasisIndex → k)) ((carrierBasis (k := k)) j)) i := by
  by_cases hij : i = j
  · subst j
    rw [torusMatrixCoefficient, if_pos rfl, torusCharacter_scalar_apply]
    simp [torusPointRepresentation, carrierBasis, Module.Basis.reindex_apply,
      torusElement, integralChevalleyTorusElement,
      RootPairing.IntegralGeckConstruction.carrierBasis]
  · have hidx : (carrierIndexEquiv (k := k)).symm i ≠
        (carrierIndexEquiv (k := k)).symm j := by
      exact fun h => hij ((carrierIndexEquiv (k := k)).symm.injective h)
    rw [torusMatrixCoefficient, if_neg hij]
    simp [torusPointRepresentation, carrierBasis, Module.Basis.reindex_apply,
      torusElement, integralChevalleyTorusElement,
      RootPairing.IntegralGeckConstruction.carrierBasis, hidx]

omit [IsAlgClosed k] in
public lemma torusPointRepresentation_inv_coefficient
    (i j : Fin (Module.finrank k (BasisIndex → k))) (x : Variety.Point (dVariety k 4)) :
    (carrierBasis (k := k)).repr
        (((((torusPointRepresentation x)⁻¹ : LinearMap.GeneralLinearGroup k (BasisIndex → k)) :
          Module.End k (BasisIndex → k)) ((carrierBasis (k := k)) j))) i =
      if i = j then
        (((basisTorusUnit (dPointEquiv 4 x)
          ((carrierIndexEquiv (k := k)).symm i))⁻¹ : kˣ) : k)
      else 0 := by
  change (carrierBasis (k := k)).repr
      (((((Matrix.GeneralLinearGroup.toLin (torusElement (dPointEquiv 4 x)))⁻¹ :
        LinearMap.GeneralLinearGroup k (BasisIndex → k)) : Module.End k (BasisIndex → k))
        ((carrierBasis (k := k)) j))) i = _
  have hinv :
      (Matrix.GeneralLinearGroup.toLin (torusElement (dPointEquiv 4 x)))⁻¹ =
        Matrix.GeneralLinearGroup.toLin ((torusElement (dPointEquiv 4 x))⁻¹) :=
    ((Matrix.GeneralLinearGroup.toLin (n := BasisIndex) (R := k)).map_inv _).symm
  rw [hinv]
  by_cases hij : i = j
  · subst j
    simp [carrierBasis, Module.Basis.reindex_apply, torusElement,
      integralChevalleyTorusElement, RootPairing.IntegralGeckConstruction.carrierBasis]
  · have hidx : (carrierIndexEquiv (k := k)).symm i ≠
        (carrierIndexEquiv (k := k)).symm j := by
      exact fun h => hij ((carrierIndexEquiv (k := k)).symm.injective h)
    simp [hij, carrierBasis, Module.Basis.reindex_apply,
      torusElement, integralChevalleyTorusElement,
      RootPairing.IntegralGeckConstruction.carrierBasis, hidx]

omit [IsAlgClosed k] in
public lemma torusInverseMatrixCoefficient_apply
    (i j : Fin (Module.finrank k (BasisIndex → k))) (x : Variety.Point (dVariety k 4)) :
    torusInverseMatrixCoefficient i j x =
      (carrierBasis (k := k)).repr
        (((((torusPointRepresentation x)⁻¹ : LinearMap.GeneralLinearGroup k (BasisIndex → k)) :
          Module.End k (BasisIndex → k)) ((carrierBasis (k := k)) j))) i := by
  by_cases hij : i = j
  · subst j
    rw [torusInverseMatrixCoefficient, if_pos rfl, torusInverseCharacter_scalar_apply]
    rw [torusPointRepresentation_inv_coefficient, if_pos rfl]
    rfl
  ·
    rw [torusInverseMatrixCoefficient, if_neg hij]
    rw [torusPointRepresentation_inv_coefficient, if_neg hij]
    rfl

public noncomputable def torusAmbientMorphism :
    AlgebraicGroup.Morphism (dVariety k 4) (Ambient k) := by
  simpa [Ambient] using
    generalLinearRepresentationMorphismOfInverseMatrixCoefficient
      (carrierBasis (k := k)) torusPointRepresentation
      torusMatrixCoefficient torusInverseMatrixCoefficient
      torusMatrixCoefficient_apply torusInverseMatrixCoefficient_apply

@[simp]
public lemma torusAmbientMorphism_apply (x : Variety.Point (dVariety k 4)) :
    torusAmbientMorphism.onPoints x =
      generalLinearRepresentationPoint (carrierBasis (k := k))
        (torusPointRepresentation x) := by
  rw [torusAmbientMorphism]
  exact generalLinearRepresentationMorphismOfInverseMatrixCoefficient_apply
    (carrierBasis (k := k)) torusPointRepresentation
    torusMatrixCoefficient torusInverseMatrixCoefficient
    torusMatrixCoefficient_apply torusInverseMatrixCoefficient_apply x

/-- The closed image of the four-parameter morphism in the ambient linear group. -/
def ambientSplitTorus : ClosedSubgroup (Ambient k) :=
  torusAmbientMorphism.imageClosedSubgroup

theorem ambientSplitTorus_isSubtorus : IsSubtorus (ambientSplitTorus (k := k)) :=
  morphism_image_isTorus torusAmbientMorphism (dVariety_isTorus 4)

public lemma ambientTorus_mem_carrier (x : Variety.Point (dVariety k 4)) :
    torusAmbientMorphism.onPoints x ∈ ambientCarrierSubgroup (k := k) := by
  rw [torusAmbientMorphism_apply]
  exact matrixToAmbient_torus_mem (torusParameter (dPointEquiv 4 x))

public noncomputable def splitTorusMorphism :
    AlgebraicGroup.Morphism (dVariety k 4) (Carrier (k := k)) :=
  torusAmbientMorphism.codRestrictClosedSubgroup ambientClosedCarrier
    ambientTorus_mem_carrier

@[simp]
public lemma splitTorusMorphism_inclusion_apply
    (x : Variety.Point (dVariety k 4)) :
    (ambientClosedCarrier (k := k)).inclusion.onPoints
        (splitTorusMorphism.onPoints x) =
      torusAmbientMorphism.onPoints x :=
  torusAmbientMorphism.codRestrictClosedSubgroup_inclusion_apply
    ambientClosedCarrier ambientTorus_mem_carrier x

public noncomputable def splitTorus : ClosedSubgroup (Carrier (k := k)) :=
  splitTorusMorphism.imageClosedSubgroup

public theorem splitTorus_isSubtorus : IsSubtorus (splitTorus (k := k)) :=
  morphism_image_isTorus splitTorusMorphism (dVariety_isTorus 4)

/-! ## Explicit coordinates on the split torus -/

omit [IsAlgClosed k] in
private lemma basisTorusUnit_inv (u : Fin 4 → kˣ) (b : BasisIndex) :
    basisTorusUnit u⁻¹ b = (basisTorusUnit u b)⁻¹ :=
  chevalleyBasisTorusUnit_inv _ _

omit [IsAlgClosed k] in
private lemma dPointEquiv_inv_local (n : ℕ)
    (x : Variety.Point (dVariety k n)) :
    dPointEquiv n x⁻¹ = (dPointEquiv n x)⁻¹ := by
  have h := dPointEquiv_mul n x⁻¹ x
  rw [inv_mul_cancel, dPointEquiv_one] at h
  calc
    dPointEquiv n x⁻¹ = dPointEquiv n x⁻¹ * 1 := (mul_one _).symm
    _ = dPointEquiv n x⁻¹ * (dPointEquiv n x * (dPointEquiv n x)⁻¹) := by
      rw [mul_inv_cancel]
    _ = (dPointEquiv n x⁻¹ * dPointEquiv n x) * (dPointEquiv n x)⁻¹ := by
      rw [mul_assoc]
    _ = 1 * (dPointEquiv n x)⁻¹ := by rw [← h]
    _ = (dPointEquiv n x)⁻¹ := one_mul _

/-- The nonnegative entries of the inverse F4 Cartan matrix. -/
def torusRecoveryExponent : Matrix (Fin 4) (Fin 4) ℕ :=
  !![2, 3, 4, 2; 3, 6, 8, 4; 2, 4, 6, 3; 1, 2, 3, 2]

omit [IsAlgClosed k] in
lemma basisTorusUnit_simple (u : Fin 4 → kˣ) (j : Fin 4) :
    basisTorusUnit u (Sum.inr (typeF4SimpleRootIndex j)) =
      ∏ i, u i ^ (-typeF4CartanMatrix j i) := by
  rw [basisTorusUnit_formula]
  apply Finset.prod_congr rfl
  intro i _
  congr 2
  exact typeF4RootPairing_base_cartan_apply j i

omit [IsAlgClosed k] in
lemma basisTorusUnit_recover (u : Fin 4 → kˣ) (i : Fin 4) :
    u i = ∏ j, (basisTorusUnit u (Sum.inr (typeF4SimpleRootIndex j)))⁻¹ ^
      torusRecoveryExponent i j := by
  simp only [basisTorusUnit_simple, Fin.prod_univ_four]
  fin_cases i <;>
    norm_num [torusRecoveryExponent, typeF4CartanMatrix, Fin.ext_iff,
      Matrix.cons_val_two, Matrix.cons_val_three]
  all_goals
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
    <;> ring_nf
    <;> rfl

omit [IsAlgClosed k] in
lemma basisTorusUnit_inv_recover (u : Fin 4 → kˣ) (i : Fin 4) :
    (u i)⁻¹ = ∏ j, basisTorusUnit u (Sum.inr (typeF4SimpleRootIndex j)) ^
      torusRecoveryExponent i j := by
  have h := basisTorusUnit_recover u⁻¹ i
  simpa only [Pi.inv_apply, basisTorusUnit_inv, inv_inv] using h

private lemma torusAmbientMorphism_diagonal_apply
    (x : Variety.Point (dVariety k 4)) (b : BasisIndex) :
    (torusAmbientMorphism.onPoints x).val
        (Sum.inl (carrierIndexEquiv (k := k) b, carrierIndexEquiv (k := k) b)) =
      (basisTorusUnit (dPointEquiv 4 x) b : k) := by
  rw [torusAmbientMorphism_apply, generalLinearRepresentationPoint_matrix]
  simp [torusPointRepresentation, carrierBasis, Module.Basis.reindex_apply,
    torusElement, integralChevalleyTorusElement, RootPairing.IntegralGeckConstruction.carrierBasis]

public noncomputable def carrierDiagonalCoordinate (b : BasisIndex) :
    Variety.PolynomialFunction (Carrier (k := k)) :=
  Variety.PolynomialFunction.pullback
    (ambientClosedCarrier (k := k)).inclusion.toVariety
    (generalLinearMatrixCoordinate (k := k)
      (Module.finrank k (BasisIndex → k))
      (carrierIndexEquiv (k := k) b) (carrierIndexEquiv (k := k) b))

public noncomputable def carrierInverseDiagonalCoordinate (b : BasisIndex) :
    Variety.PolynomialFunction (Carrier (k := k)) :=
  Variety.PolynomialFunction.pullback
    (ambientClosedCarrier (k := k)).inclusion.toVariety
    (generalLinearInverseMatrixCoordinate (k := k)
      (Module.finrank k (BasisIndex → k))
      (carrierIndexEquiv (k := k) b) (carrierIndexEquiv (k := k) b))

private lemma carrierDiagonalCoordinate_splitTorusMorphism_apply
    (b : BasisIndex) (x : Variety.Point (dVariety k 4)) :
    carrierDiagonalCoordinate (k := k) b (splitTorusMorphism.onPoints x) =
      (basisTorusUnit (dPointEquiv 4 x) b : k) := by
  change generalLinearMatrixCoordinate (k := k)
      (Module.finrank k (BasisIndex → k))
      (carrierIndexEquiv (k := k) b) (carrierIndexEquiv (k := k) b)
      ((ambientClosedCarrier (k := k)).inclusion.onPoints
        (splitTorusMorphism.onPoints x)) = _
  rw [splitTorusMorphism_inclusion_apply, generalLinearMatrixCoordinate_apply]
  exact torusAmbientMorphism_diagonal_apply x b

private lemma carrierInverseDiagonalCoordinate_splitTorusMorphism_apply
    (b : BasisIndex) (x : Variety.Point (dVariety k 4)) :
    carrierInverseDiagonalCoordinate (k := k) b (splitTorusMorphism.onPoints x) =
      ((basisTorusUnit (dPointEquiv 4 x) b)⁻¹ : kˣ) := by
  change generalLinearInverseMatrixCoordinate (k := k)
      (Module.finrank k (BasisIndex → k))
      (carrierIndexEquiv (k := k) b) (carrierIndexEquiv (k := k) b)
      ((ambientClosedCarrier (k := k)).inclusion.onPoints
        (splitTorusMorphism.onPoints x)) = _
  rw [splitTorusMorphism_inclusion_apply, generalLinearInverseMatrixCoordinate_apply]
  rw [← torusAmbientMorphism.map_inv, torusAmbientMorphism_diagonal_apply]
  rw [dPointEquiv_inv_local, basisTorusUnit_inv]

public noncomputable def carrierRecoverCoordinate (i : Fin 4) :
    Variety.PolynomialFunction (Carrier (k := k)) :=
  ∏ j, carrierInverseDiagonalCoordinate (k := k) (Sum.inr (typeF4SimpleRootIndex j)) ^
    torusRecoveryExponent i j

public noncomputable def carrierRecoverInverseCoordinate (i : Fin 4) :
    Variety.PolynomialFunction (Carrier (k := k)) :=
  ∏ j, carrierDiagonalCoordinate (k := k) (Sum.inr (typeF4SimpleRootIndex j)) ^
    torusRecoveryExponent i j

private lemma carrierRecoverCoordinate_splitTorusMorphism_apply
    (i : Fin 4) (x : Variety.Point (dVariety k 4)) :
    carrierRecoverCoordinate (k := k) i (splitTorusMorphism.onPoints x) =
      (dPointEquiv 4 x i : k) := by
  change Variety.PolynomialFunction.evalAlgHom _ (splitTorusMorphism.onPoints x)
    (∏ j, carrierInverseDiagonalCoordinate (k := k) (Sum.inr (typeF4SimpleRootIndex j)) ^
      torusRecoveryExponent i j) = _
  simp only [map_prod, map_pow]
  change (∏ j, carrierInverseDiagonalCoordinate (k := k) (Sum.inr (typeF4SimpleRootIndex j))
    (splitTorusMorphism.onPoints x) ^ torusRecoveryExponent i j) = _
  simp only [carrierInverseDiagonalCoordinate_splitTorusMorphism_apply]
  simpa only [Units.coe_prod, Units.val_pow_eq_pow_val] using
    congrArg Units.val (basisTorusUnit_recover (dPointEquiv 4 x) i).symm

private lemma carrierRecoverInverseCoordinate_splitTorusMorphism_apply
    (i : Fin 4) (x : Variety.Point (dVariety k 4)) :
    carrierRecoverInverseCoordinate (k := k) i (splitTorusMorphism.onPoints x) =
      ((dPointEquiv 4 x i)⁻¹ : kˣ) := by
  change Variety.PolynomialFunction.evalAlgHom _ (splitTorusMorphism.onPoints x)
    (∏ j, carrierDiagonalCoordinate (k := k) (Sum.inr (typeF4SimpleRootIndex j)) ^
      torusRecoveryExponent i j) = _
  simp only [map_prod, map_pow]
  change (∏ j, carrierDiagonalCoordinate (k := k) (Sum.inr (typeF4SimpleRootIndex j))
    (splitTorusMorphism.onPoints x) ^ torusRecoveryExponent i j) = _
  simp only [carrierDiagonalCoordinate_splitTorusMorphism_apply]
  simpa only [Units.coe_prod, Units.val_pow_eq_pow_val] using
    congrArg Units.val (basisTorusUnit_inv_recover (dPointEquiv 4 x) i).symm

public theorem splitTorusMorphism_injective :
    Function.Injective (splitTorusMorphism (k := k)).onPoints := by
  intro x y hxy
  apply (dPointEquiv 4).injective
  funext i
  apply Units.ext
  rw [← carrierRecoverCoordinate_splitTorusMorphism_apply i x,
    ← carrierRecoverCoordinate_splitTorusMorphism_apply i y, hxy]

private theorem splitTorusMorphism_coordinate_preimage
    (c : (dVariety k 4).Coordinates) :
    ∃ q : Variety.PolynomialFunction (Carrier (k := k)),
      Variety.PolynomialFunction.pullback splitTorusMorphism.toVariety q =
        Variety.PolynomialFunction.ofPolynomial (dVariety k 4) (MvPolynomial.X c) := by
  cases c with
  | inl i =>
      refine ⟨carrierRecoverCoordinate (k := k) i.down, ?_⟩
      apply Variety.PolynomialFunction.ext
      intro x
      change carrierRecoverCoordinate (k := k) i.down
          (splitTorusMorphism.onPoints x) =
        evalPolynomial x.val (MvPolynomial.X (Sum.inl i))
      rw [carrierRecoverCoordinate_splitTorusMorphism_apply, evalPolynomial_X]
      rfl
  | inr i =>
      refine ⟨carrierRecoverInverseCoordinate (k := k) i.down, ?_⟩
      apply Variety.PolynomialFunction.ext
      intro x
      change carrierRecoverInverseCoordinate (k := k) i.down
          (splitTorusMorphism.onPoints x) =
        evalPolynomial x.val (MvPolynomial.X (Sum.inr i))
      rw [carrierRecoverInverseCoordinate_splitTorusMorphism_apply,
        evalPolynomial_X, Units.val_inv_eq_inv_val]
      change (dPointEntry 4 x i.down)⁻¹ = dPointEntryInv 4 x i.down
      exact dPoint_entry_inv 4 x i.down

/-- The four-parameter diagonal morphism is an isomorphism onto its closed
image. The inverse is regular because the inverse Cartan matrix recovers all
four parameters from the simple-root diagonal entries. -/
public theorem exists_splitTorusIso :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    ∃ e : AlgebraicGroup.Iso (dVariety k 4) (splitTorus (k := k)).carrierVariety,
      e.hom = splitTorusMorphism.codRestrictClosedSubgroup splitTorus
        (fun y => ⟨y, rfl⟩) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  exact splitTorusMorphism.iso_imageClosedSubgroup_of_coordinate_preimage
    splitTorusMorphism_injective splitTorusMorphism_coordinate_preimage

/-- The standard rank-four torus identified with its closed image in the F4
Chevalley carrier. -/
public noncomputable def splitTorusIso :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    AlgebraicGroup.Iso (dVariety k 4) (splitTorus (k := k)).carrierVariety := by
  letI := (splitTorus (k := k)).carrierAlgebraicGroup
  exact Classical.choose (exists_splitTorusIso (k := k))

public lemma splitTorusIso_hom :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    (splitTorusIso (k := k)).hom =
      splitTorusMorphism.codRestrictClosedSubgroup splitTorus
        (fun y => ⟨y, rfl⟩) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  exact Classical.choose_spec (exists_splitTorusIso (k := k))

public lemma splitTorusIso_inclusion_apply
    (x : Variety.Point (dVariety k 4)) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    (splitTorus (k := k)).inclusion.onPoints
        ((splitTorusIso (k := k)).hom.onPoints x) =
      splitTorusMorphism.onPoints x := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  rw [splitTorusIso_hom]
  exact splitTorusMorphism.codRestrictClosedSubgroup_inclusion_apply
    splitTorus (fun y => ⟨y, rfl⟩) x

public lemma splitTorusIso_ambient_inclusion_apply
    (x : Variety.Point (dVariety k 4)) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    (ambientClosedCarrier (k := k)).inclusion.onPoints
        ((splitTorus (k := k)).inclusion.onPoints
          ((splitTorusIso (k := k)).hom.onPoints x)) =
      torusAmbientMorphism.onPoints x := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  rw [splitTorusIso_inclusion_apply, splitTorusMorphism_inclusion_apply]

public lemma splitTorusIso_inverse_apply
    (s : Variety.Point (splitTorus (k := k)).carrierVariety) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    splitTorusMorphism.onPoints ((splitTorusIso (k := k)).inv.onPoints s) =
      (splitTorus (k := k)).inclusion.onPoints s := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  have h := splitTorusIso_inclusion_apply (k := k)
    ((splitTorusIso (k := k)).inv.onPoints s)
  rw [(splitTorusIso (k := k)).inv_hom_id] at h
  exact h.symm

public lemma splitTorus_inclusion_torusElement_apply
    (s : Variety.Point (splitTorus (k := k)).carrierVariety) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    (ambientClosedCarrier (k := k)).inclusion.onPoints
        ((splitTorus (k := k)).inclusion.onPoints s) =
      generalLinearRepresentationPoint (carrierBasis (k := k))
        (Matrix.GeneralLinearGroup.toLin
          (torusElement
            (dPointEquiv 4 ((splitTorusIso (k := k)).inv.onPoints s)))) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  rw [← splitTorusIso_inverse_apply, splitTorusMorphism_inclusion_apply,
    torusAmbientMorphism_apply]
  rfl

public lemma splitTorus_diagonal_matrix_apply
    (s : Variety.Point (splitTorus (k := k)).carrierVariety) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    glPointEquivOf k (BasisIndex → k) (carrierBasis (k := k))
        ((ambientClosedCarrier (k := k)).inclusion.onPoints
          ((splitTorus (k := k)).inclusion.onPoints s)) =
      Matrix.GeneralLinearGroup.toLin
        (torusElement
          (dPointEquiv 4 ((splitTorusIso (k := k)).inv.onPoints s))) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  rw [splitTorus_inclusion_torusElement_apply,
    glPointEquivOf_generalLinearRepresentationPoint]

/-- The inverse point parametrization of the closed split torus. -/
public noncomputable def splitTorusPointEquiv :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    Variety.Point (splitTorus (k := k)).carrierVariety ≃*
      Variety.Point (dVariety k 4) := by
  letI := (splitTorus (k := k)).carrierAlgebraicGroup
  exact (splitTorusIso (k := k)).toMulEquiv.symm

/-- A Laurent character transported from the standard rank-four torus. -/
public noncomputable def splitTorusCharacter (z : Fin 4 → ℤ) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    TorusCharacter (splitTorus (k := k)).carrierVariety := by
  letI := (splitTorus (k := k)).carrierAlgebraicGroup
  exact (dLaurentCharacter (k := k) 4 z).comp
    (splitTorusIso (k := k)).inv

public lemma splitTorusCharacter_apply (z : Fin 4 → ℤ)
    (x : Variety.Point (dVariety k 4)) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    dPointEquiv 1
        ((splitTorusCharacter (k := k) z).onPoints
          ((splitTorusIso (k := k)).hom.onPoints x)) 0 =
      ∏ i, (dPointEquiv 4 x i) ^ z i := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  change dPointEquiv 1
      ((dLaurentCharacter (k := k) 4 z).onPoints
        ((splitTorusIso (k := k)).inv.onPoints
          ((splitTorusIso (k := k)).hom.onPoints x))) 0 = _
  rw [(splitTorusIso (k := k)).hom_inv_id, dLaurentCharacter_apply]

public lemma splitTorusCharacter_apply_point (z : Fin 4 → ℤ)
    (s : Variety.Point (splitTorus (k := k)).carrierVariety) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    dPointEquiv 1 ((splitTorusCharacter (k := k) z).onPoints s) 0 =
      ∏ i, (dPointEquiv 4 ((splitTorusIso (k := k)).inv.onPoints s) i) ^ z i := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  change dPointEquiv 1
      ((dLaurentCharacter (k := k) 4 z).onPoints
        ((splitTorusIso (k := k)).inv.onPoints s)) 0 = _
  exact dLaurentCharacter_apply 4 z _

/-- The character giving the diagonal entry indexed by `b`. -/
public noncomputable def splitTorusBasisCharacter (b : BasisIndex) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    TorusCharacter (splitTorus (k := k)).carrierVariety :=
  splitTorusCharacter (k := k) (torusWeightExponent b)

public lemma splitTorusBasisCharacter_apply (b : BasisIndex)
    (x : Variety.Point (dVariety k 4)) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    dPointEquiv 1
        ((splitTorusBasisCharacter (k := k) b).onPoints
          ((splitTorusIso (k := k)).hom.onPoints x)) 0 =
      basisTorusUnit (dPointEquiv 4 x) b := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  exact (splitTorusCharacter_apply (k := k) (torusWeightExponent b) x).trans
    (basisTorusUnit_formula _ _).symm

/-- A cocharacter transported from an integral exponent vector on `D₄`. -/
public noncomputable def splitTorusCocharacter (z : Fin 4 → ℤ) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    TorusCocharacter (splitTorus (k := k)).carrierVariety := by
  letI := (splitTorus (k := k)).carrierAlgebraicGroup
  exact (splitTorusIso (k := k)).hom.comp
    (dCharacterTupleMorphism (k := k) 4 1 (fun i _ => z i))

public lemma splitTorusCocharacter_inverse_apply (z : Fin 4 → ℤ)
    (t : Variety.Point (KMult k)) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    (splitTorusIso (k := k)).inv.onPoints
        ((splitTorusCocharacter (k := k) z).onPoints t) =
      (dCharacterTupleMorphism (k := k) 4 1
        (fun i _ => z i)).onPoints t := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  change (splitTorusIso (k := k)).inv.onPoints
      ((splitTorusIso (k := k)).hom.onPoints
        ((dCharacterTupleMorphism (k := k) 4 1
          (fun i _ => z i)).onPoints t)) = _
  rw [(splitTorusIso (k := k)).hom_inv_id]

public lemma splitTorusCocharacter_inclusion_apply (z : Fin 4 → ℤ)
    (t : Variety.Point (KMult k)) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    (splitTorus (k := k)).inclusion.onPoints
        ((splitTorusCocharacter (k := k) z).onPoints t) =
      splitTorusMorphism.onPoints
        ((dCharacterTupleMorphism (k := k) 4 1
          (fun i _ => z i)).onPoints t) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  exact splitTorusIso_inclusion_apply (k := k)
    ((dCharacterTupleMorphism (k := k) 4 1
      (fun i _ => z i)).onPoints t)

public lemma splitTorusCocharacter_torusElement_apply (z : Fin 4 → ℤ)
    (t : Variety.Point (KMult k)) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    (ambientClosedCarrier (k := k)).inclusion.onPoints
        ((splitTorus (k := k)).inclusion.onPoints
          ((splitTorusCocharacter (k := k) z).onPoints t)) =
      generalLinearRepresentationPoint (carrierBasis (k := k))
        (Matrix.GeneralLinearGroup.toLin
          (torusElement (fun i => (dPointEquiv 1 t 0) ^ z i))) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  rw [splitTorusCocharacter_inclusion_apply,
    splitTorusMorphism_inclusion_apply, torusAmbientMorphism_apply]
  have hparam :
      dPointEquiv 4
          ((dCharacterTupleMorphism (k := k) 4 1
            (fun i _ => z i)).onPoints t) =
        fun i => (dPointEquiv 1 t 0) ^ z i := by
    funext i
    rw [dCharacterTupleMorphism_apply]
    simp
  change generalLinearRepresentationPoint (carrierBasis (k := k))
      (Matrix.GeneralLinearGroup.toLin
        (torusElement
          (dPointEquiv 4
            ((dCharacterTupleMorphism (k := k) 4 1
              (fun i _ => z i)).onPoints t)))) = _
  rw [hparam]

public theorem exists_maximalTorus_containing_split :
    ∃ M : ClosedSubgroup (Carrier (k := k)),
      IsMaximalTorus M ∧ splitTorus (k := k) ≤ M := by
  obtain ⟨M, hM, hmax⟩ := exists_maximal_connected_closedSubgroup (Carrier (k := k))
    (fun S => IsSubtorus S ∧ splitTorus (k := k) ≤ S)
    ⟨splitTorus, splitTorus_isSubtorus, fun _ hx => hx⟩
    (fun S hS => by
      let _ : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
      have hSvar : Variety.IsConnected S.carrierVariety := hS.1.isConnected
      let : ConnectedSpace (Variety.Point S.carrierVariety) :=
        connectedSpace_iff_univ.mpr hSvar
      change _root_.IsConnected (S.toSubgroup : Set (Variety.Point (Carrier (k := k))))
      rw [← S.range_inclusion]
      exact isConnected_range S.inclusion.toVariety.continuous)
  refine ⟨M, ⟨hM.1, ?_⟩, hM.2⟩
  intro S hS hMS
  exact hmax S ⟨hS, fun x hx => hMS (hM.2 hx)⟩ hMS

public noncomputable def maximalTorus : ClosedSubgroup (Carrier (k := k)) :=
  Classical.choose (exists_maximalTorus_containing_split (k := k))

public theorem maximalTorus_isMaximal : IsMaximalTorus (maximalTorus (k := k)) :=
  (Classical.choose_spec (exists_maximalTorus_containing_split (k := k))).1

public theorem maximalTorus_isSubtorus : IsSubtorus (maximalTorus (k := k)) :=
  (maximalTorus_isMaximal (k := k)).1

public theorem splitTorus_le_maximalTorus :
    splitTorus (k := k) ≤ maximalTorus (k := k) :=
  (Classical.choose_spec (exists_maximalTorus_containing_split (k := k))).2


/-- The torus morphism uses the literal integral diagonal matrix. -/
lemma torusAmbientMorphism_matrix (x : Variety.Point (dVariety k 4)) :
    torusAmbientMorphism.onPoints x = matrixToAmbient (torusElement (dPointEquiv 4 x)) := by
  rw [torusAmbientMorphism_apply]
  rfl

/-- Root characters for conjugation by the inverse diagonal torus element. -/
def torusRootExponent (r : Root) (i : Fin 4) : ℤ :=
  typeF4RootPairing.pairingIn ℤ r (typeF4RootPairing_baseEquiv i)

omit [IsAlgClosed k] in
lemma torusRootScale_formula (u : Fin 4 → kˣ) (r : Root) :
    integralChevalleyRootScale (P := typeF4RootPairing) (torusParameter u) r =
      ∏ i, u i ^ torusRootExponent r i := by
  rw [integralChevalleyRootScale, ← typeF4RootPairing_baseEquiv.prod_comp]
  simp only [torusParameter, Equiv.symm_apply_apply, torusRootExponent]

/-- Exact conjugation in the closed carrier, with the inverse-diagonal convention. -/
theorem splitTorusMorphism_root_conjugation (x : Variety.Point (dVariety k 4))
    (r : Root) (a : k) :
    (splitTorusMorphism.onPoints x)⁻¹ * (rootMorphism r).onPoints (kPlusPoint a) *
      splitTorusMorphism.onPoints x =
      (rootMorphism r).onPoints
        (kPlusPoint ((↑(∏ i, (dPointEquiv 4 x i) ^ torusRootExponent r i) : k) * a)) := by
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  simp only [map_mul, map_inv, splitTorusMorphism_inclusion_apply,
    rootMorphism_inclusion_apply, torusAmbientMorphism_matrix, ← matrixToAmbient_root]
  simp only [← map_inv, ← map_mul]
  apply congrArg matrixToAmbient
  simpa only [torusRootScale_formula, torusElement, rootCurve, integralOperators] using
    (integralChevalleyRootCurve_torus_conjugation (P := typeF4RootPairing)
      (torusParameter (dPointEquiv 4 x)) r a)

/-- The positive simple coroot has exponent minus one in the diagonal convention. -/
def simpleCorootExponent (i j : Fin 4) : ℤ := if j = i then -1 else 0

/-- The regular simple-coroot cocharacter of the actual split torus. -/
def splitTorusSimpleCoroot (i : Fin 4) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    TorusCocharacter (splitTorus (k := k)).carrierVariety :=
  splitTorusCocharacter (simpleCorootExponent i)

omit [IsAlgClosed k] in
lemma torusParameter_simpleCoroot (i : Fin 4) (t : kˣ) :
    torusParameter (fun j => t ^ simpleCorootExponent i j) =
      integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) t⁻¹ := by
  funext q
  have he : typeF4RootPairing_baseEquiv.symm q = i ↔ q = typeF4RootPairing_baseEquiv i :=
    typeF4RootPairing_baseEquiv.symm_apply_eq
  simp only [torusParameter, simpleCorootExponent, integralChevalleySimpleCorootParameter, he]
  split_ifs <;> simp

/-- Simple cocharacters are the concrete rank-one coroot words in the ambient group. -/
theorem splitTorusSimpleCoroot_ambient_apply (i : Fin 4) (t : Variety.Point (KMult k)) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    (ambientClosedCarrier (k := k)).inclusion.onPoints
      ((splitTorus (k := k)).inclusion.onPoints
        ((splitTorusSimpleCoroot (k := k) i).onPoints t)) =
      matrixToAmbient (matrixH (F := k) (typeF4RootPairing_baseEquiv i) (dPointEquiv 1 t 0)) := by
  let _ := (splitTorus (k := k)).carrierAlgebraicGroup
  rw [splitTorusSimpleCoroot, splitTorusCocharacter_torusElement_apply]
  change matrixToAmbient (torusElement _) = _
  rw [torusElement, torusParameter_simpleCoroot, ← matrixH_simple]

/-- Evaluation of every character on a simple coroot fixes the sign convention. -/
theorem splitTorusCharacter_simpleCoroot (z : Fin 4 → ℤ) (i : Fin 4)
    (t : Variety.Point (KMult k)) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    dPointEquiv 1 ((splitTorusCharacter (k := k) z).onPoints
      ((splitTorusSimpleCoroot (k := k) i).onPoints t)) 0 =
        (dPointEquiv 1 t 0) ^ (-z i) := by
  let _ := (splitTorus (k := k)).carrierAlgebraicGroup
  rw [splitTorusCharacter_apply_point]
  change (∏ j, (dPointEquiv 4 ((splitTorusIso (k := k)).inv.onPoints
    ((splitTorusCocharacter (simpleCorootExponent i)).onPoints t)) j) ^ z j) = _
  rw [splitTorusCocharacter_inverse_apply]
  simp only [dCharacterTupleMorphism_apply, Fin.prod_univ_one]
  simp [simpleCorootExponent]

/-- The inverse isomorphism recovers each parameter by an explicit regular function. -/
theorem splitTorusIso_inverse_coordinate (s : Variety.Point (splitTorus (k := k)).carrierVariety)
    (i : Fin 4) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    (dPointEquiv 4 ((splitTorusIso (k := k)).inv.onPoints s) i : k) =
      carrierRecoverCoordinate i ((splitTorus (k := k)).inclusion.onPoints s) := by
  let _ := (splitTorus (k := k)).carrierAlgebraicGroup
  rw [← splitTorusIso_inverse_apply, carrierRecoverCoordinate_splitTorusMorphism_apply]

/-- Restriction to the carrier has exactly the original ambient diagonal image. -/
theorem splitTorus_inclusion_image :
    (ambientClosedCarrier (k := k)).inclusion.onPoints ''
      (splitTorus (k := k) : Set (Variety.Point (Carrier (k := k)))) =
      (ambientSplitTorus (k := k) : Set (Variety.Point (Ambient k))) := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, splitTorusMorphism_inclusion_apply z⟩
  · rintro ⟨x, rfl⟩
    refine ⟨splitTorusMorphism.onPoints x, ⟨x, rfl⟩, ?_⟩
    exact splitTorusMorphism_inclusion_apply x


end Theory.AlgebraicGroup.F4Chevalley
