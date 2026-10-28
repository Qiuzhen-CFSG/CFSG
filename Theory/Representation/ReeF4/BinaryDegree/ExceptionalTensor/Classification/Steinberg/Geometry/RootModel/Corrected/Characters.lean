module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.CorootConvention

/-!
# Regular raw cocharacters and the left-weight boundary for F4

The literal root curves use inverse conjugation. Thus their raw simple
cocharacters are the representation coroots evaluated at the inverse parameter.
The inversion below is an algebraic group morphism. All four coordinate formulas
and all character evaluations follow by composing the proved split-torus maps.
The positive roots and representation coroot words retain their original labels.

Source: GLS3, Sections 1.9 and 1.12, especially 1.9.6 and 1.12.1(g).
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance charactersTorusGroup : AlgebraicGroup (F4Chevalley.splitTorus (k := F)).carrierVariety :=
  (F4Chevalley.splitTorus (k := F)).carrierAlgebraicGroup

/-- Regular group inversion on the multiplicative parameter. -/
def parameterInversion : Theory.AlgebraicGroup.Morphism (KMult F) (KMult F) where
  toVariety := Theory.AlgebraicGroup.invMorphism (KMult F)
  map_one := inv_one
  map_mul := fun x y => (mul_inv_rev x y).trans
    (isMulCommutative_iff.mp (dVariety_isMulCommutative 1) _ _)

omit [IsAlgClosed F] in
@[simp] theorem parameterInversion_apply (t : Variety.Point (KMult F)) :
    (parameterInversion (F := F)).onPoints t = t⁻¹ := rfl

omit [IsAlgClosed F] in
/-- Inversion on multiplicative points is inversion in every unit coordinate. -/
theorem dPointEquiv_inv (n : ℕ) (t : Variety.Point (dVariety F n)) :
    dPointEquiv n t⁻¹ = (dPointEquiv n t)⁻¹ := by
  let f : Variety.Point (dVariety F n) →* (Fin n → Fˣ) :=
    ⟨⟨dPointEquiv n, dPointEquiv_one n⟩, dPointEquiv_mul n⟩
  exact map_inv f t

/-- The raw simple cocharacter is the actual regular inverse-parameter composite. -/
def rawSimpleCocharacter (i : Fin 4) :
    ClosedSubgroupTorusCocharacter (F4Chevalley.splitTorus (k := F)) :=
  (F4Chevalley.splitTorusSimpleCoroot i).comp parameterInversion

@[simp] theorem rawSimpleCocharacter_apply (i : Fin 4) (t : Variety.Point (KMult F)) :
    (rawSimpleCocharacter (F := F) i).onPoints t =
      (F4Chevalley.splitTorusSimpleCoroot i).onPoints t⁻¹ := rfl

/-- The corrected source identification, inside the literal carrier. -/
theorem rawSimpleCocharacter_inclusion (i : Fin 4) (t : Variety.Point (KMult F)) :
    (F4Chevalley.splitTorus (k := F)).inclusion.onPoints
      ((rawSimpleCocharacter i).onPoints t) =
    algebraicCorootElement (typeF4SimpleRootIndex i) ((dPointEquiv 1 t 0)⁻¹) := by
  rw [rawSimpleCocharacter_apply, splitTorusSimpleCoroot_eq_algebraicCoroot,
    dPointEquiv_inv]
  rfl

/-- Conversely, the representation coroot is the raw coroot at the inverse parameter. -/
theorem representationCoroot_eq_raw_inverse (i : Fin 4) (t : Variety.Point (KMult F)) :
    algebraicCorootElement (typeF4SimpleRootIndex i) (dPointEquiv 1 t 0) =
      (F4Chevalley.splitTorus (k := F)).inclusion.onPoints
        ((rawSimpleCocharacter i).onPoints t⁻¹) := by
  rw [rawSimpleCocharacter_inclusion, dPointEquiv_inv]
  simp

/-- Raw simple cocharacters have positive coordinate one at their numbered node. -/
theorem rawSimpleCocharacter_coordinate (i j : Fin 4) (t : Variety.Point (KMult F)) :
    dPointEquiv 4 ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints
      ((rawSimpleCocharacter i).onPoints t)) j =
        if j = i then dPointEquiv 1 t 0 else 1 := by
  rw [rawSimpleCocharacter_apply]
  change dPointEquiv 4 ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints
    ((F4Chevalley.splitTorusCocharacter (F4Chevalley.simpleCorootExponent i)).onPoints t⁻¹)) j = _
  rw [F4Chevalley.splitTorusCocharacter_inverse_apply, dCharacterTupleMorphism_apply]
  simp [F4Chevalley.simpleCorootExponent, dPointEquiv_inv]

theorem rawSimpleCocharacter_coordinates_zero (t : Variety.Point (KMult F)) :
    dPointEquiv 4 ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints
      ((rawSimpleCocharacter 0).onPoints t)) = ![dPointEquiv 1 t 0, 1, 1, 1] := by
  funext j
  rw [rawSimpleCocharacter_coordinate]
  fin_cases j <;> simp

theorem rawSimpleCocharacter_coordinates_one (t : Variety.Point (KMult F)) :
    dPointEquiv 4 ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints
      ((rawSimpleCocharacter 1).onPoints t)) = ![1, dPointEquiv 1 t 0, 1, 1] := by
  funext j
  rw [rawSimpleCocharacter_coordinate]
  fin_cases j <;> simp

theorem rawSimpleCocharacter_coordinates_two (t : Variety.Point (KMult F)) :
    dPointEquiv 4 ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints
      ((rawSimpleCocharacter 2).onPoints t)) = ![1, 1, dPointEquiv 1 t 0, 1] := by
  funext j
  rw [rawSimpleCocharacter_coordinate]
  fin_cases j <;> simp

theorem rawSimpleCocharacter_coordinates_three (t : Variety.Point (KMult F)) :
    dPointEquiv 4 ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints
      ((rawSimpleCocharacter 3).onPoints t)) = ![1, 1, 1, dPointEquiv 1 t 0] := by
  funext j
  rw [rawSimpleCocharacter_coordinate]
  fin_cases j <;> simp

/-- Evaluation on the corrected raw simple cocharacters has the positive Cartan exponent. -/
theorem rootWeight_rawSimpleCocharacter (r : F4Chevalley.Root) (i : Fin 4) :
    WeightCocharacterEquation (F4Chevalley.splitTorus (k := F))
      (F4Chevalley.rootWeight r) (rawSimpleCocharacter i)
      (typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i)) :=
  rootWeight_simpleCoroot_inverse_parameter r i

/-- The raw integral character coordinates. -/
def rawCharacter (a : Fin 4 → ℤ) : TorusWeight (F4Chevalley.splitTorus (k := F)) :=
  F4Chevalley.splitTorusCharacter a

/-- Direct left-action characters use the negatives of the raw coordinates. -/
def leftCharacter (a : Fin 4 → ℤ) : TorusWeight (F4Chevalley.splitTorus (k := F)) :=
  rawCharacter (-a)

/-- The explicit interface `E_left(a) = E_raw(-a)`. -/
theorem leftCharacter_eq_raw_neg (a : Fin 4 → ℤ) :
    leftCharacter (F := F) a = rawCharacter (-a) := rfl

/-- Negation of raw coordinates is inversion of the actual regular character. -/
theorem rawCharacter_neg (a : Fin 4 → ℤ) :
    rawCharacter (F := F) (-a) = (rawCharacter a)⁻¹ := by
  change TorusCharacter.pullback (F4Chevalley.splitTorusIso (k := F)).inv
      (dLaurentCharacter 4 (-a)) = _
  have h : dLaurentCharacter (k := F) 4 (-a) = (dLaurentCharacter 4 a)⁻¹ :=
    (dLaurentCharacterHom 4).map_neg a
  rw [h, map_inv]
  rfl

/-- Simultaneous inversion of the character coordinates and parameter preserves positive evaluation. -/
theorem leftCharacter_representationCoroot (a : Fin 4 → ℤ) (i : Fin 4) :
    WeightCocharacterEquation (F4Chevalley.splitTorus (k := F))
      (leftCharacter a) (F4Chevalley.splitTorusSimpleCoroot i) (a i) := by
  intro t
  change (dPointEquiv 1 ((F4Chevalley.splitTorusCharacter (-a)).onPoints
    ((F4Chevalley.splitTorusSimpleCoroot i).onPoints t)) 0 : F) = _
  rw [F4Chevalley.splitTorusCharacter_simpleCoroot]
  simp

/-- Raw coordinates evaluate positively on raw simple cocharacters. -/
theorem rawCharacter_rawSimpleCocharacter (a : Fin 4 → ℤ) (i : Fin 4) :
    WeightCocharacterEquation (F4Chevalley.splitTorus (k := F))
      (rawCharacter a) (rawSimpleCocharacter i) (a i) := by
  intro t
  change (dPointEquiv 1 ((F4Chevalley.splitTorusCharacter a).onPoints
    ((F4Chevalley.splitTorusSimpleCoroot i).onPoints t⁻¹)) 0 : F) = _
  rw [F4Chevalley.splitTorusCharacter_simpleCoroot, dPointEquiv_inv]
  simp

/-- Each left fundamental character is the inverse of its raw counterpart. -/
theorem left_fundamentalCharacter (i : Fin 4) :
    leftCharacter (F := F) (Pi.single i 1) = (rawCharacter (Pi.single i 1))⁻¹ :=
  rawCharacter_neg _

/-- Raw fundamental coordinates on the concrete torus points. -/
theorem raw_fundamentalCharacter_apply (i : Fin 4)
    (s : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety) :
    (rawCharacter (Pi.single i 1)).pointCharacter s =
      (dPointEquiv 4 ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints s) i : F) := by
  change (dPointEquiv 1 ((F4Chevalley.splitTorusCharacter (Pi.single i 1)).onPoints s) 0 : F) = _
  rw [F4Chevalley.splitTorusCharacter_apply_point]
  simp [Pi.single_apply]

/-- The corresponding left fundamental coordinates are inverted. -/
theorem left_fundamentalCharacter_apply (i : Fin 4)
    (s : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety) :
    (leftCharacter (Pi.single i 1)).pointCharacter s =
      (dPointEquiv 4 ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints s) i : F)⁻¹ := by
  change (dPointEquiv 1 ((F4Chevalley.splitTorusCharacter (-Pi.single i 1)).onPoints s) 0 : F) = _
  rw [F4Chevalley.splitTorusCharacter_apply_point]
  simp [Pi.single_apply]

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
