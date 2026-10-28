module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected.Geometry
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected.CorootWords
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan

/-!
# The concrete F4 root-system model in characteristic two

The geometric tangent-dimension bound proves that the fixed tangent space and
the 48 literal root lines span. Together with the computed torus centralizer,
this proves that the literal root characters exhaust the actual torus roots.
We therefore realize the standard F4 root pairing, with its transported standard
base, on the concrete Chevalley carrier without further geometric premises.

The regular raw cocharacters include as the literal representation coroot words
at the inverse parameter. The pointwise comparisons below retain the original
positive root labels and the positive Cartan pairing. Left-action characters
retain positive evaluation on the representation coroots by using the negatives
of the raw character coordinates, as in `Corrected.Characters`.

Source: GLS3, Chapter 1, 1.9.3--1.9.6 and 1.12.1(e),(g),(i),
`refs/KGroup/GLS3/Chapter1.tex`. This constructs the concrete root model;
semisimplicity, Borels and universality have their separate constructions.
-/

public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected

universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

local instance : AlgebraicGroup (F4Chevalley.splitTorus (k := F)).carrierVariety :=
  (F4Chevalley.splitTorus (k := F)).carrierAlgebraicGroup

/-- The actual torus roots are exactly the literal F4 root characters. -/
theorem rootWeight_range :
    Set.range (F4Chevalley.rootWeight (k := F)) =
      TorusRootSet (F4Chevalley.splitTorus (k := F)) :=
  rootWeight_range_of_tangent_span F4Chevalley.concreteTangentSummand_iSup_eq_top

/-- All realization clauses hold for the literal datum in characteristic two. -/
theorem rootData_isRealization_charTwo : (rootData (F := F)).IsRealization :=
  rootData_isRealization rootWeight_range

/-- The standard F4 model on the literal carrier, with no geometric premises. -/
@[expose] def rootSystemModel :
    RootSystemModel typeF4RootPairingULift (F4Chevalley.Carrier (k := F)) :=
  model rootWeight_range splitTorus_isMaximal

local instance : AlgebraicGroup (rootSystemModel (F := F)).torus.carrierVariety :=
  (rootSystemModel (F := F)).torus.carrierAlgebraicGroup

/-- The model uses the actual rank-four split torus. -/
theorem rootSystemModel_torus :
    (rootSystemModel (F := F)).torus = F4Chevalley.splitTorus := rfl

/-- The model carries the literal root-group datum. -/
theorem rootSystemModel_rootData :
    (rootSystemModel (F := F)).rootData = rootData := rfl

/-- The chosen base is exactly the transported standard base. -/
theorem rootSystemModel_base :
    (rootSystemModel (F := F)).base = typeF4RootPairingULift_base := rfl

/-- The standard labels are unchanged by the root-system identification. -/
theorem rootSystemModel_rootEquiv (r : F4Chevalley.Root) :
    (rootSystemModel (F := F)).rootEquiv ⟨r⟩ = ⟨r⟩ := rfl

/-- Each labelled model subgroup is the actual literal root subgroup. -/
theorem rootSystemModel_rootSubgroup (r : F4Chevalley.Root) :
    (rootSystemModel (F := F)).rootData.rootSubgroup ⟨r⟩ =
      F4Chevalley.rootSubgroup r := rfl

/-- Each model root character is the literal inverse-conjugation character. -/
theorem rootSystemModel_rootWeight (r : F4Chevalley.Root) :
    (rootSystemModel (F := F)).rootData.rootWeight ⟨r⟩ =
      F4Chevalley.rootWeight r := rfl

/-- Each model cocharacter is the constructed regular inverse-parameter map. -/
theorem rootSystemModel_rootCocharacter (r : F4Chevalley.Root) :
    (rootSystemModel (F := F)).rootData.rootCocharacter ⟨r⟩ =
      rawRootCocharacter r := rfl

/-- Positivity is exactly that of the original standard F4 base. -/
theorem rootSystemModel_positive (r : F4Chevalley.Root) :
    (⟨r⟩ : (rootSystemModel (F := F)).rootData.Root) ∈
      (rootSystemModel (F := F)).rootData.positive ↔
        typeF4RootPairing_base.IsPos r := Iff.rfl

/-- The simple roots are the original standard base support. -/
theorem rootSystemModel_simple (r : F4Chevalley.Root) :
    (⟨r⟩ : (rootSystemModel (F := F)).rootData.Root) ∈
      (rootSystemModel (F := F)).rootData.simple ↔
        r ∈ typeF4RootPairing_base.support := Iff.rfl

/-- The labelled addition contains every root-valued character sum. -/
theorem rootSystemModel_isRootAdditionComplete :
    (rootSystemModel (F := F)).rootData.IsRootAdditionComplete :=
  rootData_isRootAdditionComplete

/-- The original positive labels form an actual positive system. -/
theorem rootSystemModel_isPositiveSystem :
    IsPositiveSystem (rootSystemModel (F := F)).rootData
      (rootSystemModel (F := F)).rootData.positive := by
  apply rootData_isRealization_charTwo.positive_isPositiveSystem_of_height_ne_zero
  intro r
  exact typeF4RootPairing_base.height_ne_zero r.down

/-- The model's regular cocharacters include as the inverse-parameter coroot words. -/
theorem rootSystemModel_rootCocharacter_inclusion (r : F4Chevalley.Root)
    (t : Variety.Point (KMult F)) :
    (rootSystemModel (F := F)).torus.inclusion.onPoints
      (((rootSystemModel (F := F)).rootData.rootCocharacter ⟨r⟩).onPoints t) =
      algebraicCorootElement r ((dPointEquiv 1 t 0)⁻¹) :=
  rawRootCocharacter_inclusion r t

/-- Conversely, every representation coroot is the model coroot at the inverse parameter. -/
theorem representationCoroot_eq_rootSystemModel_inverse (r : F4Chevalley.Root)
    (t : Variety.Point (KMult F)) :
    algebraicCorootElement r (dPointEquiv 1 t 0) =
      (rootSystemModel (F := F)).torus.inclusion.onPoints
        (((rootSystemModel (F := F)).rootData.rootCocharacter ⟨r⟩).onPoints t⁻¹) := by
  rw [rootSystemModel_rootCocharacter_inclusion, dPointEquiv_inv]
  simp

/-- Root evaluation has the positive Cartan exponent for every pair of roots. -/
theorem rootSystemModel_rootWeight_rootCocharacter (r s : F4Chevalley.Root) :
    WeightCocharacterEquation (rootSystemModel (F := F)).torus
      ((rootSystemModel (F := F)).rootData.rootWeight ⟨r⟩)
      ((rootSystemModel (F := F)).rootData.rootCocharacter ⟨s⟩)
      (typeF4RootPairing.pairingIn ℤ r s) :=
  rootWeight_rawRootCocharacter r s

/-- Numbered simple cocharacters agree as regular morphisms with the corrected maps. -/
theorem rootSystemModel_simpleCocharacter (i : Fin 4) :
    (rootSystemModel (F := F)).rootData.rootCocharacter ⟨typeF4SimpleRootIndex i⟩ =
      rawSimpleCocharacter i :=
  rawRootCocharacter_simple i

/-- The four simple cocharacters have their original numbered coordinate axes. -/
theorem rootSystemModel_simpleCocharacter_coordinate (i j : Fin 4)
    (t : Variety.Point (KMult F)) :
    dPointEquiv 4 ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints
      (((rootSystemModel (F := F)).rootData.rootCocharacter
        ⟨typeF4SimpleRootIndex i⟩).onPoints t)) j =
      if j = i then dPointEquiv 1 t 0 else 1 := by
  rw [rootSystemModel_simpleCocharacter]
  exact rawSimpleCocharacter_coordinate i j t

/-- The required simple-root word comparison preserves the numbering and inverts the parameter. -/
theorem rootSystemModel_simpleCocharacter_inclusion (i : Fin 4)
    (t : Variety.Point (KMult F)) :
    (rootSystemModel (F := F)).torus.inclusion.onPoints
      (((rootSystemModel (F := F)).rootData.rootCocharacter
        ⟨typeF4SimpleRootIndex i⟩).onPoints t) =
      algebraicCorootElement (typeF4SimpleRootIndex i) ((dPointEquiv 1 t 0)⁻¹) :=
  rootSystemModel_rootCocharacter_inclusion _ t

/-- Raw character coordinates are exactly the model's numbered simple-coroot pairings. -/
theorem rootSystemModel_weightPairing_rawCharacter (a : Fin 4 → ℤ) (i : Fin 4) :
    (rootSystemModel (F := F)).rootData.weightPairing (rawCharacter a)
      ⟨typeF4SimpleRootIndex i⟩ = a i := by
  change characterCocharacterPairing (F4Chevalley.splitTorus (k := F))
    (rawRootCocharacter (typeF4SimpleRootIndex i)) (Additive.ofMul (rawCharacter a)) = a i
  rw [rawRootCocharacter_simple]
  exact (weightCocharacterEquation_existsUnique (F4Chevalley.splitTorus (k := F))
    (rawCharacter a) (rawSimpleCocharacter i)).unique
      (characterCocharacterPairing_spec _ _ _) (rawCharacter_rawSimpleCocharacter a i)

/-- A direct left-action weight has the negative coordinates in the raw model pairing. -/
theorem rootSystemModel_weightPairing_leftCharacter (a : Fin 4 → ℤ) (i : Fin 4) :
    (rootSystemModel (F := F)).rootData.weightPairing (leftCharacter a)
      ⟨typeF4SimpleRootIndex i⟩ = -a i :=
  rootSystemModel_weightPairing_rawCharacter (-a) i

omit [CharP F 2] in
/-- Left character coordinates evaluate positively on every representation cocharacter. -/
theorem leftCharacter_representationRootCocharacter (a : Fin 4 → ℤ)
    (r : F4Chevalley.Root) :
    WeightCocharacterEquation (F4Chevalley.splitTorus (k := F))
      (leftCharacter a) (representationRootCocharacter r)
      (∑ i, corootCoordinates r i * a i) := by
  intro t
  have h := rawCharacter_rawRootCocharacter (F := F) (-a) r t⁻¹
  simpa [rawRootCocharacter_apply, dPointEquiv_inv, leftCharacter, mul_neg] using h

/-- Actual character evaluation at the torus lift of each literal representation coroot. -/
theorem leftCharacter_representationCoroot_word (a : Fin 4 → ℤ)
    (r : F4Chevalley.Root) (t : Variety.Point (KMult F)) :
    (rootSystemModel (F := F)).torus.inclusion.onPoints
        ((representationRootCocharacter r).onPoints t) =
        algebraicCorootElement r (dPointEquiv 1 t 0) ∧
      (leftCharacter a).pointCharacter ((representationRootCocharacter r).onPoints t) =
        (dPointEquiv 1 t 0 : F) ^ (∑ i, corootCoordinates r i * a i) :=
  ⟨representationRootCocharacter_inclusion r t,
    leftCharacter_representationRootCocharacter a r t⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
