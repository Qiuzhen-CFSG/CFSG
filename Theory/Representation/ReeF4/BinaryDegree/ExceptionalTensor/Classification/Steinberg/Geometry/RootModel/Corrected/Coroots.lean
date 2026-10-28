module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected.Characters

/-!
# All raw F4 cocharacters from the integral coroot lattice

Expand each coroot in the numbered integral simple-coroot basis. Transport its
negative coordinates to the concrete torus for the representation convention,
then compose with regular parameter inversion for the raw convention. The
basis expansion proves the positive Cartan evaluation for every pair of roots.
The simple members agree with the corrected literal representation coroots.
The all-root comparison with the literal rank-one words is a further statement;
no such comparison is assumed here. Source: GLS3 1.9.6 and 1.12.1(e),(g).
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance corootsTorusGroup : AlgebraicGroup (F4Chevalley.splitTorus (k := F)).carrierVariety :=
  (F4Chevalley.splitTorus (k := F)).carrierAlgebraicGroup

/-- The integral simple-coroot basis, with the original four numbered nodes. -/
def corootBasis : Module.Basis (Fin 4) ℤ (typeF4RootPairing.corootSpan ℤ) :=
  typeF4RootPairing_base.flip.toWeightBasisInt.reindex typeF4RootPairing_baseEquiv.symm

lemma corootBasis_apply (i : Fin 4) :
    corootBasis i = typeF4RootPairing.corootSpanMem ℤ (typeF4SimpleRootIndex i) := by
  have h := Module.Basis.reindex_apply typeF4RootPairing_base.flip.toWeightBasisInt
    typeF4RootPairing_baseEquiv.symm i
  apply Subtype.ext
  exact (congrArg Subtype.val h).trans
    (typeF4RootPairing_base.flip.coe_toWeightBasisInt_apply (typeF4RootPairing_baseEquiv i))

/-- Integral coordinates of each coroot in the numbered simple-coroot basis. -/
def corootCoordinates (r : F4Chevalley.Root) (i : Fin 4) : ℤ :=
  corootBasis.repr (typeF4RootPairing.corootSpanMem ℤ r) i

lemma corootCoordinates_simple (i j : Fin 4) :
    corootCoordinates (typeF4SimpleRootIndex i) j = if j = i then 1 else 0 := by
  rw [corootCoordinates, ← corootBasis_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply, eq_comm]

lemma corootCoordinates_pairing (r s : F4Chevalley.Root) :
    ∑ i, corootCoordinates s i * F4Chevalley.torusRootExponent r i =
      typeF4RootPairing.pairingIn ℤ r s := by
  have h := congrArg (typeF4RootPairing.root'In ℤ r)
    (corootBasis.sum_repr (typeF4RootPairing.corootSpanMem ℤ s))
  simp only [map_sum, map_smul, corootBasis_apply,
    RootPairing.root'In_corootSpanMem_eq_pairingIn, smul_eq_mul] at h
  exact h

/-- The representation-oriented regular cocharacter for every root. Its word
identification is a separate statement about the literal rank-one matrices. -/
def representationRootCocharacter (r : F4Chevalley.Root) :
    ClosedSubgroupTorusCocharacter (F4Chevalley.splitTorus (k := F)) :=
  F4Chevalley.splitTorusCocharacter (-corootCoordinates r)

/-- Raw cocharacters use the inverse parameter for every root. -/
def rawRootCocharacter (r : F4Chevalley.Root) :
    ClosedSubgroupTorusCocharacter (F4Chevalley.splitTorus (k := F)) :=
  (representationRootCocharacter r).comp parameterInversion

theorem rawRootCocharacter_apply (r : F4Chevalley.Root) (t : Variety.Point (KMult F)) :
    (rawRootCocharacter (F := F) r).onPoints t =
      (representationRootCocharacter r).onPoints t⁻¹ := rfl

/-- The raw cocharacter has the actual integral coroot coordinates. -/
theorem rawRootCocharacter_coordinate (r : F4Chevalley.Root) (i : Fin 4)
    (t : Variety.Point (KMult F)) :
    dPointEquiv 4 ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints
      ((rawRootCocharacter r).onPoints t)) i =
        (dPointEquiv 1 t 0) ^ corootCoordinates r i := by
  change dPointEquiv 4 ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints
    ((F4Chevalley.splitTorusCocharacter (-corootCoordinates r)).onPoints t⁻¹)) i = _
  rw [F4Chevalley.splitTorusCocharacter_inverse_apply, dCharacterTupleMorphism_apply]
  simp [dPointEquiv_inv]

/-- The whole cocharacter family specializes to the corrected simple cocharacters. -/
theorem rawRootCocharacter_simple (i : Fin 4) :
    rawRootCocharacter (F := F) (typeF4SimpleRootIndex i) = rawSimpleCocharacter i := by
  apply Theory.AlgebraicGroup.Morphism.ext
  funext t
  apply (F4Chevalley.splitTorusIso (k := F)).toMulEquiv.symm.injective
  apply (dPointEquiv 4).injective
  funext j
  change dPointEquiv 4 ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints
    ((rawRootCocharacter (typeF4SimpleRootIndex i)).onPoints t)) j =
    dPointEquiv 4 ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints
    ((rawSimpleCocharacter i).onPoints t)) j
  rw [rawRootCocharacter_coordinate, rawSimpleCocharacter_coordinate,
    corootCoordinates_simple]
  split_ifs <;> simp

/-- Every pair of literal roots has the positive Cartan evaluation. -/
theorem rootWeight_rawRootCocharacter (r s : F4Chevalley.Root) :
    WeightCocharacterEquation (F4Chevalley.splitTorus (k := F))
      (F4Chevalley.rootWeight r) (rawRootCocharacter s)
      (typeF4RootPairing.pairingIn ℤ r s) := by
  intro t
  rw [F4Chevalley.rootWeight_pointCharacter]
  simp_rw [rawRootCocharacter_coordinate, ← zpow_mul]
  rw [← corootCoordinates_pairing r s, ← Units.val_zpow_eq_zpow_val]
  congr 1
  rw [Fin.sum_univ_four, Fin.prod_univ_four]
  simp only [zpow_add]

/-- Evaluation of any raw character on any raw root cocharacter. -/
theorem rawCharacter_rawRootCocharacter (a : Fin 4 → ℤ) (r : F4Chevalley.Root) :
    WeightCocharacterEquation (F4Chevalley.splitTorus (k := F))
      (rawCharacter a) (rawRootCocharacter r)
      (∑ i, corootCoordinates r i * a i) := by
  intro t
  change (dPointEquiv 1 ((F4Chevalley.splitTorusCharacter a).onPoints
    ((rawRootCocharacter r).onPoints t)) 0 : F) = _
  rw [F4Chevalley.splitTorusCharacter_apply_point]
  simp_rw [rawRootCocharacter_coordinate, ← zpow_mul]
  rw [← Units.val_zpow_eq_zpow_val]
  congr 1
  rw [Fin.sum_univ_four, Fin.prod_univ_four]
  simp only [zpow_add]

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
