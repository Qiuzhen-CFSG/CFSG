module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected.Coroots
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected.LiftedBase
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.CharacterPowers

/-!
# The standard labelled F4 root datum on the concrete split torus

The datum uses the literal root subgroups and raw weights, the integral coroot
cocharacters, and the original positive base. All realization clauses except
exhaustiveness are proved from these concrete formulas. `rootData_isRealization`
keeps exhaustiveness explicit, and `model` additionally requires maximality of
the literal split torus. These are assembly interfaces, not assertions of the
remaining geometric input. Source: GLS3 1.9.1--1.9.6 and 1.12.1.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance dataTorusGroup : AlgebraicGroup (F4Chevalley.splitTorus (k := F)).carrierVariety :=
  (F4Chevalley.splitTorus (k := F)).carrierAlgebraicGroup

private def rawCharacterHom : (Fin 4 → ℤ) →+ Additive (TorusWeight (F4Chevalley.splitTorus (k := F))) :=
  (TorusCharacter.pullback (F4Chevalley.splitTorusIso (k := F)).inv).toAdditive.comp
    (dLaurentCharacterHom 4)

private lemma rawCharacter_add (a b : Fin 4 → ℤ) :
    rawCharacter (F := F) (a + b) = rawCharacter a * rawCharacter b :=
  (rawCharacterHom (F := F)).map_add a b

private lemma rawCharacter_zsmul (n : ℤ) (a : Fin 4 → ℤ) :
    rawCharacter (F := F) (n • a) = rawCharacter a ^ n :=
  (rawCharacterHom (F := F)).map_zsmul n a

private lemma rootWeight_eq_raw (r : F4Chevalley.Root) :
    F4Chevalley.rootWeight (k := F) r = rawCharacter (F4Chevalley.torusRootExponent r) := by
  apply TorusCharacter.pointCharacter_injective
  ext s
  exact (F4Chevalley.rootWeight_pointCharacter r s).trans
    (congrArg Units.val (F4Chevalley.splitTorusCharacter_apply_point
      (F4Chevalley.torusRootExponent r) s)).symm

/-- Root addition is defined exactly when the sum of the actual real root vectors is a root. -/
def rootAdd (r s : F4Chevalley.Root) : Option F4Chevalley.Root :=
  if h : ∃ q, typeF4RootPairing.root q = typeF4RootPairing.root r + typeF4RootPairing.root s
  then some h.choose else none

theorem rootAdd_eq_some_iff (r s q : F4Chevalley.Root) :
    rootAdd r s = some q ↔
      typeF4RootPairing.root q = typeF4RootPairing.root r + typeF4RootPairing.root s := by
  classical
  simp only [rootAdd]
  split_ifs with h
  · constructor
    · intro he
      cases Option.some.inj he
      exact h.choose_spec
    · intro hq
      exact congrArg some (typeF4RootPairing.root.injective (h.choose_spec.trans hq.symm))
  · constructor
    · intro he
      cases he
    · intro hq
      exact (h ⟨q, hq⟩).elim

private lemma rootWeight_neg (r : F4Chevalley.Root) :
    F4Chevalley.rootWeight (k := F) (typeF4RootPairing.reflectionPerm r r) =
      (F4Chevalley.rootWeight r)⁻¹ := by
  rw [rootWeight_eq_raw, rootWeight_eq_raw, ← rawCharacter_neg]
  congr 1
  funext i
  exact typeF4RootPairing.pairingIn_reflectionPerm_self_left ℤ r _

private lemma rootWeight_add (r s q : F4Chevalley.Root) (h : rootAdd r s = some q) :
    F4Chevalley.rootWeight (k := F) q = F4Chevalley.rootWeight r * F4Chevalley.rootWeight s := by
  rw [rootWeight_eq_raw, rootWeight_eq_raw, rootWeight_eq_raw, ← rawCharacter_add]
  congr 1
  funext i
  exact RootPairing.pairingIn_eq_add_of_root_eq_add ((rootAdd_eq_some_iff r s q).mp h)

private lemma rootWeight_reflect (r s : F4Chevalley.Root) :
    F4Chevalley.rootWeight (k := F) (typeF4RootPairing.reflectionPerm r s) =
      F4Chevalley.rootWeight s *
        F4Chevalley.rootWeight r ^ (-typeF4RootPairing.pairingIn ℤ s r) := by
  rw [rootWeight_eq_raw, rootWeight_eq_raw, rootWeight_eq_raw,
    ← rawCharacter_zsmul, ← rawCharacter_add]
  congr 1
  funext i
  have h : typeF4RootPairing.root (typeF4RootPairing.reflectionPerm r s) =
      (1 : ℤ) • typeF4RootPairing.root s +
        (-typeF4RootPairing.pairingIn ℤ s r) • typeF4RootPairing.root r := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root' ℤ]
    simp [sub_eq_add_neg]
  simpa only [one_smul, Pi.add_apply, Pi.smul_apply, F4Chevalley.torusRootExponent] using
    (RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul (j := (typeF4RootPairing_baseEquiv i : F4Chevalley.Root)) h)

private lemma simple_iff (r : F4Chevalley.Root) :
    r ∈ typeF4RootPairing_base.support ↔ typeF4RootPairing_base.IsPos r ∧
      ∀ s q, rootAdd s q = some r →
        ¬ (typeF4RootPairing_base.IsPos s ∧ typeF4RootPairing_base.IsPos q) := by
  constructor
  · intro hr
    refine ⟨typeF4RootPairing_base.isPos_of_mem_support hr, ?_⟩
    rintro s q hadd ⟨hs, hq⟩
    have hheight := typeF4RootPairing_base.height_add ((rootAdd_eq_some_iff s q r).mp hadd)
    have hrh := typeF4RootPairing_base.height_one_of_mem_support hr
    change 0 < typeF4RootPairing_base.height s at hs
    change 0 < typeF4RootPairing_base.height q at hq
    omega
  · rintro ⟨hr, hind⟩
    have hh : typeF4RootPairing_base.IsPos r ∧
        (r ∈ typeF4RootPairing_base.support ∨
          ∃ s q, typeF4RootPairing_base.IsPos s ∧ typeF4RootPairing_base.IsPos q ∧
            typeF4RootPairing.root r = typeF4RootPairing.root s + typeF4RootPairing.root q) := by
      apply hr.induction_on_add
      · intro s hs
        exact ⟨typeF4RootPairing_base.isPos_of_mem_support hs, Or.inl hs⟩
      · intro s q z hz hs hq
        exact ⟨hs.1.add (typeF4RootPairing_base.isPos_of_mem_support hq) hz,
          Or.inr ⟨s, q, hs.1, typeF4RootPairing_base.isPos_of_mem_support hq, hz⟩⟩
    rcases hh.2 with h | ⟨s, q, hs, hq, he⟩
    · exact h
    · exact (hind s q ((rootAdd_eq_some_iff s q r).mpr he) ⟨hs, hq⟩).elim

/-- Literal F4 data with the raw inverse-conjugation convention and standard positive labels. -/
def rootData : RootGroupData (F4Chevalley.Carrier (k := F)) (F4Chevalley.splitTorus (k := F)) where
  Root := TypeF4RootIndexULift.{u}
  rootWeight := fun r => F4Chevalley.rootWeight r.down
  rootSubgroup := fun r => F4Chevalley.rootSubgroup r.down
  neg := fun r => ⟨typeF4RootPairing.reflectionPerm r.down r.down⟩
  add := fun r s => (rootAdd r.down s.down).map ULift.up
  pairing := fun r s => typeF4RootPairing.pairingIn ℤ r.down s.down
  weightPairing := fun χ s => characterCocharacterPairing (F4Chevalley.splitTorus (k := F))
    (rawRootCocharacter s.down) (Additive.ofMul χ)
  rootCocharacter := fun r => rawRootCocharacter r.down
  reflect := fun r s => ⟨typeF4RootPairing.reflectionPerm r.down s.down⟩
  positive := fun r => typeF4RootPairing_base.IsPos r.down
  simple := fun r => r.down ∈ typeF4RootPairing_base.support
  height := fun r => typeF4RootPairing_base.height r.down

private lemma rootData_add_iff (r s q : TypeF4RootIndexULift.{u}) :
    (rootData (F := F)).add r s = some q ↔ rootAdd r.down s.down = some q.down := by
  change Option.map ULift.up _ = some q ↔ _
  simp only [Option.map_eq_some_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro h
    exact ⟨q.down, h, rfl⟩

/-- The concrete datum realizes the root system once root exhaustiveness is supplied. -/
theorem rootData_isRealization
    (hexhaust : Set.range (F4Chevalley.rootWeight (k := F)) =
      TorusRootSet (F4Chevalley.splitTorus (k := F))) :
    (rootData (F := F)).IsRealization := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r s h
    exact ULift.ext _ _ (F4Chevalley.concreteRootWeight_injective h)
  · rw [← hexhaust]
    ext χ
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r.down, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨⟨r⟩, rfl⟩
  · intro r
    exact F4Chevalley.rootSubgroup_package r.down
  · intro r
    exact rootWeight_neg r.down
  · intro r s q h
    exact rootWeight_add r.down s.down q.down ((rootData_add_iff r s q).mp h)
  · intro r s
    exact rootWeight_reflect r.down s.down
  · intro r
    exact typeF4RootPairing.pairingIn_same ℤ r.down
  · intro r s
    exact (weightCocharacterEquation_existsUnique (F4Chevalley.splitTorus (k := F))
      (F4Chevalley.rootWeight r.down) (rawRootCocharacter s.down)).unique
      (characterCocharacterPairing_spec _ _ _) (rootWeight_rawRootCocharacter r.down s.down)
  · intro r
    exact typeF4RootPairing_base.height_reflectionPerm_self r.down
  · intro r s q h
    exact typeF4RootPairing_base.height_add
      ((rootAdd_eq_some_iff _ _ _).mp ((rootData_add_iff r s q).mp h))
  · rfl
  · intro r
    change r.down ∈ typeF4RootPairing_base.support ↔ _
    rw [simple_iff]
    constructor
    · rintro ⟨hr, hind⟩
      exact ⟨hr, fun s q h => hind s.down q.down ((rootData_add_iff s q r).mp h)⟩
    · rintro ⟨hr, hind⟩
      exact ⟨hr, fun s q h => hind ⟨s⟩ ⟨q⟩ ((rootData_add_iff ⟨s⟩ ⟨q⟩ r).mpr h)⟩
  · intro χ r
    exact characterCocharacterPairing_spec _ _ _

/-- The underlying real root pairing and its base are the actual standard F4 pairing. -/
theorem rootData_actual : IsActualBasedRootPairing (rootData (F := F))
    typeF4RootPairingULift typeF4RootPairingULift_base (Equiv.refl _) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s
    exact lifted_pairing r s
  · intro r s
    exact lifted_reflect r s
  · intro r
    exact lifted_reflect r r
  · intro r
    exact lifted_mem_base r

/-- Assembly of the literal model from the two remaining geometric inputs. -/
def model
    (hexhaust : Set.range (F4Chevalley.rootWeight (k := F)) =
      TorusRootSet (F4Chevalley.splitTorus (k := F)))
    (hmax : IsMaximalTorus (F4Chevalley.splitTorus (k := F))) :
    RootSystemModel typeF4RootPairingULift (F4Chevalley.Carrier (k := F)) where
  torus := F4Chevalley.splitTorus
  maximalTorus := hmax
  rootData := rootData
  realization := rootData_isRealization hexhaust
  base := typeF4RootPairingULift_base
  rootEquiv := Equiv.refl _
  actual := rootData_actual

/-- Pointwise identification with the literal root subgroups. -/
theorem rootData_rootSubgroup (r : F4Chevalley.Root) :
    (rootData (F := F)).rootSubgroup ⟨r⟩ = F4Chevalley.rootSubgroup r := rfl

/-- Pointwise identification with the literal inverse-conjugation root weights. -/
theorem rootData_rootWeight (r : F4Chevalley.Root) :
    (rootData (F := F)).rootWeight ⟨r⟩ = F4Chevalley.rootWeight r := rfl

/-- Positivity keeps exactly the original root labels. -/
theorem rootData_positive (r : F4Chevalley.Root) :
    (⟨r⟩ : (rootData (F := F)).Root) ∈ (rootData (F := F)).positive ↔
      typeF4RootPairing_base.IsPos r := Iff.rfl

/-- The model's numbered simple cocharacters include as inverse-parameter representation words. -/
theorem rootData_simpleCocharacter_inclusion (i : Fin 4) (t : Variety.Point (KMult F)) :
    (F4Chevalley.splitTorus (k := F)).inclusion.onPoints
      (((rootData (F := F)).rootCocharacter ⟨typeF4SimpleRootIndex i⟩).onPoints t) =
      algebraicCorootElement (typeF4SimpleRootIndex i) ((dPointEquiv 1 t 0)⁻¹) := by
  change (F4Chevalley.splitTorus (k := F)).inclusion.onPoints
    ((rawRootCocharacter (typeF4SimpleRootIndex i)).onPoints t) = _
  rw [rawRootCocharacter_simple, rawSimpleCocharacter_inclusion]

/-- Raw characters are faithfully indexed by their four simple-coroot evaluations. -/
theorem rawCharacter_injective : Function.Injective (rawCharacter (F := F)) := by
  intro a b h
  funext i
  apply (weightCocharacterEquation_existsUnique (F4Chevalley.splitTorus (k := F))
    (rawCharacter a) (rawSimpleCocharacter i)).unique
    (rawCharacter_rawSimpleCocharacter a i)
  rw [h]
  exact rawCharacter_rawSimpleCocharacter b i

private lemma root_eq_add_of_exponents (r s q : F4Chevalley.Root)
    (h : F4Chevalley.torusRootExponent q =
      F4Chevalley.torusRootExponent r + F4Chevalley.torusRootExponent s) :
    typeF4RootPairing.root q = typeF4RootPairing.root r + typeF4RootPairing.root s := by
  apply typeF4RootPairing.toLinearMap.toPerfPair.injective
  apply typeF4RootPairing_base.flip.toWeightBasis.ext
  intro j
  let j' : typeF4RootPairing_base.support :=
    ⟨j.val, by simpa only [RootPairing.Base.flip_support] using j.property⟩
  have hjZ := congrFun h (typeF4RootPairing_baseEquiv.symm j')
  simp only [F4Chevalley.torusRootExponent, Pi.add_apply, Equiv.apply_symm_apply] at hjZ
  have hj := congrArg (algebraMap ℤ ℝ) hjZ
  simp only [map_add, typeF4RootPairing.algebraMap_pairingIn] at hj
  simp only [RootPairing.Base.toWeightBasis_apply, LinearMap.toPerfPair_apply,
    map_add, LinearMap.add_apply]
  exact hj

/-- Addition also satisfies the converse source clause: every root-valued sum is represented. -/
theorem rootData_isRootAdditionComplete : (rootData (F := F)).IsRootAdditionComplete := by
  intro r s q h
  apply (rootData_add_iff r s q).mpr
  apply (rootAdd_eq_some_iff _ _ _).mpr
  apply root_eq_add_of_exponents
  apply rawCharacter_injective (F := F)
  change F4Chevalley.rootWeight q.down =
    F4Chevalley.rootWeight r.down * F4Chevalley.rootWeight s.down at h
  rw [rootWeight_eq_raw, rootWeight_eq_raw, rootWeight_eq_raw] at h
  rwa [rawCharacter_add]

/-- The direct left-action character at a root is the inverse of its raw root character. -/
theorem leftRootCharacter_eq_inverse (r : F4Chevalley.Root) :
    leftCharacter (F := F) (F4Chevalley.torusRootExponent r) =
      (F4Chevalley.rootWeight r)⁻¹ := by
  change rawCharacter (-F4Chevalley.torusRootExponent r) = _
  rw [rawCharacter_neg, ← rootWeight_eq_raw]

/-- Direct conjugation uses the left character, with the literal positive root labels unchanged. -/
theorem direct_root_conjugation (r : F4Chevalley.Root) (a : F)
    (s : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety) :
    (F4Chevalley.splitTorus (k := F)).includePoint s *
      (F4Chevalley.rootMorphism r).onPoints (kPlusPoint a) *
        ((F4Chevalley.splitTorus (k := F)).includePoint s)⁻¹ =
      (F4Chevalley.rootMorphism r).onPoints
        (kPlusPoint ((leftCharacter (F4Chevalley.torusRootExponent r)).pointCharacter s * a)) := by
  have h := F4Chevalley.rootMorphism_splitTorus_conjugation r a s⁻¹
  change ((F4Chevalley.splitTorus (k := F)).inclusion.onPoints s⁻¹)⁻¹ * _ *
    (F4Chevalley.splitTorus (k := F)).inclusion.onPoints s⁻¹ = _ at h
  rw [map_inv, inv_inv] at h
  have hc : (F4Chevalley.rootWeight (k := F) r).pointCharacter s⁻¹ =
      (leftCharacter (F4Chevalley.torusRootExponent r)).pointCharacter s := by
    rw [leftRootCharacter_eq_inverse]
    change (dPointEquiv 1 ((F4Chevalley.rootWeight r).onPoints s⁻¹) 0 : F) =
      (dPointEquiv 1 ((F4Chevalley.rootWeight r).onPoints s)⁻¹ 0 : F)
    rw [map_inv]
  rwa [hc] at h

/-- The left character coordinates also give an actual embedding of the integral weight lattice. -/
theorem leftCharacter_injective : Function.Injective (leftCharacter (F := F)) := by
  intro a b h
  exact neg_injective (rawCharacter_injective h)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
