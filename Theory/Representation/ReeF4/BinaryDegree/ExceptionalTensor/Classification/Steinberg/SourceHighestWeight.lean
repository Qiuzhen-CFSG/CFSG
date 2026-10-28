module
public import Theory.AlgebraicGroup.Borel.HighestWeight
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.CoefficientFrobenius
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.Assembly
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Coordinates

/-!
# Source highest-weight uniqueness on the literal F4 carrier

The source highest vector is fixed by every positive root curve and has the
specified eigenvalue on each positive coroot word. The actual positive Borel
is the product of the split torus and those root groups. Its torus is the
product of the same four coroot words, so the vector has the regular left
character with these coefficients. The proved opposite big cell then gives
uniqueness of the irreducible algebraic factor and uniqueness of its weight.

The literal coefficient-Frobenius theorem is an actual consumer: its former
highest-weight uniqueness premise is now discharged. Finite restriction and
existence of the restricted factors remain separate source obligations.
Source: GLS3 Section 1.14; Steinberg, Endomorphisms, Sections 13.1–13.3.
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceHighestWeight
open Geometry Geometry.RootModel.Corrected
open ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance : AlgebraicGroup (F4Chevalley.splitTorus (k := F)).carrierVariety :=
  (F4Chevalley.splitTorus (k := F)).carrierAlgebraicGroup

private def corootPoint (i : Fin 4) (t : Fˣ) :
    Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety :=
  (F4Chevalley.splitTorusSimpleCoroot i).onPoints ((dPointEquiv 1).symm (fun _ => t))

private theorem corootPoint_include (i : Fin 4) (t : Fˣ) :
    (F4Chevalley.splitTorus (k := F)).inclusion.onPoints (corootPoint i t) =
      algebraicCorootElement (typeF4SimpleRootIndex i) t := by
  simp [corootPoint, splitTorusSimpleCoroot_eq_algebraicCoroot]

private theorem corootPoint_character (a : Weight) (i : Fin 4) (t : Fˣ) :
    (leftCharacter (fun i => (a i : ℤ))).pointCharacter (corootPoint i t) =
      (t : F) ^ a i := by
  simpa [corootPoint] using
    leftCharacter_representationCoroot (F := F) (fun i => (a i : ℤ)) i
      ((dPointEquiv 1).symm (fun _ => t))

private theorem highestVector_torus (B : AlgebraicFactor F) (a : Weight)
    (v : B.Space)
    (hcor : ∀ i t, (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = (t : F) ^ a i • v)
    (s : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety) :
    (B.action.action ((F4Chevalley.splitTorus (k := F)).includePoint s) :
      Module.End F B.Space) v =
        (leftCharacter (fun i => (a i : ℤ))).pointCharacter s • v := by
  obtain ⟨t, ht⟩ := (TorusCoverage.mem_splitTorus_iff _).mp
    ((F4Chevalley.splitTorus (k := F)).pointEquiv s).property
  change corootTorusElement t = (F4Chevalley.splitTorus (k := F)).inclusion.onPoints s at ht
  have hs : s = corootPoint 0 (t 0) * corootPoint 1 (t 1) *
      corootPoint 2 (t 2) * corootPoint 3 (t 3) := by
    apply (F4Chevalley.splitTorus (k := F)).inclusion_injective
    simpa only [map_mul, corootPoint_include, corootTorusElement] using ht.symm
  rw [hs]
  change (B.action.action ((F4Chevalley.splitTorus (k := F)).inclusion.onPoints
    (corootPoint 0 (t 0) * corootPoint 1 (t 1) * corootPoint 2 (t 2) * corootPoint 3 (t 3))) :
      Module.End F B.Space) v = _
  simp only [map_mul, corootPoint_include, Units.val_mul, Module.End.mul_apply,
    hcor, map_smul, corootPoint_character, smul_smul]
  congr 1
  ring

variable [CharP F 2]

private theorem highestVector_positive (B : AlgebraicFactor F) (v : B.Space)
    (hpos : ∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r → ∀ t : F,
      (B.action.action (algebraicRootElement r t) : Module.End F B.Space) v = v)
    (g : PointGroup F)
    (hg : g ∈ RootSubgroupGenerated (rootSystemModel (F := F)).rootData
      (OppositeBorels.positiveRoots F)) :
    (B.action.action g : Module.End F B.Space) v = v := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, hr, hx⟩ := Set.mem_iUnion₂.mp hx
    change x ∈ F4Chevalley.rootSubgroup r.down at hx
    obtain ⟨t, rfl⟩ := hx
    have ht : kPlusPoint ((additiveGroupPointEquiv F t).toAdd) = t := by
      apply (additiveGroupPointEquiv F).injective
      rfl
    simpa only [algebraicRootElement, ht] using
      hpos r.down hr ((additiveGroupPointEquiv F t).toAdd)
  | one => simp
  | mul x y hx hy ihx ihy =>
    simpa [map_mul, ihy] using ihx
  | inv x hx ih =>
    have he := congrArg (fun w => (B.action.action x⁻¹ : Module.End F B.Space) w) ih
    simpa [← Module.End.mul_apply, ← Units.val_mul, ← map_mul] using he.symm

/-- The raw source vector is a highest vector for the actual positive Borel. -/
theorem hasHighWeight_of_source_vector (B : AlgebraicFactor F) (a : Weight)
    (v : B.Space) (hv : v ≠ 0)
    (hpos : ∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r → ∀ t : F,
      (B.action.action (algebraicRootElement r t) : Module.End F B.Space) v = v)
    (hcor : ∀ i t, (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = (t : F) ^ a i • v) :
    HasHighWeight B.action (OppositeBorels.bigCell F).data.B
      (F4Chevalley.splitTorus (k := F)) v (leftCharacter (fun i => (a i : ℤ))) := by
  have htor := highestVector_torus B a v hcor
  refine ⟨⟨hv, ?_⟩, hv, htor⟩
  intro g hg
  obtain ⟨t, u, ht, hu, rfl⟩ := (OppositeBorels.positive_decomposition F g).mp hg
  let s := (F4Chevalley.splitTorus (k := F)).pointEquiv.symm ⟨t, ht⟩
  have hs : (F4Chevalley.splitTorus (k := F)).includePoint s = t := by
    change ((F4Chevalley.splitTorus (k := F)).pointEquiv s).val = t
    simp [s]
  refine ⟨(leftCharacter (fun i => (a i : ℤ))).pointCharacter s, ?_⟩
  rw [map_mul]
  change (B.action.action t : Module.End F B.Space)
    ((B.action.action u : Module.End F B.Space) v) = _
  rw [highestVector_positive B v hpos u hu, ← hs, htor]

/-- Actual algebraic factors with the same source highest weight are equivalent. -/
theorem equivalent_of_same_highestWeight (B C : AlgebraicFactor F) (a : Weight)
    (hB : HasHighestWeight B a) (hC : HasHighestWeight C a) :
    AreEquivalentRepresentations B.action C.action := by
  obtain ⟨v, hv, hp, hc⟩ := hB
  obtain ⟨w, hw, hq, hd⟩ := hC
  exact irreducible_highWeight_equivalent_of_oppositeBorelBigCell
    (OppositeBorels.bigCell F) splitTorus_isMaximal B.action C.action B.irreducible C.irreducible
    v w _ (hasHighWeight_of_source_vector B a v hv hp hc)
      (hasHighWeight_of_source_vector C a w hw hq hd)


/-- The actual source weights distinguish equivalent rational irreducible factors. -/
theorem highestWeight_eq_of_equivalent (B C : AlgebraicFactor F) (a d : Weight)
    (hB : HasHighestWeight B a) (hC : HasHighestWeight C d)
    (heq : AreEquivalentRepresentations B.action C.action) : a = d := by
  obtain ⟨e, he⟩ := heq
  obtain ⟨v, hv, hp, hc⟩ := hB
  obtain ⟨w, hw, hq, hd⟩ := hC
  have hev : e v ≠ 0 := by simpa using hv
  have hep (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r) (t : F) :
      (C.action.action (algebraicRootElement r t) : Module.End F C.Space) (e v) = e v := by
    have h := he (algebraicRootElement r t) v
    change e ((B.action.action (algebraicRootElement r t) : Module.End F B.Space) v) = _ at h
    rw [hp r hr] at h
    exact h.symm
  have hec (i : Fin 4) (t : Fˣ) :
      (C.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
        Module.End F C.Space) (e v) = (t : F) ^ a i • e v := by
    have h := he (algebraicCorootElement (typeF4SimpleRootIndex i) t) v
    change e ((B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v) = _ at h
    rw [hc, map_smul] at h
    exact h.symm
  obtain ⟨c, hcn, hwc⟩ := irreducible_highWeight_unique_line_of_oppositeBorelBigCell
    (OppositeBorels.bigCell F) splitTorus_isMaximal C.action C.irreducible (e v) w _ _
      (hasHighWeight_of_source_vector C a (e v) hev hep hec)
      (hasHighWeight_of_source_vector C d w hw hq hd)
  funext i
  by_contra hne
  have hdiff : (a i : ℤ) - d i ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  obtain ⟨t, ht⟩ := exists_unit_zpow_ne_one (k := F) hdiff
  have hwa : (C.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F C.Space) w = (t : F) ^ a i • w := by
    rw [hwc, map_smul, hec]
    simp [smul_smul, mul_comm]
  have hpow : (t : F) ^ a i = (t : F) ^ d i :=
    smul_left_injective F hw (hwa.symm.trans (hd i t))
  apply ht
  rw [zpow_sub, mul_inv_eq_one]
  apply Units.ext
  simpa using hpow

/-- The basic algebraic uniqueness premise in coefficient Frobenius is discharged. -/
theorem equivalent_of_same_basicHighestWeight (B C : AlgebraicFactor F)
    (b : BasicWeight) (hB : HasBasicHighestWeight B b) (hC : HasBasicHighestWeight C b) :
    AreEquivalentRepresentations B.action C.action :=
  equivalent_of_same_highestWeight B C (basicCoefficient b) hB hC

/-- The literal coefficient-Frobenius shift now has no extra representation premise. -/
theorem character_shift {m : ℕ} (f : CoefficientField m →+* F)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (hB : ∀ i, (B i).IsExceptionalBasic)
    (r : ℕ) (g : Model m) :
    Representation.character (exceptionalTensor (splitEmbedding f) B).ρ g ^ (2 ^ r) =
      Representation.character (exceptionalTensor (splitEmbedding f) (shiftFactors B r)).ρ g :=
  CoefficientFrobenius.character_shift equivalent_of_same_basicHighestWeight f B hB r g

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceHighestWeight
