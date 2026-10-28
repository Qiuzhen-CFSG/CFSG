module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.SixPointModel.LinearIdentification
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.SixPointModel.OrthogonalDuality.Perpendicular
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.SixPointModel.OrthogonalDuality.Quadratic

/-!
# Orthogonal duality for the genuine six-point hexad cocode module

The native supported M22 cocode image is the deleted module on the six actual
coordinates. Its perfect dot pairing identifies it with the dual of the
perpendicular to the marked pair in the natural octad module. Zero extension
identifies that perpendicular with the even six-coordinate module, respecting
the actual stabilizer actions and the half-weight quadratic forms.

The pair has quadratic value one. Accordingly the quadratic form is restricted
to its perpendicular, never descended through its line. The cocode quotient
and the orthogonal module remain distinguished; no self-duality is assumed.
The fixed-space corollaries retain exactly the earlier scalar inputs of
`LinearIdentification`; group-image recognition and H.16 chief-factor
identifications belong to their separate assembly owners.

Source: Aschbacher--Smith, H.15.2(2), printed pp.398--399, combined manuscript
of 1 March 2004.
-/

@[expose] public section
open scoped BigOperators
open Representation.BinaryOffender Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.Hexad.CocodeAction.SixPointModel.OrthogonalDuality
noncomputable section
open BinaryPermutation

lemma weight_zeroExtend (v : core H) : hammingNorm (zeroExtend v).val = hammingNorm v.val := by
  simp only [Atlas.Codes.hammingNorm_eq_sum]
  change (∑ i, if zeroExtendFull v.val i = 0 then 0 else 1) = _
  rw [sum_octad]
  simp

/-- The quadratic form on the pair perpendicular, not on the cocode quotient. -/
def perpendicularQuadratic : QuadraticForm (ZMod 2) perpendicular :=
  octadQuadratic.comp perpendicular.subtype

lemma perpendicularQuadratic_polar (v w : perpendicular) :
    perpendicularQuadratic.polarBilin v w = naturalPairing O.val v.val w.val :=
  octadQuadratic_polar v.val w.val

/-- On the even six-coordinate module, the restricted form is half the weight. -/
lemma perpendicularQuadratic_apply (v : core H) :
    perpendicularQuadratic (corePerpendicularEquiv v) = (hammingNorm v.val / 2 : ℕ) := by
  change octadQuadratic (coreToNatural O.val (zeroExtend v)) = _
  rw [octadQuadratic_apply_core, weight_zeroExtend]

/-- The actual linear identification also identifies the quadratic geometry. -/
def corePerpendicularIsometry : (evenQuadratic H).IsometryEquiv perpendicularQuadratic :=
  { corePerpendicularEquiv with map_app' := perpendicularQuadratic_apply }

lemma perpendicularQuadratic_invariant {G : Type*} [Group G]
    (f : G →* m22PairStabilizer) (g : Stabilizer f) (v : perpendicular) :
    perpendicularQuadratic (perpendicularRepresentation f g v) = perpendicularQuadratic v :=
  octadQuadratic_invariant _ v.val

/-- The pair is perpendicular to itself in characteristic two. -/
lemma pair_mem_perpendicular : pairVector ∈ perpendicular := by
  apply (mem_perpendicular_iff pairWord).mpr
  decide +kernel

/-- The marked nonsingular vector in the perpendicular space. -/
def perpendicularPair : perpendicular := ⟨pairVector, pair_mem_perpendicular⟩

lemma perpendicularQuadratic_pair : perpendicularQuadratic perpendicularPair = 1 :=
  octadQuadratic_pair

/-- The even six-point constant word corresponds to the octad pair class. -/
def sixConstant : core H := ⟨allOne H, by
  change augmentation H (allOne H) = 0
  rw [augmentation_allOne, card_H]
  rfl⟩

lemma corePerpendicularEquiv_sixConstant :
    corePerpendicularEquiv sixConstant = perpendicularPair := by
  apply Subtype.ext
  apply Subtype.ext
  change (constants O.val).mkQ (zeroExtend sixConstant).val = (constants O.val).mkQ pairWord.val
  apply (Submodule.Quotient.eq _).mpr
  apply Submodule.mem_span_singleton.mpr
  refine ⟨1, ?_⟩
  decide +kernel

/-- The even six-coordinate polar radical is exactly the constant line. -/
lemma evenQuadratic_polar_zero_iff (v : core H) :
    (evenQuadratic H).polarBilin v = 0 ↔ v.val ∈ constants H := by
  rw [← ker_fullCorePairing H]
  change (evenQuadratic H).polarBilin v = 0 ↔ fullCorePairing H v.val = 0
  have he : (evenQuadratic H).polarBilin v = fullCorePairing H v.val := by
    ext w
    exact evenQuadratic_polar H v w
  rw [he]

/-- The polar radical of the odd-dimensional orthogonal module is nonsingular. -/
lemma evenQuadratic_radical_eq_bot : (evenQuadratic H).radical = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((evenQuadratic_polar_zero_iff v).mp hv.2)
  have hc0 : c = 0 := by
    have hq := hv.1
    change ((hammingNorm v.val / 2 : ℕ) : ZMod 2) = 0 at hq
    rw [← hc] at hq
    have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
    rcases hcases c with rfl | rfl
    · rfl
    · have h : hammingNorm (allOne H) = 6 := by decide +kernel
      simp only [one_smul, h] at hq
      change (1 : ZMod 2) = 0 at hq
      exact hq
  apply Subtype.ext
  simpa [hc0] using hc.symm

lemma perpendicularQuadratic_radical_eq_bot : perpendicularQuadratic.radical = ⊥ := by
  rw [← corePerpendicularIsometry.map_radical, evenQuadratic_radical_eq_bot, Submodule.map_bot]

/-- Transfer of the fixed space using precisely the published earlier M24/H.14 inputs. -/
def fixedPerpendicularDualEquiv {G : Type*} [Group G]
    {f : G →* m22PairStabilizer} {K : Subgroup G}
    (h : RestrictionInput f K O)
    (hd : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (h6 : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (octadPointwiseKernel O)) = 6) :
    fixedSpace (quotientRepresentation f) K ≃ₗ[ZMod 2] Module.Dual (ZMod 2) perpendicular :=
  (fixedEquiv h hd h6).trans ((deletedCoreDualEquiv H).trans corePerpendicularEquiv.symm.dualMap)

lemma fixedPerpendicularDualEquiv_apply {G : Type*} [Group G]
    {f : G →* m22PairStabilizer} {K : Subgroup G}
    (h : RestrictionInput f K O)
    (hd : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (h6 : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (octadPointwiseKernel O)) = 6)
    (v : core O.val) (w : core H) :
    fixedPerpendicularDualEquiv h hd h6
      ⟨toM22 v, imageSpace_le_fixed h.kernel_image (LinearMap.mem_range_self _ _)⟩
      (corePerpendicularEquiv w) =
        naturalPairing O.val (coreToNatural O.val v) (corePerpendicularEquiv w).val := by
  change deletedCoreDualEquiv H (fixedEquiv h hd h6 _) (corePerpendicularEquiv.symm
    (corePerpendicularEquiv w)) = _
  rw [fixedEquiv_apply, LinearEquiv.symm_apply_apply, deletedCoreDualEquiv_mk,
    corePerpendicularEquiv_apply, pairing_zeroExtend]
  rfl

lemma fixedPerpendicularDualEquiv_equivariant {G : Type*} [Group G]
    {f : G →* m22PairStabilizer} {K : Subgroup G}
    (h : RestrictionInput f K O)
    (hd : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (h6 : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (octadPointwiseKernel O)) = 6)
    (g : Stabilizer f) (v : fixedSpace (quotientRepresentation f) K) :
    fixedPerpendicularDualEquiv h hd h6
      ⟨quotientRepresentation f g.val v.val, fixedSpace_invariant h hd h6 g v.property⟩ =
      (perpendicularRepresentation f).dual g (fixedPerpendicularDualEquiv h hd h6 v) := by
  exact imagePerpendicularDualEquiv_equivariant f g
    ⟨v.val, (fixedSpace_eq_image h hd h6) ▸ v.property⟩

end
end MathieuCode.Hexad.CocodeAction.SixPointModel.OrthogonalDuality
