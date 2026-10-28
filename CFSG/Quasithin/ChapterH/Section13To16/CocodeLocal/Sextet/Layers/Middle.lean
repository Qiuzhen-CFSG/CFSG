module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Sextet.Geometry
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.NativeMiddle

/-!
# The native middle sextet factor and its translation action

Restricting the code-preserving cocode equivalence to the pair space and then
quotienting by the tetrad line transports the ATLAS dot pairing to the literal
native middle quotient. Its intertwining equation identifies this quotient
with the dual of conjugation on the transported translation subgroup. Thus the
middle factor is irreducible, with exactly the translations as action kernel.
The same coordinates transfer translation displacements into the tetrad line.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.3(1),
printed p.400 (PDF p.411). Intrinsic-kernel identification remains separate.
The ATLAS constructions are by Gerald Höhn and ATLAS contributors, under the
ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt and the
attribution in the imported coordinate and pairing modules.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode MathieuCode.SextetLayers MathieuCode.SextetLayers.CoordinateTransport

/-- The restricted coordinate map on the chapter's exact pair-space carrier. -/
def sextetPairCoordinateEquiv (S : Sextet) : atlasPairSpace ≃ₗ[ZMod 2]
    (sextetPairSubrepresentation S).toSubmodule := nativePairEquiv S

/-- The quotient coordinate map on the chapter's exact middle-section carrier. -/
def sextetMiddleCoordinateEquiv (S : Sextet) : AtlasMiddle ≃ₗ[ZMod 2]
    ((sextetPairSubrepresentation S).toSubmodule ⧸ (sextetLineInPair S).toSubmodule) :=
  nativeMiddleEquiv S

lemma sextetMiddleCoordinateEquiv_mk (S : Sextet) (v : atlasPairSpace) :
    sextetMiddleCoordinateEquiv S (atlasLineInPair.mkQ v) =
      (sextetLineInPair S).toSubmodule.mkQ (sextetPairCoordinateEquiv S v) := rfl

/-- The native middle action in the coordinates of the actual affine stabilizer. -/
lemma sextetMiddleCoordinate_equivariant (S : Sextet) (s : Atlas.Codes.SextetStabilizer)
    (v : AtlasMiddle) :
    sextetMiddleCoordinateEquiv S (atlasMiddleRepresentation s v) =
      (sextetLineInPair S).quotientRepresentation (nativeStabilizerEquiv S s)
        (sextetMiddleCoordinateEquiv S v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ w =>
    change (sextetLineInPair S).toSubmodule.mkQ
        (sextetPairCoordinateEquiv S (atlasPairRepresentation s w)) =
      (sextetLineInPair S).toSubmodule.mkQ
        ((sextetPairSubrepresentation S).toRepresentation (nativeStabilizerEquiv S s)
          (sextetPairCoordinateEquiv S w))
    apply congrArg (sextetLineInPair S).toSubmodule.mkQ
    apply Subtype.ext
    exact nativeCocodeEquiv_equivariant S s w.val

/-- The literal native middle quotient is the dual hexacode. -/
def sextetMiddleModelEquiv (S : Sextet) :
    ((sextetPairSpace S) ⧸ (sextetLineInPair S).toSubmodule) ≃ₗ[ZMod 2]
      Module.Dual (ZMod 2) Atlas.Codes.hexacode :=
  (sextetMiddleCoordinateEquiv S).symm.trans atlasMiddleDualEquiv

/-- Pairing in compatible Golay coordinates computes the native identification. -/
lemma sextetMiddleModelEquiv_mk (S : Sextet) (v : atlasPairSpace) :
    sextetMiddleModelEquiv S ((sextetLineInPair S).toSubmodule.mkQ (sextetPairCoordinateEquiv S v)) =
      atlasPairHexPairing v := by
  change atlasMiddleDualEquiv ((sextetMiddleCoordinateEquiv S).symm
    ((sextetLineInPair S).toSubmodule.mkQ (sextetPairCoordinateEquiv S v))) = _
  rw [← sextetMiddleCoordinateEquiv_mk, (sextetMiddleCoordinateEquiv S).symm_apply_apply,
    atlasMiddleDualEquiv_apply, atlasMiddlePairing_mk]

/-- The middle identification intertwines the actual quotient and conjugation-dual actions. -/
lemma sextetMiddleModelEquiv_equivariant (S : Sextet) (g : sextetStabilizer S)
    (v : (sextetPairSpace S) ⧸ (sextetLineInPair S).toSubmodule) :
    sextetMiddleModelEquiv S ((sextetLineInPair S).quotientRepresentation g v) =
      (nativeHexacodeRepresentation S).dual g (sextetMiddleModelEquiv S v) := by
  obtain ⟨s, rfl⟩ := (nativeStabilizerEquiv S).surjective g
  obtain ⟨w, rfl⟩ := (sextetMiddleCoordinateEquiv S).surjective v
  rw [← sextetMiddleCoordinate_equivariant]
  change atlasMiddleDualEquiv ((sextetMiddleCoordinateEquiv S).symm
      (sextetMiddleCoordinateEquiv S (atlasMiddleRepresentation s w))) =
    (nativeHexacodeRepresentation S).dual (nativeStabilizerEquiv S s)
      (atlasMiddleDualEquiv ((sextetMiddleCoordinateEquiv S).symm (sextetMiddleCoordinateEquiv S w)))
  rw [(sextetMiddleCoordinateEquiv S).symm_apply_apply, (sextetMiddleCoordinateEquiv S).symm_apply_apply,
    nativeHexacodeRepresentation_dual_apply]
  exact atlasMiddleDualEquiv_equivariant s w

/-- A genuine equivalence of representations for the literal native middle section. -/
def sextetMiddleRepresentationEquiv (S : Sextet) :
    (sextetLineInPair S).quotientRepresentation.Equiv (nativeHexacodeRepresentation S).dual :=
  .mk (sextetMiddleModelEquiv S)
    (fun g => LinearMap.ext (sextetMiddleModelEquiv_equivariant S g))

lemma sextetMiddle_isIrreducible (S : Sextet) :
    Representation.IsIrreducible (sextetLineInPair S).quotientRepresentation := by
  let e := sextetMiddleRepresentationEquiv S
  let f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ e.toIntertwiningMap
  let E := LinearEquiv.ofBijective f (show Function.Bijective f from e.toLinearEquiv.bijective)
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact E.isSimpleModule_iff.mpr
    ((Representation.irreducible_iff_isSimpleModule_asModule _).mp
      (nativeHexacodeRepresentation_dual_isIrreducible S))

/-- The middle quotient has exactly the native affine translations as action kernel. -/
lemma sextetMiddle_action_kernel (S : Sextet) :
    (sextetLineInPair S).quotientRepresentation.ker = (nativeTranslation S).range := by
  rw [← nativeHexacodeRepresentation_dual_kernel]
  ext g
  change (sextetLineInPair S).quotientRepresentation g = 1 ↔
    (nativeHexacodeRepresentation S).dual g = 1
  constructor
  · intro hg
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := (sextetMiddleModelEquiv S).surjective v
    rw [← sextetMiddleModelEquiv_equivariant, LinearMap.congr_fun hg]
    rfl
  · intro hg
    apply LinearMap.ext
    intro v
    apply (sextetMiddleModelEquiv S).injective
    rw [sextetMiddleModelEquiv_equivariant, hg]
    rfl

/-- Every actual native translation displaces the pair space into the tetrad line. -/
lemma sextetTranslation_displacement (S : Sextet) (t : Multiplicative Atlas.Codes.hexacode)
    {v : Cocode} (hv : v ∈ sextetPairSpace S) :
    sextetRepresentation S (nativeTranslation S t) v - v ∈ sextetTetradLine S :=
  nativeTranslation_displacement S t hv

/-- The line is a genuine simple factor of the native flag. -/
lemma sextetLine_isIrreducible (S : Sextet) :
    Representation.IsIrreducible (sextetLineSubrepresentation S).toRepresentation := by
  rw [Subrepresentation.irreducible_iff_isAtom]
  refine ⟨?_, fun W hW => ?_⟩
  · intro h
    exact sextetTetradLine_ne_bot S (congrArg Subrepresentation.toSubmodule h)
  · apply Subrepresentation.toSubmodule_injective
    apply Submodule.finrank_eq_zero.mp
    have hlt : W.toSubmodule < sextetTetradLine S := by
      refine lt_of_le_of_ne hW.le ?_
      intro he
      exact hW.ne (Subrepresentation.toSubmodule_injective he)
    have hdim : Module.finrank (ZMod 2) W.toSubmodule <
        Module.finrank (ZMod 2) (sextetTetradLine S) := Submodule.finrank_strictMono hlt
    have hline := sextetTetradLine_finrank S
    omega

end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
