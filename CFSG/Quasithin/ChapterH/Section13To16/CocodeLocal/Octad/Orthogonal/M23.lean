module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Octad.Geometry
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Orthogonal.M23

/-!
# H.15.2(2): the actual alternating-seven quadratic restriction

For an octad through the fixed point, its native M23 stabilizer acts on the
six-dimensional supported cocode space as the even binary permutation module
on the seven remaining coordinates. Its kernel is precisely the restriction
of the published `m23OctadKernel`, and is the stabilizer's intrinsic two-core.
The quotient is genuinely A7 and acts faithfully by isometries of the existing
quadratic form. The action is irreducible. The seven source-orbit vectors are
kept distinct from the full M24 nonsingular set.

The equality of this geometric space with the kernel fixed space belongs to
the parent octad assembly. This module imports only the chapter Geometry
boundary, so it can be used by that assembly without a cycle.

Source: Aschbacher--Smith, H.15.2(2), printed pp.398--399.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal

/-- The literal restriction of the cocode action to the M23 octad stabilizer. -/
def m23OctadPairRepresentation (O : Octad) :
    Representation (ZMod 2) (CocodeOctad.m23OctadStabilizer O) (octadPairSpace O) :=
  CocodeOctad.m23PairRepresentation O

lemma m23OctadPairRepresentation_apply (O : Octad)
    (g : CocodeOctad.m23OctadStabilizer O) (v : octadPairSpace O) :
    (m23OctadPairRepresentation O g v).val = m23CocodeRepresentation g.val v.val := rfl

/-- Pulling the published kernel back to S equals the relative octad core pullback. -/
lemma m23Octad_relativeKernel_eq_comap (O : Octad) :
    (m23OctadKernel O).comap (CocodeOctad.m23OctadStabilizer O).subtype =
      (pCore 2 (octadStabilizer O)).comap (CocodeOctad.m23ToOctad O) := by
  ext g
  change pointEmbedding g.val ∈ (pCore 2 (octadStabilizer O)).map (octadStabilizer O).subtype ↔
    CocodeOctad.m23ToOctad O g ∈ pCore 2 (octadStabilizer O)
  constructor
  · rintro ⟨a, ha, he⟩
    have he' : a = CocodeOctad.m23ToOctad O g := Subtype.ext he
    exact he' ▸ ha
  · intro hg
    exact ⟨CocodeOctad.m23ToOctad O g, hg, rfl⟩

/-- The lower relative kernel is exactly the chapter kernel restricted to S. -/
lemma m23Octad_restrictedKernel_eq (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    CocodeOctad.m23OctadKernelRestricted O hO =
      (m23OctadKernel O).comap (CocodeOctad.m23OctadStabilizer O).subtype :=
  (m23Octad_relativeKernel_eq_comap O).symm

/-- Normality is relative to the octad stabilizer, as required by the source. -/
instance m23Octad_relativeKernel_normal (O : Octad) :
    ((m23OctadKernel O).comap (CocodeOctad.m23OctadStabilizer O).subtype).Normal := by
  rw [m23Octad_relativeKernel_eq_comap]
  infer_instance

lemma m23Octad_restriction_kernel (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (CocodeOctad.sevenCoordinateAction O hO).ker =
      (m23OctadKernel O).comap (CocodeOctad.m23OctadStabilizer O).subtype :=
  (CocodeOctad.sevenCoordinateAction_ker O hO).trans (m23Octad_restrictedKernel_eq O hO)

lemma m23Octad_core_eq_relativeKernel (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    pCore 2 (CocodeOctad.m23OctadStabilizer O) =
      (m23OctadKernel O).comap (CocodeOctad.m23OctadStabilizer O).subtype :=
  (CocodeOctad.sevenCoordinateAction_core O hO).trans (m23Octad_restriction_kernel O hO)

lemma m23OctadPairRepresentation_ker (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (m23OctadPairRepresentation O).ker =
      (m23OctadKernel O).comap (CocodeOctad.m23OctadStabilizer O).subtype :=
  (CocodeOctad.m23PairRepresentation_ker O hO).trans (m23Octad_core_eq_relativeKernel O hO)

lemma m23Octad_sevenAction_range (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (CocodeOctad.sevenCoordinateAction O hO).range =
      alternatingGroup (CocodeOctad.octadSeven O) :=
  CocodeOctad.sevenCoordinateAction_range O hO

/-- The six-dimensional even seven-coordinate model, with its actual action. -/
def m23Octad_evenSevenEquiv (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    BinaryPermutation.core (CocodeOctad.octadSeven O) ≃ₗ[ZMod 2] octadPairSpace O :=
  CocodeOctad.sevenCoreEquiv O hO

lemma m23Octad_evenSevenEquiv_equivariant (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : CocodeOctad.m23OctadStabilizer O) (v : BinaryPermutation.core (CocodeOctad.octadSeven O)) :
    m23Octad_evenSevenEquiv O hO
        (BinaryPermutation.coreRepresentation _ (CocodeOctad.sevenCoordinateAction O hO g) v) =
      m23OctadPairRepresentation O g (m23Octad_evenSevenEquiv O hO v) :=
  CocodeOctad.sevenCoreEquiv_equivariant O hO g v

lemma m23OctadPairRepresentation_isIrreducible (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Representation.IsIrreducible (m23OctadPairRepresentation O) :=
  CocodeOctad.m23PairRepresentation_isIrreducible O hO

lemma m23Octad_restriction_quadratic_invariant (O : Octad)
    (g : CocodeOctad.m23OctadStabilizer O) (v : octadPairSpace O) :
    CocodeOctad.quadratic O (m23OctadPairRepresentation O g v) = CocodeOctad.quadratic O v :=
  CocodeOctad.m23_quadratic_invariant O g v

/-- The intrinsic quotient is the standard A7, via the actual coordinate action. -/
def m23Octad_quotient_A7 (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (CocodeOctad.m23OctadStabilizer O ⧸ pCore 2 (CocodeOctad.m23OctadStabilizer O)) ≃*
      alternatingGroup (Fin 7) :=
  CocodeOctad.m23QuotientA7Equiv O hO

lemma m23Octad_quotient_A7_mk (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : CocodeOctad.m23OctadStabilizer O) :
    (m23Octad_quotient_A7 O hO (QuotientGroup.mk g)).val =
      (CocodeOctad.sevenIndexEquiv O hO).permCongr (CocodeOctad.sevenCoordinateAction O hO g) :=
  CocodeOctad.m23QuotientA7Equiv_mk O hO g

/-- The faithful quadratic action of the intrinsic quotient. -/
def m23OctadQuotientIsometryAction (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (CocodeOctad.m23OctadStabilizer O ⧸ pCore 2 (CocodeOctad.m23OctadStabilizer O)) →*
      Atlas.Order20160A8.isometrySubgroup (CocodeOctad.quadratic O) :=
  CocodeOctad.m23QuotientIsometryAction O hO

lemma m23OctadQuotientIsometryAction_injective (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Function.Injective (m23OctadQuotientIsometryAction O hO) :=
  CocodeOctad.m23QuotientIsometryAction_injective O hO

lemma m23OctadQuotientIsometryAction_mk (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : CocodeOctad.m23OctadStabilizer O) (v : octadPairSpace O) :
    (m23OctadQuotientIsometryAction O hO (QuotientGroup.mk g)).val v =
      m23OctadPairRepresentation O g v :=
  CocodeOctad.m23QuotientIsometryAction_mk O hO g v

/-- The source quotient by the published kernel, restricted to its local stabilizer. -/
def m23Octad_publishedKernel_quotient_A7 (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (CocodeOctad.m23OctadStabilizer O ⧸
      (m23OctadKernel O).comap (CocodeOctad.m23OctadStabilizer O).subtype) ≃*
        alternatingGroup (Fin 7) :=
  (QuotientGroup.quotientMulEquivOfEq (m23Octad_core_eq_relativeKernel O hO).symm).trans
    (m23Octad_quotient_A7 O hO)

lemma m23Octad_publishedKernel_quotient_A7_mk (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : CocodeOctad.m23OctadStabilizer O) :
    (m23Octad_publishedKernel_quotient_A7 O hO (QuotientGroup.mk g)).val =
      (CocodeOctad.sevenIndexEquiv O hO).permCongr (CocodeOctad.sevenCoordinateAction O hO g) := rfl

/-- The source quotient's faithful action on the literal quadratic space. -/
def m23Octad_publishedKernel_isometryAction (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (CocodeOctad.m23OctadStabilizer O ⧸
      (m23OctadKernel O).comap (CocodeOctad.m23OctadStabilizer O).subtype) →*
        Atlas.Order20160A8.isometrySubgroup (CocodeOctad.quadratic O) :=
  (m23OctadQuotientIsometryAction O hO).comp
    (QuotientGroup.quotientMulEquivOfEq (m23Octad_core_eq_relativeKernel O hO).symm).toMonoidHom

lemma m23Octad_publishedKernel_isometryAction_injective (O : Octad)
    (hO : (0 : Fin 24) ∈ O.val) :
    Function.Injective (m23Octad_publishedKernel_isometryAction O hO) :=
  (m23OctadQuotientIsometryAction_injective O hO).comp
    (QuotientGroup.quotientMulEquivOfEq (m23Octad_core_eq_relativeKernel O hO).symm).injective

lemma m23Octad_publishedKernel_isometryAction_mk (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : CocodeOctad.m23OctadStabilizer O) (v : octadPairSpace O) :
    (m23Octad_publishedKernel_isometryAction O hO (QuotientGroup.mk g)).val v =
      m23OctadPairRepresentation O g v :=
  m23OctadQuotientIsometryAction_mk O hO g v

lemma m23Octad_sourceOrbit_card (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Nat.card {v : octadPairSpace O | v.val ∈ m23WeightTwoOrbit} = 7 :=
  CocodeOctad.card_m23_sourceOrbit O hO

end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
