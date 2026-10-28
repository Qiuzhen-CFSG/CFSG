module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Octad.Geometry
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Orthogonal.Orbit
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Orthogonal.Action
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Orthogonal.OmegaAction
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Octad.Orthogonal.M23

/-!
# The orthogonal octad cocode action

The supported octad space carries the transported half-weight quadratic form.
An actual isometry identifies it with the split six-dimensional space, its
polar form is nondegenerate, and its nonsingular set is exactly the intersection
with the native weight-two orbit. This proves the geometric M24 avoidance bound.
The native stabilizer acts irreducibly, with intrinsic two-core kernel. Its
quotient is identified with the actual Siegel-generated Ω⁺₆(2), and the split
isometry intertwines its natural action with the faithful supported-space action.
The imported M23 endpoint gives the incident octad's A7 quotient and its
equivariant even seven-coordinate model, with the published relative kernel.

These are the geometric action and avoidance assertions. The parent octad
assembly identifies this supported space with the kernel fixed space and
assembles the other clauses of H.15.2.

Source: Aschbacher--Smith, H.15.2(2--3), printed pp.398--399.
-/

@[expose] public section

open scoped BigOperators Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
noncomputable section

/-- A genuine isometry from the standard split six-dimensional form to the
supported octad quadratic space. -/
def octadQuadraticIsometry (O : Octad) :
    (ClassicalOrthogonal.formD 3 (ZMod 2)).IsometryEquiv
      (MathieuCode.CocodeOctad.quadratic O) :=
  MathieuCode.CocodeOctad.formEquiv O

@[simp] lemma octadQuadraticIsometry_apply (O : Octad)
    (x : ClassicalOrthogonal.VectorD 3 (ZMod 2)) :
    MathieuCode.CocodeOctad.quadratic O (octadQuadraticIsometry O x) =
      ClassicalOrthogonal.formD 3 (ZMod 2) x :=
  (octadQuadraticIsometry O).map_app x

lemma quadratic_polar_nondegenerate (O : Octad) :
    (MathieuCode.CocodeOctad.quadratic O).polarBilin.Nondegenerate :=
  MathieuCode.CocodeOctad.quadratic_polar_nondegenerate O

lemma m24_octad_avoiding_finrank_le (O : Octad)
    (I : Submodule (ZMod 2) Cocode)
    (hI : I ≤ octadPairSpace O)
    (ha : Disjoint (I : Set Cocode) weightTwoOrbit) :
    Module.finrank (ZMod 2) I ≤ 3 :=
  MathieuCode.CocodeOctad.m24_avoiding_finrank_le O I hI ha

lemma quadratic_nonsingular_mem_weightTwo (O : Octad)
    {v : octadPairSpace O} (hv : MathieuCode.CocodeOctad.quadratic O v = 1) :
    v.val ∈ weightTwoOrbit :=
  MathieuCode.CocodeOctad.quadratic_nonsingular_mem_weightTwo O hv

/-- The converse orbit inclusion required by the source orthogonal description. -/
lemma octad_quadratic_one_iff_weightTwo (O : Octad) (v : octadPairSpace O) :
    CocodeOctad.quadratic O v = 1 ↔ v.val ∈ weightTwoOrbit :=
  CocodeOctad.quadratic_one_iff_weightTwo O v

lemma octad_quadratic_invariant (O : Octad) (g : octadStabilizer O)
    (v : octadPairSpace O) :
    CocodeOctad.quadratic O (CocodeOctad.pairRepresentation O g v) =
      CocodeOctad.quadratic O v :=
  CocodeOctad.quadratic_invariant O g v

lemma octad_quadratic_action_equivariant (O : Octad) (g : octadStabilizer O)
    (x : ClassicalOrthogonal.VectorD 3 (ZMod 2)) :
    octadQuadraticIsometry O ((CocodeOctad.splitAction O g).val x) =
      CocodeOctad.pairRepresentation O g (octadQuadraticIsometry O x) :=
  CocodeOctad.formEquiv_equivariant O g x

lemma octadPairSpace_isIrreducible (O : Octad) :
    Representation.IsIrreducible (CocodeOctad.pairRepresentation O) :=
  CocodeOctad.pairRepresentation_isIrreducible O

/-- The faithful quotient action retains the literal supported-space carrier. -/
def octadQuotientIsometryAction (O : Octad) :
    (octadStabilizer O ⧸ pCore 2 (octadStabilizer O)) →*
      Atlas.Order20160A8.isometrySubgroup (CocodeOctad.quadratic O) :=
  CocodeOctad.quotientIsometryAction O

lemma octadQuotientIsometryAction_injective (O : Octad) :
    Function.Injective (octadQuotientIsometryAction O) :=
  CocodeOctad.quotientIsometryAction_injective O

lemma octadQuotientIsometryAction_mk (O : Octad) (g : octadStabilizer O)
    (v : octadPairSpace O) :
    (octadQuotientIsometryAction O (QuotientGroup.mk g)).val v =
      CocodeOctad.pairRepresentation O g v :=
  CocodeOctad.quotientIsometryAction_mk O g v

lemma octad_splitAction_range (O : Octad) :
    (CocodeOctad.splitAction O).range = (alternatingGroup (Fin 8)).map
      Atlas.Order20160A8.DeletedEight.orthogonalHom :=
  CocodeOctad.splitAction_range O

/-- The split action image is the actual Siegel-generated Omega subgroup. -/
lemma octad_splitAction_range_eq_elementary (O : Octad) :
    (CocodeOctad.splitAction O).range =
      ClassicalOrthogonal.elementarySubgroup (ClassicalOrthogonal.formD 3 (ZMod 2)) :=
  CocodeOctad.splitAction_range_eq_elementary O

/-- The native intrinsic quotient, identified with Ω⁺₆(2) through its action. -/
def octad_quotient_Omega (O : Octad) :
    (octadStabilizer O ⧸ pCore 2 (octadStabilizer O)) ≃*
      ClassicalOrthogonal.elementarySubgroup (ClassicalOrthogonal.formD 3 (ZMod 2)) :=
  CocodeOctad.quotientOmegaEquiv O

lemma octad_quotient_Omega_mk (O : Octad) (g : octadStabilizer O) :
    (octad_quotient_Omega O (QuotientGroup.mk g)).val = CocodeOctad.splitAction O g :=
  CocodeOctad.quotientOmegaEquiv_mk O g

/-- The genuine isometry is equivariant for the quotient's natural Omega action. -/
lemma octad_quotient_Omega_equivariant (O : Octad)
    (q : octadStabilizer O ⧸ pCore 2 (octadStabilizer O))
    (x : ClassicalOrthogonal.VectorD 3 (ZMod 2)) :
    octadQuadraticIsometry O ((octad_quotient_Omega O q).val.val x) =
      (octadQuotientIsometryAction O q).val (octadQuadraticIsometry O x) := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [octad_quotient_Omega_mk]
    exact (octad_quadratic_action_equivariant O g x).trans
      (octadQuotientIsometryAction_mk O g (octadQuadraticIsometry O x)).symm

lemma octadQuotientIsometryAction_range (O : Octad) :
    (octadQuotientIsometryAction O).range =
      (ClassicalOrthogonal.elementarySubgroup (ClassicalOrthogonal.formD 3 (ZMod 2))).map
        (Atlas.Order20160A8.isometryGroupTransport (octadQuadraticIsometry O)).toMonoidHom :=
  CocodeOctad.quotientIsometryAction_range O

/-- Pulling the published ambient kernel back to its stabilizer gives its intrinsic core. -/
lemma octad_core_eq_relativeKernel (O : Octad) :
    pCore 2 (octadStabilizer O) = (octadKernel O).comap (octadStabilizer O).subtype :=
  (Subgroup.comap_map_eq_self_of_injective (octadStabilizer O).subtype_injective _).symm

/-- The published kernel is normal in the local stabilizer. -/
instance octad_relativeKernel_normal (O : Octad) :
    ((octadKernel O).comap (octadStabilizer O).subtype).Normal := by
  rw [← octad_core_eq_relativeKernel]
  infer_instance

lemma octadPairRepresentation_ker (O : Octad) :
    (CocodeOctad.pairRepresentation O).ker =
      (octadKernel O).comap (octadStabilizer O).subtype :=
  (CocodeOctad.pairRepresentation_ker O).trans (octad_core_eq_relativeKernel O)

/-- The source quotient uses the published kernel restricted to its local stabilizer. -/
def octad_publishedKernel_quotient_Omega (O : Octad) :
    (octadStabilizer O ⧸ (octadKernel O).comap (octadStabilizer O).subtype) ≃*
      ClassicalOrthogonal.elementarySubgroup (ClassicalOrthogonal.formD 3 (ZMod 2)) :=
  (QuotientGroup.quotientMulEquivOfEq (octad_core_eq_relativeKernel O).symm).trans
    (octad_quotient_Omega O)

lemma octad_publishedKernel_quotient_Omega_mk (O : Octad) (g : octadStabilizer O) :
    (octad_publishedKernel_quotient_Omega O (QuotientGroup.mk g)).val =
      CocodeOctad.splitAction O g := rfl

/-- The source quotient equivalence induces the literal cocode action. -/
lemma octad_publishedKernel_Omega_equivariant (O : Octad) (g : octadStabilizer O)
    (x : ClassicalOrthogonal.VectorD 3 (ZMod 2)) :
    octadQuadraticIsometry O
        ((octad_publishedKernel_quotient_Omega O (QuotientGroup.mk g)).val.val x) =
      CocodeOctad.pairRepresentation O g (octadQuadraticIsometry O x) :=
  CocodeOctad.formEquiv_equivariant O g x

end
end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
