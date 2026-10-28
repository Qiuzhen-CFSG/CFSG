module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Octad.Dynamics
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Octad.Orthogonal
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Octad.Involutions
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.SourceInvolutions

/-!
# The octad and heptad clauses of H.15.2

Identify the supported pair space with the intrinsic kernel's fixed space,
then apply its orthogonal model and orbit bounds. The native class theorem
discharges the representative hypotheses in the involution ranks and pointwise
centralizers. The imported dynamics gives every transvection with the parity
axis and its stabilizer-equivariant identification with the kernel.

This completes H.15.2(2--6) for M24 and M23, with the octad incident with the
fixed point in the latter case. Offender uniqueness, H.15.2(1), belongs to the
separate offender argument. Source: Aschbacher--Smith, printed pp.397--399.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal

/-- H.14.4(3), the source Sylow-central M24 class. -/
theorem m24_twoCentral_fixedCodim (z : M24) (hz : IsSylowCentralInvolution z) :
    fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4 :=
  CocodeOctad.Involutions.sylowCentral_fixedCodim z hz

/-- H.14.4(3), the other M24 involution class. -/
theorem m24_noncentral_fixedCodim (t : M24) (ht : orderOf t = 2)
    (hn : ¬ IsSylowCentralInvolution t) :
    fixedCodim cocodeRepresentation (Subgroup.zpowers t) = 5 :=
  CocodeOctad.Involutions.noncentral_fixedCodim t ht hn

theorem m24_fixedPointFree_fixedCodim (t : M24) (ht : orderOf t = 2)
    (hf : ∀ i : Fin 24, t • i ≠ i) :
    fixedCodim cocodeRepresentation (Subgroup.zpowers t) = 5 :=
  CocodeOctad.Involutions.fixedPointFree_fixedCodim t ht hf

/-- All M23 involutions satisfy the rank-four assertion, with no class premise. -/
theorem m23_all_involutions_fixedCodim (z : M23) (hz : orderOf z = 2) :
    fixedCodim m23CocodeRepresentation (Subgroup.zpowers z) = 4 :=
  CocodeOctad.Involutions.m23_involution_fixedCodim z hz

/-- H.15.2(5), pointwise centrality in the full native M24. -/
theorem m24_twoCentral_pointwiseCentralizer (z : M24) (hz : IsSylowCentralInvolution z) :
    subspaceKernel cocodeRepresentation
      (fixedSpace cocodeRepresentation (Subgroup.zpowers z)) ⊤ = Subgroup.zpowers z :=
  CocodeOctad.Involutions.sylowCentral_pointwiseCentralizer z hz

theorem m23_all_involutions_pointwiseCentralizer (z : M23) (hz : orderOf z = 2) :
    subspaceKernel m23CocodeRepresentation
      (fixedSpace m23CocodeRepresentation (Subgroup.zpowers z)) ⊤ = Subgroup.zpowers z :=
  CocodeOctad.Involutions.m23_involution_pointwiseCentralizer z hz

/-- The split orthogonal model now has the literal source fixed-space carrier. -/
def octadFixedSpaceEquiv (O : Octad) :
    ClassicalOrthogonal.VectorD 3 (ZMod 2) ≃ₗ[ZMod 2]
      fixedSpace cocodeRepresentation (octadKernel O) :=
  (octadQuadraticIsometry O).toLinearEquiv.trans
    (LinearEquiv.ofEq _ _ (octadPairSpace_eq_fixedSpace O))

theorem octadFixedSpaceEquiv_equivariant (O : Octad) (g : octadStabilizer O)
    (x : ClassicalOrthogonal.VectorD 3 (ZMod 2)) :
    (octadFixedSpaceEquiv O
      ((octad_publishedKernel_quotient_Omega O (QuotientGroup.mk g)).val.val x)).val =
        cocodeRepresentation g.val (octadFixedSpaceEquiv O x).val := by
  exact congrArg Subtype.val (octad_publishedKernel_Omega_equivariant O g x)

/-- The even seven-coordinate module identifies the actual M23 fixed space. -/
def heptadFixedSpaceEquiv (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    BinaryPermutation.core (CocodeOctad.octadSeven O) ≃ₗ[ZMod 2]
      fixedSpace m23CocodeRepresentation (m23OctadKernel O) :=
  (m23Octad_evenSevenEquiv O hO).trans
    (LinearEquiv.ofEq _ _ (m23_octad_fixedSpace_eq_pairSpace O hO).symm)

theorem heptadFixedSpaceEquiv_equivariant (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : CocodeOctad.m23OctadStabilizer O)
    (x : BinaryPermutation.core (CocodeOctad.octadSeven O)) :
    (heptadFixedSpaceEquiv O hO
      (BinaryPermutation.coreRepresentation _ (CocodeOctad.sevenCoordinateAction O hO g) x)).val =
        m23CocodeRepresentation g.val (heptadFixedSpaceEquiv O hO x).val := by
  exact congrArg Subtype.val (m23Octad_evenSevenEquiv_equivariant O hO g x)

/-- H.15.2(2), rank of the M24 fixed space. -/
theorem octad_fixedSpace_finrank (O : Octad) :
    Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (octadKernel O)) = 6 := by
  rw [← octadPairSpace_eq_fixedSpace]
  exact finrank_octadPairSpace O

theorem heptad_fixedSpace_finrank (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Module.finrank (ZMod 2) (fixedSpace m23CocodeRepresentation (m23OctadKernel O)) = 6 := by
  rw [m23_octad_fixedSpace_eq_pairSpace O hO]
  exact finrank_octadPairSpace O

/-- H.15.2(3) for the actual M24 kernel fixed space. -/
theorem octad_fixedSpace_avoiding_finrank_le (O : Octad) (I : Submodule (ZMod 2) Cocode)
    (hI : I ≤ fixedSpace cocodeRepresentation (octadKernel O))
    (ha : Disjoint (I : Set Cocode) weightTwoOrbit) : Module.finrank (ZMod 2) I ≤ 3 := by
  rw [← octadPairSpace_eq_fixedSpace] at hI
  exact m24_octad_avoiding_finrank_le O I hI ha

theorem heptad_fixedSpace_avoiding_finrank_le (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (I : Submodule (ZMod 2) Cocode)
    (hI : I ≤ fixedSpace m23CocodeRepresentation (m23OctadKernel O))
    (ha : Disjoint (I : Set Cocode) m23WeightTwoOrbit) : Module.finrank (ZMod 2) I ≤ 4 := by
  rw [m23_octad_fixedSpace_eq_pairSpace O hO] at hI
  exact m23_octadPairSpace_avoiding_finrank_le O hO I hI ha

/-- H.15.2(4), with the fixed-space span from the source definition. -/
theorem octad_fixedSpaceSpan_hyperplane (O : Octad) :
    Module.finrank (ZMod 2) (Cocode ⧸ fixedSpaceSpan cocodeRepresentation (octadKernel O)) = 1 := by
  rw [octad_fixedSpaceSpan_eq_hyperplane]
  exact CocodeOctad.finrank_quotient_octadHyperplane O

theorem heptad_fixedSpaceSpan_hyperplane (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Module.finrank (ZMod 2)
      (Cocode ⧸ fixedSpaceSpan m23CocodeRepresentation (m23OctadKernel O)) = 1 := by
  rw [m23_octad_fixedSpaceSpan_eq_hyperplane O hO]
  exact CocodeOctad.finrank_quotient_octadHyperplane O

/-- H.15.2(5) in its source form, comparing the two literal fixed spaces. -/
theorem octad_noncyclic_fixedSpace (O : Octad) (A : Subgroup M24)
    (hA : A ≤ octadKernel O) (hnc : ¬ IsCyclic A) :
    fixedSpace cocodeRepresentation A = fixedSpace cocodeRepresentation (octadKernel O) := by
  rw [octad_noncyclic_fixedSpace_eq_pairSpace O A hA hnc, ← octadPairSpace_eq_fixedSpace]

theorem heptad_noncyclic_fixedSpace (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (A : Subgroup M23) (hA : A ≤ m23OctadKernel O) (hnc : ¬ IsCyclic A) :
    fixedSpace m23CocodeRepresentation A =
      fixedSpace m23CocodeRepresentation (m23OctadKernel O) := by
  rw [m23_octad_noncyclic_fixedSpace_eq_pairSpace O hO A hA hnc,
    m23_octad_fixedSpace_eq_pairSpace O hO]

end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
