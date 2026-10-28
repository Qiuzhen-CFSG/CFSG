module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.Recognition
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.OddCoreGeometry

/-!
# Complete cyclic chosen-plane conclusions

Restricted-model recognition is discharged from the preceding source inputs.
The common-image and odd-core arguments now give all cyclic clauses of
15.2.13. The original ambient centralizer lemmas give the literal intersections
in 15.2.14(1),(5); the numerical alternatives give the shared plane geometry,
Baumann containment and the omega-center identity.

The preceding 15.2.1--12 premises remain with qt-e-152-plane-geometry. The
natural Omega branch and its assembly remain with qt-e-152-action-plane.
No model-recognition or local calculation premise remains in these exports.

Source: Aschbacher--Smith 15.2.13--14, printed pp.1111--1112,
refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Original 15.2.14(1),(5) in the non-Omega branch, without a recognition premise. -/
theorem Preceding.source_centralizers {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H) :
    Mc = centralizer (centralInvolutions T : Set G) ∧
      M ⊓ Mc = M ⊓ centralizer (centralInvolutions T : Set G) ∧
      M ⊓ centralizer (centralInvolutions T : Set G) =
        (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) :=
  centralizers_of_restricted_models h d.full d.restricted_models

/-- The complete common-image and fixed/moved-plane clauses of 15.2.13(2)
in the non-Omega branch. Model recognition is discharged internally. -/
theorem Preceding.source_common_plane {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H) :
    letI := h.prepared.elementary
    ∃ B₀ : Subgroup (internalActionImage M V h.prepared.normalized),
      B₀ ≤ actor M V (T : Subgroup G) h.prepared.normalized ∧ Nat.card B₀ = 2 ∧
      pPrimeCore 2 (internalActionImage M V h.prepared.normalized) =
        ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),B₀⁆ ∧
      (∀ A : Subgroup (internalActionImage M V h.prepared.normalized),
        A ≤ actor M V (T : Subgroup G) h.prepared.normalized → Nat.card A = 2 → A = B₀) ∧
      ∀ B ∈ sigmaOutside (T : Subgroup G) H,
        actor M V B h.prepared.normalized = B₀ ∧
        V ⊓ centralizer (B : Set G) = ⁅V,B⁆ ∧
        ⁅V,B⁆ = ambientSpace V (subspaceCommutator
          (imageRepresentation M V h.prepared.normalized) ⊤ B₀) ∧
        ambientSpace V (subspaceCommutator
          (imageRepresentation M V h.prepared.normalized) ⊤ B₀) =
          ambientSpace V (fixedSpace (imageRepresentation M V h.prepared.normalized) B₀) ∧
        centralInvolutions T ≤ ⁅V,B⁆ := by
  let := h.prepared.elementary
  obtain ⟨B₀,hP,hc,hu,hplanes⟩ := d.common_plane
  refine ⟨B₀,hP,hc,?_,hu,hplanes⟩
  obtain ⟨B,hB⟩ := d.nonempty
  rw [←(hplanes B hB).1]
  exact d.oddCore_commutator d.restricted_models hB

/-- The actual common plane satisfies both alternatives of 15.2.14(2),
Baumann containment, and the literal omega-center equality. The returned
shared geometry supplies the interface used by the final plane assembly. -/
theorem Preceding.source_plane_geometry {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    ChosenPlaneGeometry h H ⁅V,B⁆ ∧
      centralInvolutions T ≤ ⁅V,B⁆ ∧
      ((planeCentralizer T ⁅V,B⁆ = (T : Subgroup G) ∧ centralInvolutions T = ⁅V,B⁆) ∨
        (Nonempty (internalActionImage M V h.prepared.normalized ≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∧
          Nat.card (centralInvolutions T) = 2 ∧
          (planeCentralizer T ⁅V,B⁆).relIndex (T : Subgroup G) = 2)) ∧
      ⁅V,B⁆ = omegaOneCenterAmbient (planeCentralizer T ⁅V,B⁆) := by
  let := h.prepared.elementary
  have hp := (d.planes B hB).2.2
  have hg := source_chosen_geometry_of_plane h d.outside d.two_overgroups d.quotient
    d.full hp.1 hp.2.1 hp.2.2.1
  obtain ⟨hz,hcases⟩ := d.plane_alternatives d.restricted_models hB
  refine ⟨hg,hz,hcases,hg.omegaCenter ?_⟩
  exact hcases.elim Or.inl (fun hh => Or.inr hh.2)
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
