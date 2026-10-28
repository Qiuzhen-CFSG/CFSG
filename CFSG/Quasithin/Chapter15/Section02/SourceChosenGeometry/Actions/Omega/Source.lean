module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Omega.Numerics
/-!
# Complete natural Omega chosen-plane conclusions

The preceding source inputs construct the common image and its plane.
The fixed-line calculation supplies the exact index-two alternative,
while the ambient centralizer theorem identifies Mc and the intersections.
The shared plane theorem then gives Baumann containment and the omega-center
identity. The original natural action witness is retained throughout.

Source: Aschbacher--Smith 15.2.13--14, printed pp.1111--1112,
refs/quasithin.pdf. Earlier source premises remain with qt-e-152-plane-geometry.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Omega
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 Cyclic
variable {G : Type*} [Group G] [Finite G]

/-- Original 15.2.14(1),(5) on the same natural Omega source inputs. -/
theorem Preceding.source_centralizers {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H) :
    Mc = centralizer (centralInvolutions T : Set G) ∧
      M ⊓ Mc = M ⊓ centralizer (centralInvolutions T : Set G) ∧
      M ⊓ centralizer (centralInvolutions T : Set G) =
        (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) :=
  h.centralizers_of_omega d.full d.omega (d.residual_eq ▸ d.residual_centralizes)

/-- The complete natural Omega plane geometry of 15.2.14, preserving its
action witness and the literal Sylow-plane centralizer. -/
theorem Preceding.source_plane_geometry {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    letI := h.prepared.elementary
    ChosenPlaneGeometry h H ⁅V,B⁆ ∧
      centralInvolutions T ≤ ⁅V,B⁆ ∧
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized) ∧
      Nat.card (centralInvolutions T) = 2 ∧
      (planeCentralizer T ⁅V,B⁆).relIndex (T : Subgroup G) = 2 ∧
      ⁅V,B⁆ = omegaOneCenterAmbient (planeCentralizer T ⁅V,B⁆) := by
  let := h.prepared.elementary
  have hp := (d.planes B hB).2.2
  have hg := source_chosen_geometry_of_plane h d.outside d.two_overgroups d.quotient
    d.full hp.1 hp.2.1 hp.2.2.1
  obtain ⟨hz,hc,hi⟩ := d.plane_numerics hB
  exact ⟨hg,hz,d.omega,hc,hi,hg.omegaCenter (Or.inr ⟨hc,hi⟩)⟩

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Omega
