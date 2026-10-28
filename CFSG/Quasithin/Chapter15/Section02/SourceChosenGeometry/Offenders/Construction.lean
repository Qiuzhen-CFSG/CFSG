module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Residual
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.ChiefActors
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.WreathGeneration

/-!
# The offender-plane consumer with uniform chief identities left explicit

This assembly constructs a member of the literal Sigma-minus-Sigma(T) family
and proves all the plane conclusions uniformly. Residual containment follows
from the maximum-actor displacement theorem. The actual wreath quotient gives
the normalizer identity and generation by T and any outside actor; this proves
H-normality and residual centralization without assuming marked generators.

The final consumer discharges equality of fixed centralizers on U_H using
ChiefActors. Uniform Delta quadraticity remains an unproved local obligation
of qt-e-152-offender-plane. Thus it is still a conditional consumer, not a proof
of 15.2.9--11 from the preceding source hypotheses alone.
The parent qt-e-152-plane-geometry discharges the preceding action alternatives
and wreath quotient supplied by qt-e-152-small-parabolic.

Source: Aschbacher--Smith 15.2.9--11, printed pp.1110--1111.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01
variable {G : Type*} [Group G] [Finite G]

/-- Uniform conditional assembly with the normalizer, generation, residual
containment, centrality and nonemptiness inputs discharged. The two uniform
identities remain with this offender-plane owner. -/
theorem ChosenSmallSource.offender_plane_of_uniform_identities
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hquad : ∀ A ∈ delta H, ⁅⁅conjugateSpan H V,A⁆,A⁆ = ⊥)
    (hfix : ∀ A ∈ delta H,
      conjugateSpan H V ⊓ centralizer (A : Set G) =
        conjugateSpan H V ⊓ centralizer (A ⊓ twoCoreIn H : Subgroup G)) :
    letI := h.prepared.elementary
    (sigmaOutside (T : Subgroup G) H).Nonempty ∧
      ∀ B ∈ sigmaOutside (T : Subgroup G) H,
        actor M V B h.prepared.normalized ∈ ChapterD.Q
          (imageRepresentation M V h.prepared.normalized) ∧
        ⁅V,B⁆ ≤ V ∧ Nat.card (⁅V,B⁆ : Subgroup G) = 4 ∧
        (T : Subgroup G) ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
        H ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
        ⁅V,B⁆ ≤ (center (ChosenGeometry.residual H)).map
          (ChosenGeometry.residual H).subtype := by
  let := h.prepared.elementary
  refine ⟨h.sigmaOutside_nonempty_of_uniform_fixed hH hfix,?_⟩
  intro B hB
  obtain ⟨hactor,hq,hZV,hcard,hTZ⟩ := h.sigmaOutside_plane_of_wreath ha hH he hquad hfix hB
  have hHZ := h.sigmaOutside_normalized_of_wreath ha hH he hquad hfix hB
  have hKZ := h.sigmaOutside_residual_centralizes_of_wreath ha hH he hquad hfix hB
  refine ⟨h.quadratic_actor_mem_Q _ hactor hq,hZV,hcard,hTZ,hHZ,?_⟩
  obtain ⟨A,hA,_,rfl⟩ := exists_offender_of_mem_sigmaOutside hB
  have hVU : V ≤ conjugateSpan H V := by
    rw [conjugateSpan_eq]
    exact le_conjugateSpanBy _ _
  have hZK : ⁅V,A ⊓ twoCoreIn H⁆ ≤ ChosenGeometry.residual H :=
    (commutator_mono hVU inf_le_left).trans (h.maximal_span_commutator_le_residual hH hA.1)
  intro z hz
  refine ⟨⟨z,hZK hz⟩,mem_center_iff.mpr ?_,rfl⟩
  intro k
  exact Subtype.ext ((hKZ k.property z hz).symm)

/-- The plane construction with the uniform fixed-centralizer identity and
outside-offender existence proved. Uniform quadraticity remains a local
obligation of this owner; the preceding action and wreath inputs belong to
qt-e-152-small-parabolic and are discharged by qt-e-152-plane-geometry. -/
theorem ChosenSmallSource.offender_plane_of_uniform_quadratic
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hquad : ∀ A ∈ delta H, ⁅⁅conjugateSpan H V,A⁆,A⁆ = ⊥) :
    letI := h.prepared.elementary
    (sigmaOutside (T : Subgroup G) H).Nonempty ∧
      ∀ B ∈ sigmaOutside (T : Subgroup G) H,
        actor M V B h.prepared.normalized ∈ ChapterD.Q
          (imageRepresentation M V h.prepared.normalized) ∧
        ⁅V,B⁆ ≤ V ∧ Nat.card (⁅V,B⁆ : Subgroup G) = 4 ∧
        (T : Subgroup G) ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
        H ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
        ⁅V,B⁆ ≤ (center (ChosenGeometry.residual H)).map
          (ChosenGeometry.residual H).subtype :=
  h.offender_plane_of_uniform_identities ha hH he hquad (fun _ hA => h.delta_fixed hH hA)

end CFSG.Quasithin.Chapter15.Section02
