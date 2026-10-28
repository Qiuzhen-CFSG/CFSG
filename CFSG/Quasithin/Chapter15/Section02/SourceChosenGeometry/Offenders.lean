module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Planes
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.GenerationReduction
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Construction
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.ChiefImages
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.ChiefActors.Coordinates
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.ChiefActors.Alignment
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.ChiefActors.InternalLift
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Source
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.WreathGeneration.Marked
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Completion

/-!
# The original uniform offender-plane construction

The `offender_plane` consumer constructs an outside Sigma member and proves
all plane conclusions uniformly: nontrivial quadratic action, order four,
T- and H-normality, and containment in the embedded center of O²(H).
Quadratic proves whole-span quadraticity and both sharp action-rank identities
for every original Delta member. It uses the full displacement centralizer,
the actual four-dimensional fixed/moved plane, and relative generation;
it does not identify the original actor with an arbitrary replacement.
Source supplies the actual ResidualInput consumed by the geometry owner.
Only the preceding small-action, wreath and two-overgroup inputs remain
explicit there. ChiefActors.FourImages excludes order four by replacing the
original offender using V itself, preserving maximum elementary order and
the literal quotient-image inclusion. Completion supplies the resulting
order-two images, chief transvections and original marked generator identities.
ChiefActors.Coordinates supplies actual natural chief actions, the literal
offender-image transport, complementary marked four-groups, and their common
base J(H)O₂(H).
ChiefActors.Alignment identifies the same individual factors on both chief
modules, proves their literal plane commutator identities, selects a common
interchanging element in T, and proves that either marked residual normally
generates O²(H).

The earlier conditional consumers below retain their public interfaces.
The final sigmaOutside_geometry consumer discharges all their local premises
using the original marked family spans and residuals.

Source: Aschbacher--Smith 15.2.9--11, printed pp.1110--1111, combined
manuscript of 1 March 2004.
-/

public section

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor

namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01
variable {G : Type*} [Group G] [Finite G]

/-- Conditional assembly of 15.2.11, retained for callers supplying their own
uniform chief-action identities and marked generators. -/
theorem ChosenSmallSource.sigmaOutside_geometry_of_generation
    {T : Sylow 2 G} {M Mc V H B : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hNV : H ⊓ normalizer (V : Set G) = (T : Subgroup G))
    (hquad : ∀ A ∈ delta H, ⁅⁅conjugateSpan H V,A⁆,A⁆ = ⊥)
    (hfix : ∀ A ∈ delta H,
      conjugateSpan H V ⊓ centralizer (A : Set G) =
        conjugateSpan H V ⊓ centralizer (A ⊓ twoCoreIn H : Subgroup G))
    (hres : ∀ A ∈ delta H, ⁅conjugateSpan H V,A⁆ ≤ ChosenGeometry.residual H)
    (hgen : ∀ A ∈ delta H, ¬ A ≤ (T : Subgroup G) → ∃ X L : Subgroup G,
      X ≤ centralizer (V : Set G) ∧ H = (X ⊔ A) ⊔ (T : Subgroup G) ∧
        L ≤ X ⊔ A ∧ ChosenGeometry.residual H = conjugateSpanBy L H)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    letI := h.prepared.elementary
    actor M V B h.prepared.normalized ∈ ChapterD.Q (imageRepresentation M V h.prepared.normalized) ∧
      ⁅V,B⁆ ≤ V ∧ Nat.card (⁅V,B⁆ : Subgroup G) = 4 ∧
      (T : Subgroup G) ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
      H ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
      ⁅V,B⁆ ≤ (center (ChosenGeometry.residual H)).map (ChosenGeometry.residual H).subtype := by
  let := h.prepared.elementary
  obtain ⟨hactor,hq,hZV,hcard,hTZ⟩ := h.sigmaOutside_plane ha hH hNV hquad hfix hB
  refine ⟨h.quadratic_actor_mem_Q _ hactor hq,hZV,hcard,hTZ,?_⟩
  obtain ⟨A,hA,hAT,rfl⟩ := exists_offender_of_mem_sigmaOutside hB
  obtain ⟨X,L,hXV,hHgen,hLX,hspan⟩ := hgen A hA hAT
  have hBV : A ⊓ twoCoreIn H ≤ normalizer (V : Set G) := by
    have hh := map_mono (f := H.subtype)
      (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2))
    change (pCore 2 H).map H.subtype ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rw [map_subgroupOf_eq_of_le hH.1.1.2] at hh
    exact (inf_le_right.trans hh).trans (h.maximal.1.2.trans h.prepared.normalized)
  obtain ⟨hHN,hKC⟩ := plane_normality_of_generation hBV (hquad A hA) hXV hTZ hHgen hLX hspan
  refine ⟨hHN,?_⟩
  have hVU : V ≤ conjugateSpan H V := by
    rw [conjugateSpan_eq]
    exact le_conjugateSpanBy _ _
  have hZK : ⁅V,A ⊓ twoCoreIn H⁆ ≤ ChosenGeometry.residual H :=
    (commutator_mono hVU inf_le_left).trans (hres A hA)
  intro z hz
  refine ⟨⟨z,hZK hz⟩,mem_center_iff.mpr ?_,rfl⟩
  intro k
  exact Subtype.ext ((hKC k.property z hz).symm)

end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01
variable {G : Type*} [Group G] [Finite G]

/-- The original marked-generator proof of the uniform source plane theorem.
All local offender, chief-action and generation premises are discharged.
The preceding action, uniqueness and wreath inputs are supplied by
qt-e-152-small-parabolic and discharged by qt-e-152-plane-geometry. -/
theorem ChosenSmallSource.sigmaOutside_geometry
    {T : Sylow 2 G} {M Mc V H B : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    letI := h.prepared.elementary
    actor M V B h.prepared.normalized ∈ ChapterD.Q
        (imageRepresentation M V h.prepared.normalized) ∧
      ⁅V,B⁆ ≤ V ∧ Nat.card (⁅V,B⁆ : Subgroup G) = 4 ∧
      (T : Subgroup G) ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
      H ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
      ⁅V,B⁆ ≤ (center (ChosenGeometry.residual H)).map (ChosenGeometry.residual H).subtype := by
  exact h.sigmaOutside_geometry_of_generation ha hH (h.wreath_intersections hH he).2
    (fun _ hA => h.delta_quadratic hH he hA)
    (fun _ hA => h.delta_fixed hH hA)
    (fun _ hA => h.maximal_span_commutator_le_residual hH hA.1)
    (fun A hA hAT => h.delta_generator_witnesses ha hunique hH he hA hAT) hB

end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01
variable {G : Type*} [Group G] [Finite G]

/-- The marked-generator route with an explicit order-two image clause,
retained for compatibility. `delta_image_card_two` now supplies that clause
from the preceding source hypotheses. -/
theorem ChosenSmallSource.sigmaOutside_geometry_of_order_two
    {T : Sylow 2 G} {M Mc V H B : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (htwo : ∀ A∈delta H, Nat.card (offenderImage H A)=2)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    letI := h.prepared.elementary
    actor M V B h.prepared.normalized ∈ ChapterD.Q (imageRepresentation M V h.prepared.normalized) ∧
      ⁅V,B⁆ ≤ V ∧ Nat.card (⁅V,B⁆ : Subgroup G) = 4 ∧
      (T : Subgroup G) ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
      H ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
      ⁅V,B⁆ ≤ (center (ChosenGeometry.residual H)).map (ChosenGeometry.residual H).subtype := by
  exact h.sigmaOutside_geometry_of_generation ha hH (h.wreath_intersections hH he).2
    (fun _ hA => h.delta_quadratic hH he hA)
    (fun _ hA => h.delta_fixed hH hA)
    (fun _ hA => h.maximal_span_commutator_le_residual hH hA.1)
    (fun A hA hAT => h.delta_two_generator_witnesses hunique hH he hA (htwo A hA) hAT) hB
end CFSG.Quasithin.Chapter15.Section02
