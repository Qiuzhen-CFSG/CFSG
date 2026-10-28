module

public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.ComponentLifting.Source
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.LowerSources
public import CFSG.KnownSimple.CarrierCatalogue
/-!
# B.5.2 component lifting and generalized Fitting images

The literal prepared cover from B.5.2(1–2) lifts every component by taking
the solvable residual of its preimage. Its Fitting preimage equals its own
Fitting subgroup, contains the kernel, and its generalized Fitting subgroup
maps onto that of the quotient. The quotient statement uses the compatible
kernel quotient equivalence attached to this same prepared cover.

The elementary argument and the A.3.6 interface live below these consumer
contracts. This final adapter constructs the actual `ComponentCover` and
existential `CoverInput` already consumed by the B.5 induction. It includes
the full `KnownSimple.IsKnownSimple` specialization and imposes no
nontriviality assumption on the target group.

This is a conditional source family: the sole earlier classification input
is universal A.3.6 (`qt-a03-sqtk-structure`). The source assembly owner
`qt-b05-quotient-components` must discharge it. No B.4, B.5.5, module,
multiplier, or center–Frattini premise is added.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.2,
pp.103–104, using A.3.6, pp.43–45.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- B.5.2(3) on this exact prepared cover and projection. -/
theorem PreparedCover.component_lifts_of_a36 (c : PreparedCover K G)
    (hA36 : A36Input K) : ∀ L, IsComponent G L →
      ∃ M, IsComponent c.Cover M ∧ M.map c.projection = L := by
  let := c.fitting_nilpotent
  let := c.kernel_nilpotent
  exact ComponentLifting.component_lifts hA36 c.sqtk c.projection c.surjective c.kernel_odd

omit [Finite G] in
/-- The nilpotent Fitting preimage is the Fitting subgroup of the cover. -/
theorem PreparedCover.fitting_comap (c : PreparedCover K G) :
    (fittingSubgroup G).comap c.projection = fittingSubgroup c.Cover := by
  let := c.fitting_nilpotent
  exact fitting_comap_eq_of_nilpotent c.projection c.surjective

omit [Finite G] in
/-- The literal projection kernel lies in the cover Fitting subgroup. -/
theorem PreparedCover.kernel_le_fitting (c : PreparedCover K G) :
    c.projection.ker ≤ fittingSubgroup c.Cover := by
  rw [← c.fitting_comap]
  intro x hx
  change c.projection x ∈ fittingSubgroup G
  rw [MonoidHom.mem_ker.mp hx]
  exact one_mem _

/-- B.5.2(4) for the original projection. -/
theorem PreparedCover.generalizedFitting_image_of_a36 (c : PreparedCover K G)
    (hA36 : A36Input K) :
    (generalizedFitting c.Cover).map c.projection = generalizedFitting G := by
  let := c.fitting_nilpotent
  exact generalizedFitting_map_eq_of_component_lifts c.projection c.surjective
    (c.component_lifts_of_a36 hA36)

/-- B.5.2(4) inside the literal kernel quotient, using its compatible equivalence. -/
theorem PreparedCover.generalizedFitting_quotient_of_a36 (c : PreparedCover K G)
    (hA36 : A36Input K) :
    (generalizedFitting c.Cover).map (QuotientGroup.mk' c.projection.ker) =
      (generalizedFitting G).comap c.quotientEquiv.toMonoidHom := by
  apply map_injective (f := c.quotientEquiv.toMonoidHom) c.quotientEquiv.injective
  rw [map_comap_eq_self_of_surjective (f := c.quotientEquiv.toMonoidHom)
    c.quotientEquiv.surjective, map_map]
  exact c.generalizedFitting_image_of_a36 hA36

namespace CoverCentralizer.SourceConstruction

/-- Supply the existing four-clause source contract on the given prepared cover. -/
def componentCoverOfA36 (c : PreparedCover K G) (hA36 : A36Input K) :
    ComponentCover K G where
  prepared := c
  component_lifts := c.component_lifts_of_a36 hA36
  fitting_image := c.generalizedFitting_image_of_a36 hA36

/-- Combine the proved cover construction with component lifting. The presentation
is existentially selected, including when the quotient group is trivial. -/
theorem exists_componentCover_of_a36 (hA36 : A36Input K)
    (hq : Nonempty (SQTKQuotient K G)) : Nonempty (ComponentCover K G) := by
  obtain ⟨q⟩ := hq
  let f := q.equiv.toMonoidHom.comp (QuotientGroup.mk' q.kernel)
  have hf : Function.Surjective f :=
    q.equiv.surjective.comp (QuotientGroup.mk'_surjective q.kernel)
  obtain ⟨H, hH, hfin, α, hsqtk, hα, hfit, hker, hodd, _, _⟩ :=
    NilpotentCover.exists_sqtk_cover q.sqtk f hf
  let c : PreparedCover K G :=
    { Cover := H
      coverGroup := hH
      coverFinite := hfin
      projection := α
      surjective := hα
      sqtk := hsqtk
      fitting_nilpotent := hfit
      kernel_nilpotent := hker
      kernel_odd := hodd }
  exact ⟨componentCoverOfA36 c hA36⟩

/-- Discharge the existing existential B.5.2 input, conditionally only on A.3.6. -/
theorem coverInput_of_a36 (hA36 : A36Input K) : CoverInput K := by
  intro G _ _ hq
  exact exists_componentCover_of_a36 hA36 hq

/-- The full known-simple class required by the quasithin campaign. The earlier
A.3.6 premise remains with `qt-a03-sqtk-structure` and the source assembly owner. -/
theorem knownSimple_coverInput_of_a36
    (hA36 : A36Input.{u} KnownSimple.IsKnownSimple) :
    CoverInput.{u} KnownSimple.IsKnownSimple := coverInput_of_a36 hA36
end CoverCentralizer.SourceConstruction
end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank
