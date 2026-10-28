module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.Applicability
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.SixCover

/-!
# Lifting the marked natural quotient to the actual moved module

For the actual offender overgroup LA, an offender moving O3(G) cannot lie
in L: components centralize the three-core. Consequently the complete
B.5.1 conclusion is in its irreducible-section branch. Apply the central
cover calculation to that literal section. A marked natural six/seven
quotient then gives the marked natural moved module, or the six-point
augmentation core with its central line retained.

`model_of_earlier_source` assembles the lifted-component comparison with
the moved-space extension. The comparison excludes the five-point action
by three-rank, and A8 and derived G2(2) by the three-part of the actual
lifted center. It constructs `ReducedSymmetricModel`, then
`model_of_reduced` lifts its action with the same actor and component
markings. The result retains the central line in the augmentation-core
case and makes no splitting assumption.

There are exactly two universal earlier-source parameters: the complete
`ProjectiveLine.QuasisimpleClassificationInput` (B.5.1, producer
`qt-b05-quasisimple`) and `ModelComparison.BinaryG2Exclusion.EarlierMultiplierInput`
(all six rows of I.1.3, producer `qt-i-01`, including `qt-i01-lie-a2`).
The supplied `NoncentralContext` already retains the prepared cover and
the A.3.18/B.5.2/B.5.5 consequences; its construction remains with
`CoverCentralizer.SourceConstruction` and the earlier-source owners,
including `qt-b05-quotient-components`. The extension itself uses proved
I.1.5, alternating I.1.6(1) cohomology and self-duality results, with no
additional earlier-source parameter. Final assembly of B.5.7 and discharge
of its earlier inputs remain with `qt-b05-high-three-offender-module`.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.7, printed
p.106, and I.1.5–6(1), printed p.408.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction
universe u v
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V)

private theorem component_centralizes_threeCore {L : Subgroup G} (hL : IsComponent G L) :
    L ≤ centralizer (pCore 3 G : Set G) := by
  rcases hL.normal_dichotomy (pCore 3 G) with hle | hc
  · let := hL.2
    let := IsQuasisimple.simple (G := L)
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    let := (pCore_isPGroup (p := 3) (G := G)).isNilpotent
    let : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective hle)
    exact (Group.IsPerfect.not_isSolvable L inferInstance).elim
  · exact commutator_eq_bot_iff_le_centralizer.mp hc

/-- Apply the extension theorem to the original offender, component and B.5.1 section.
The construction of `r` remains the lifted-cover/model-comparison obligation. -/
theorem model_of_reduced (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (d : NoncentralContext K G L) {A : Subgroup G}
    (hm : ¬ A ≤ centralizer (pCore 3 G : Set G))
    (r : ReducedSymmetricModel ρ L A) : Nonempty (SymmetricMovedModel ρ L A) := by
  let : FiniteDimensional (ZMod 2) V := hyp.finite_module
  let : L.Normal := d.normal
  have hout : ¬ A ≤ L := fun h => hm (h.trans (component_centralizes_threeCore hL))
  have hi := (local_irreducible ρ hout r.classification).1
  exact ⟨⟨r.classification.sectionData,
    moved_action_of_reduced r.classification.sectionData hi r.action⟩⟩

/-- The marked natural six/seven or six-point augmentation-core action on
the actual moved space of the original moving offender. The reduced model
and its central extension are constructed; only the complete universal
earlier B.5.1 and I.1.3 implications remain explicit. -/
theorem model_of_earlier_source
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (multipliers : ModelComparison.BinaryG2Exclusion.EarlierMultiplierInput K)
    (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (hr : 1 < primeRank 3 L)
    (d : NoncentralContext K G L) {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hm : ¬ A ≤ centralizer (pCore 3 G : Set G)) :
    Nonempty (SymmetricMovedModel ρ L A) := by
  obtain ⟨r⟩ := ModelComparison.reduced_of_earlier_source
    earlier multipliers ρ hyp hL hr d hA hm
  exact model_of_reduced ρ hyp hL d hm r

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction
