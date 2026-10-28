module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.PreciseMultiplierInputs.Cover
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank

/-!
# The B.5.7 rank reduction with the precise kernel input

The A.3.6 lifted cover feeds the existing centralizer reduction. In its
noncentral branch, the proved A₈ exclusion and the explicit three-free
perfect-kernel theorem for the actual binary derived G₂ group give the
marked six/seven module comparison. The existing moved-module and cubic
centralizer arguments yield the full adequate alternative. Its negation,
together with the original preparation chief section, forces rank one.

The binary-G₂ kernel premise is exactly the existing intrinsic cover
contract; its source producer is qt-i01-a2-unitary-covers. The full earlier
B.5.1 classification and all preparation conclusions are retained.
Source: Aschbacher–Smith, B.5.7, pp.105–106; I.1.1–3, p.407.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.PreciseMultiplierInputs
open HighThreeRank HighThreeRank.CoverCentralizer
open HighThreeRank.CoverCentralizer.SourceConstruction
open HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison
open ComponentReduction
universe u v

variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The proved A₈ exclusion and the exact binary-G₂ kernel input complete
the marked module comparison on the original moving offender. -/
theorem cubicCentralizers_of_threeFreePerfectKernels
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hg : ThreeFreePerfectKernels.{u} (commutator (Atlas.G2.Model (ZMod 2))))
    (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (hr : 1 < primeRank 3 L)
    (d : NoncentralContext K G L) : Nonempty (CubicCentralizers G L) := by
  obtain ⟨A, hA, hm, _, _⟩ := exists_moving_offender ρ hyp hL d
  obtain ⟨r⟩ := reduced_of_threeFreePerfectKernels h1
    alternatingEight_threeFreePerfectKernels hg ρ hyp hL hr d hA hm
  obtain ⟨m⟩ := ModuleCalculation.NaturalReduction.model_of_reduced ρ hyp hL d hm r
  exact ModuleCalculation.NaturalCentralizers.cubicCentralizers_of_moved_model
    ρ hyp hL d hA hm m

/-- The complete high-rank adequate alternative from the preparation input,
A.3.6 and the precise binary-G₂ perfect-kernel statement. -/
theorem adequate_of_high_three_rank
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K)
    (h5 : PreliminaryActions.Preparation.ComponentInput.{u,v} K)
    (hA : SemisimpleInput K) (h36 : Chapter1.Section02.A36Input K)
    (hg : ThreeFreePerfectKernels.{u} (commutator (Atlas.G2.Model (ZMod 2))))
    (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (hr : 1 < primeRank 3 L) : AdequateAlternative ρ := by
  obtain ⟨d⟩ := liftedCover_of_preparation ρ h52 h5 hA h36 hyp hL hr
  rcases reduction_of_liftedCover hyp hL hr d with ⟨hsq, hfit⟩ | hd
  · exact HighThreeRank.adequate_of_central_fitting ρ h1 hyp hL hsq hfit
  · obtain ⟨d⟩ := hd
    obtain ⟨c⟩ := cubicCentralizers_of_threeFreePerfectKernels ρ h1 hg hyp hL hr d
    exact HighThreeRank.adequate_of_module_calculation ρ d c

/-- The actual component has three-rank one in a counterexample. Positivity
comes from its original B.5.5 chief-section projection. -/
theorem component_rank_eq_one
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K)
    (h5 : PreliminaryActions.Preparation.ComponentInput.{u,v} K)
    (hA : SemisimpleInput K) (h36 : Chapter1.Section02.A36Input K)
    (hg : ThreeFreePerfectKernels.{u} (commutator (Atlas.G2.Model (ZMod 2))))
    (hyp : FFHypothesis K ρ) (hnot : ¬ AdequateAlternative ρ)
    {L : Subgroup G} (hL : IsComponent G L) : primeRank 3 L = 1 := by
  have hpos := component_rank_pos_of_preparation ρ (h5 G V ρ hyp) hL
  have hle : primeRank 3 L ≤ 1 := by
    by_contra hr
    exact hnot (adequate_of_high_three_rank ρ h1 h52 h5 hA h36 hg hyp hL (by omega))
  omega

end CFSG.Quasithin.ChapterB.SourceInduction.PreciseMultiplierInputs
