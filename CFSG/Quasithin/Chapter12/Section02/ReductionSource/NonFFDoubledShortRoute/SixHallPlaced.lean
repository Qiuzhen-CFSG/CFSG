module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixHallOuter
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixHallPlacement

/-!
# Full placement of the original alternating-six Hall residual

The original proper odd normalizer supplies the complete Theorem B marking
of its selected ordinary component. The proved outer-section inspection
forces inner action. Original residual uniqueness then places the literal
residual and whole rank-eight orbit in that component, with odd centralizer.
No outer, model, inner-action or uniqueness guard is added.
Source: Aschbacher--Smith 4.4.10--11, printed p.621, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The selected original Hall component contains the full orbit and residual
with odd centralizer. Every model and outer-action premise is derived. -/
theorem sourceOrbit_six_oddNormalizer_placement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G)) :
    K.Normal ∧ D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) ∧
      8 ≤ primeRank 2 (K ⧸ center K) := by
  let := hK.2
  have hqt := ((oddNormalizer_properQTK h.simpleQTKE A hne).2.1).subgroup K
  have hkg := ((oddNormalizer_properQTK h.simpleQTKE A hne).2.2).subgroup K
  have hm := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple hqt hkg
  exact D.six_oddNormalizer_placement h hd hmodel A hne hAC ho hout K hK houtK
    (SixHallOuter.six_no_outer_section hm)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
