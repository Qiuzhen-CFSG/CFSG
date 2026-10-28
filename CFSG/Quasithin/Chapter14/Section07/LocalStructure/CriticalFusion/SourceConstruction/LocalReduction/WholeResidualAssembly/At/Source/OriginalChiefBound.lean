module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.ExtraspecialCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.At

/-!
# Original extraspecial Baumann control from the proved chief bound

The literal Heisenberg residual supplies six noncentral two-chief factors in
the original point residual. The natural-point Baumann theorem at this same
group and Sylow bounds every such series by three unless the actual Baumann
normalizer lies in the original component normalizer. This discharges the
14.7.10 duty here without a universal earlier-theorem premise.

The full original cores and chief series are retained. The earlier structural
and 12.2.13 sources are needed only at the original Sylow subgroup.
Source: Aschbacher--Smith 14.7.10 and 14.7.16(7), printed pp.1045,1048.
-/

public noncomputable section
open Subgroup NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.Local14710Source
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original six chief factors force the actual Baumann normalizer bound.
The earlier 14.7.10 alternative is proved at this group and Sylow. -/
theorem extraspecial_baumann_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨s,hs0,hs1,hcount⟩ :=
    GuardedSource.extraspecial_point_six_chief_factors h hab structural previous
      hex hcard hexp
  rcases ResidualNormalizer.LocalControl.OriginalSourceAt.chief_bound_or_baumann_normalizer_of_naturalPointMS
      h structural F with hsmall | hnormal
  · have hb := hsmall s hs0 hs1
    omega
  · exact hnormal

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.Local14710Source
