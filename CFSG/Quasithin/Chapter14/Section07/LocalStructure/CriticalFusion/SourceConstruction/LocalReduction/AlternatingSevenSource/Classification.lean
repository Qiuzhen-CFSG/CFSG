module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Quotients
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.SmallModules

/-!
# The small-module catalogue on the original local quotient

The source quotient construction and seven-letter marking satisfy the
already proved compatible A₇/S₇ catalogue. This invocation keeps the
four-plus-dual alternative until the source cubic geometry excludes it.
In particular it does not infer component irreducibility merely from
ambient irreducibility.

Source: Aschbacher–Smith 14.7.50 and B.4.2/B.4.5,
printed p.1064 and Appendix B, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.ComponentSieve.Seven
open PairsBranch.ModuleSelection
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Every original faithful simple quotient has the complete marked
four-, natural-six-, or four-plus-dual alternative. -/
theorem local_quotient_small_module_alternatives_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤)
    (hirr : IsIrreducible N.quotientRepresentation)
    (hq : quadraticRatio N.quotientRepresentation ≤ 2)
    (j : (I ⧸ pCore 2 I) →* Equiv.Perm (Fin 7)) (hj : Function.Injective j)
    (hCj : (C.map (QuotientGroup.mk' (pCore 2 I))).map j = alternatingGroup (Fin 7)) :
    SmallModuleAlternatives N.quotientRepresentation j
      (componentInclusion j hj (C.map (QuotientGroup.mk' (pCore 2 I))) hCj) := by
  obtain ⟨A,hA,hquad,hsmall⟩ := (quadraticRatio_le_two_iff N.quotientRepresentation).mp hq
  exact OriginalSource.source_small_quadratic j hj
    (C.map (QuotientGroup.mk' (pCore 2 I))) hCj _ N.quotientRepresentation
    (local_proper_quotient_faithful_at d h hab structural previous faithful earlier
      source47 I hI C hC a N hN) hirr A hA hquad hsmall

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
