module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialityPresentation.Application
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobal

/-!
# Triality presentation recognition in the original Chapter 12 chosen module

The chosen-module preparation supplies the genuine original F.1.1 source.
The explicit signed triality data on any marked split quotient then give the
exact ConcreteAmalgamComparison of the selected sourceParabolicAmalgam. The
same equivalence carries its original Sylow to the native positive subgroup
and both original odd Cartans into the whole native Borel.

Both orientations and every positive binary exponent are retained. The quotient
carrier can be geometric, with no universal-to-original-group descent premise.
Source: Aschbacher–Smith 12.2.2, printed p.795, and F.1.1–12; DGS Theorem D.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Triality.Standard.RootPresentationRecognition
open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
variable {G X F : Type*} [Group G] [Finite G] [Group X]
  [Field F]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)

include D in
/-- One full-model comparison retains all three representative formulas and
the actual original common Sylow, in either marked endpoint orientation. -/
theorem rankOne_triality_marked_presentation
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
    {m : ℕ} {hm : 0 < m} {σ : F ≃+* F}
    {armIndex : Fin 2} (roots : RootData Q split m hm σ armIndex)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) Q.standardAmalgam) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∧
    (MarkedLocal.sylowMap Q e
      (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH d).1).range.map
        roots.bruhat.quotientEquiv.toMonoidHom =
          _root_.Triality.Standard.Parabolics.unipotent (_root_.Triality.Standard.binaryParameters m hm) ∧
    ∀ i : Fin 2, Nat.Coprime 2 (Nat.card (MarkedLocal.localCartan Q e i)) ∧
      (MarkedLocal.localCartan Q e i).map
        (roots.bruhat.quotientEquiv.toMonoidHom.comp (MarkedLocal.factorMap Q e i)) ≤
          _root_.Triality.Standard.Parabolics.borel (_root_.Triality.Standard.binaryParameters m hm) := by
  have hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH d).1
  exact ⟨roots.concreteComparison e, source_sylow_image e hf roots, source_cartans e hf roots⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
