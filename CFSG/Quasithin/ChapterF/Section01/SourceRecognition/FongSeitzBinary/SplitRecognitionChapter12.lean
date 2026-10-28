module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SplitRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Exhaustive split comparison in the actual Chapter 12 preparation

The selected original factor is already linear. Exhaustive marked split
recognition therefore supplies its concrete amalgam comparison with no
rotation-order or row-selection premise. The generic preparation version
retains an arbitrary known-simple class; the Chapter 12 version retains
full KnownSimple and the original proper-K hypotheses.

The residual application discharges the concrete-comparison hypothesis of
rankOne_global_residual_preparation_of_concrete_comparisons. It still needs
original uniqueness and a genuine marked split quotient for every prepared
pair to which it is applied. The regular apartment/quotient input belongs
to qt-dgs85-apartment-exchange; exceptional and other source branches and
final premise discharge remain with the original assembly owners.

Source: DGS Theorem D, printed p.224; AS 5.2.6, F.1.12 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open Chapter6.Source.RankOneGeneric
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}

/-- The existing generic preparation supplies both the source hypothesis and
its linear factor. Only the actual marked split quotient remains an input. -/
theorem prepared_split_complete_comparison
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  SplitRecognition.marked_catalogue_of_linear_left Q mark (d.hypothesisF11 h hTH)
    split h.qtke.quasithin (by have := h.exponent; omega) h.linear

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The actual Chapter 12 marked split quotient supplies the full concrete
comparison, with every Weyl-order alternative discharged. -/
theorem rankOne_split_complete_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  exact prepared_split_complete_comparison d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH Q mark split

/-- Genuine marked split quotients discharge the comparison premise in the
original residual preparation. Original uniqueness remains explicit. -/
theorem rankOne_global_residual_preparation_of_split_quotients
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hquot : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R → ∃ Q : SourceQuotient ![L,R] (Global.sourceS L H),
        Nonempty (SplitData Q.tits)) :
    ∃ A B : Subgroup G, Global.Preparation T L H A B (residual H) ∧
      Group.IsPerfect (residual H) := by
  apply D.rankOne_global_residual_preparation_of_concrete_comparisons h hmany hn hpsl
    hH hpar hthree hN hunique
  intro A B R d hp
  obtain ⟨Q,⟨split⟩⟩ := hquot A B R d hp
  exact D.rankOne_split_complete_comparison h hmany hn hpsl d hH.1.1.2
    Q (originalMarkedIso Q) split

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
