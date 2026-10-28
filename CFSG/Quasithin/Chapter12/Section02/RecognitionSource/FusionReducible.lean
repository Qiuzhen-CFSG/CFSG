module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleRows
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleAdjustment

/-!
# The two remaining geometric inputs to the reducible fusion reduction

The alternating row producer reconstructs the literal augmentation core,
selects a complementary fusion pair and arranges its point Sylow. This
module performs the remaining Sylow adjustment, constructs the published
A₈ configuration and feeds the original global-TI assembly. The G₂ producer
supplies its independent seven-dimensional Weyl exclusion.

Both geometric row implications remain explicit source obligations. The
SL₃ marking, the irreducible-row exclusions and the A₈ adjustment have been
proved separately. Neither this conditional assembly nor its application
claims completion of the reducible reduction or of 12.2.16.

Source: Aschbacher–Smith, 12.2.16, pp.799–800; rows 12.2.2(3), p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The alternating producer supplies an unadjusted source pair. Its fixed
line and adjusted outside conjugator are constructed here. -/
theorem reducible_of_geometric_rows
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (rows : ModuleAlternatives1222 D)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (alternating : ∀ n : ℕ, 5 ≤ n → n ≤ 8 →
      (letI := D.actionCentralizer_normal
       ActionEquiv D.faithfulCentralAction (alternatingNatural n)) →
      IsTISubgroup V ∨ Nonempty (AlternatingEightFusionSeed T L V))
    (g2 : ActionEquiv D.centralQuotientAction
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype) →
      IsTISubgroup V) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V) := by
  apply reducible_of_alternating_and_g2 h D structural hnone rows hne _ g2
  intro n hlo hhi action
  rcases alternating n hlo hhi action with ht | hC
  · exact Or.inl ht
  · let C : AlternatingEightFusionSeed T L V := Classical.choice hC
    exact Or.inr (C.exists_adjusted h D structural hnone)

/-- Actual application to the original TI assembly. The two reducible
geometric rows, fixed-free row theorem and terminal A₈ geometry remain
independent inputs; all other row and adjustment premises are discharged. -/
theorem globalTI_of_geometric_row_reductions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (rows : ModuleAlternatives1222 D)
    (fixedFree : V ⊓ centralizer (L : Set G) = ⊥ → IsTISubgroup V)
    (alternating : V ⊓ centralizer (L : Set G) ≠ ⊥ →
      ∀ n : ℕ, 5 ≤ n → n ≤ 8 →
        (letI := D.actionCentralizer_normal
         ActionEquiv D.faithfulCentralAction (alternatingNatural n)) →
        IsTISubgroup V ∨ Nonempty (AlternatingEightFusionSeed T L V))
    (g2 : V ⊓ centralizer (L : Set G) ≠ ⊥ →
      ActionEquiv D.centralQuotientAction
        ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype) →
      IsTISubgroup V)
    (eight : ∀ C : AlternatingEightFusion T L V, omegaCenterIn C.pointSylow ≤ V) :
    IsTISubgroup V := by
  apply globalTI_of_row_reductions h D structural hnone fixedFree _ eight
  intro hc
  exact reducible_of_geometric_rows h D structural hnone rows hc (alternating hc) (g2 hc)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
