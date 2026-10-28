module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionTransitive
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionSLThree
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAlternatingEight
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.Assembly

/-!
# Applications and remaining assembly for 12.2.16

The alternating-seven four-space and marked nonsplit SL₃ extension supply
the TI argument of the original 12.2.13 assembly. The remaining universal
argument splits at C_V(L)=1. Its three independent inputs are the
fixed-free row proofs, the reducible reduction to the literal A₈ fusion
configuration, and that configuration's central-omega containment.

These remaining inputs are unfinished source obligations. The assembly
theorem below does not assert unconditional 12.2.16 or 12.2.13.
Source: Aschbacher--Smith 12.2.16, printed pp.799--800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 Section04.SmallFusion
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

/-- Source row (e) supplies the TI input on the original choice. -/
theorem alternatingSeven_alternatives_of_local_recognition
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K)
    [((centralizer (V : Set G)).subgroupOf L).Normal]
    (e : (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) D.space = 4)
    (localStep : NoEscape L V → IsTISubgroup V → ∃ d, SplitLinearConfiguration L V d)
    (recognize : ∀ d, SplitLinearConfiguration L V d →
      NoEscape L V → RecognizedGroup G d) : Alternatives12213 T L V :=
  alternatives_of_source_steps
    (fun hn => globalTI_of_alternating_seven_four h D structural hn e hd)
    localStep recognize

/-- The actual SL₃ central extension also discharges the original TI input. -/
theorem slThree_alternatives_of_local_recognition
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (E : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (localStep : NoEscape L V → IsTISubgroup V → ∃ d, SplitLinearConfiguration L V d)
    (recognize : ∀ d, SplitLinearConfiguration L V d →
      NoEscape L V → RecognizedGroup G d) : Alternatives12213 T L V :=
  alternatives_of_source_steps
    (fun hn => globalTI_of_slThree_extension h D structural hn E hne)
    localStep recognize

/-- Assembly boundary for the three independent remaining source proofs.
The module classification can remain an explicit earlier input to each producer. -/
theorem globalTI_of_row_reductions
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (fixedFree : V ⊓ centralizer (L : Set G) = ⊥ → IsTISubgroup V)
    (reducible : V ⊓ centralizer (L : Set G) ≠ ⊥ →
      IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V))
    (eight : ∀ C : AlternatingEightFusion T L V, omegaCenterIn C.pointSylow ≤ V) :
    IsTISubgroup V := by
  classical
  by_cases hc : V ⊓ centralizer (L : Set G) = ⊥
  · exact fixedFree hc
  · rcases reducible hc with ht | hC
    · exact ht
    · let C : AlternatingEightFusion T L V := Classical.choice hC
      exact (C.false_of_omega_le h D structural hnone (eight C)).elim

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
