module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.ExceptionalKernel
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSClassification

/-!
# Exceptional kernel bounds in the original nonblock configuration

Apply the intrinsic cover bounds to the genuine MS-pair constructed from the
original configuration, chosen module, constrained hypothesis and supplied full
SL₃ quotient. The actual Q has index dividing sixteen in O₂(K), including at
field four. Fourth powers in that core lie in Q, centralize the whole U=Z(Q),
and have all commutators with Q in its actual Frattini subgroup.

This bounds the remaining descent obstruction in original 4.3.8--10 without a
whole-section model. Eliminating the exceptional kernel and recognizing the
entire source sections remain separate obligations.
Source: Aschbacher--Smith C.1.34, pp.136--137, I.1.3(6), p.407, and original
4.3.8--10, pp.616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.ExceptionalKernel
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))

include D hf n hn hF e

/-- The original commutator has index dividing sixteen in the intrinsic core,
including at field four and without whole-section assumptions. -/
theorem core_index_dvd : (Q c).relIndex ((K c).pCoreIn 2) ∣ 16 := by
  simpa only [ms_commutator_eq] using
    NonbinarySource.ExceptionalKernel.componentCore_index_dvd
      (msPair_of_quotient c D hf n (by omega) hF e) hn

/-- Fourth powers of the original intrinsic core lie in the actual Q. -/
theorem core_fourth_mem (x : G) (hx : x ∈ (K c).pCoreIn 2) : x ^ 4 ∈ Q c := by
  simpa only [ms_commutator_eq] using
    NonbinarySource.ExceptionalKernel.componentCore_fourth_mem
      (msPair_of_quotient c D hf n (by omega) hF e) hn x hx

/-- Fourth powers centralize the whole original U=Z(Q). -/
theorem fourth_centralizes_center (x : G) (hx : x ∈ (K c).pCoreIn 2) :
    x ^ 4 ∈ centralizer (U c : Set G) := by
  simpa only [ms_commutator_eq,
    show Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
      (Q c) = U c from rfl] using
    NonbinarySource.ExceptionalKernel.fourth_centralizes_center
      (msPair_of_quotient c D hf n (by omega) hF e) hn x hx

/-- Fourth powers act trivially on the entire original Frattini section;
the displacement is the literal ambient commutator. -/
theorem fourth_commutator_mem_frattini (x y : G) (hx : x ∈ (K c).pCoreIn 2)
    (hy : y ∈ Q c) : ⁅x ^ 4,y⁆ ∈ frattiniIn (Q c) := by
  let : Fact (IsPGroup 2 (Q c)) :=
    ⟨T.isPGroup'.to_le ((core_le_sylow c).trans inf_le_left)⟩
  have hm : ⁅(⟨x ^ 4,core_fourth_mem c D hf n hn hF e x hx⟩ : Q c),⟨y,hy⟩⁆ ∈
      frattini (Q c) := commutator_le_frattini_of_isPGroup (p := 2)
        (commutator_mem_commutator (mem_top _) (mem_top _))
  exact mem_map_of_mem (Q c).subtype hm

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.ExceptionalKernel
