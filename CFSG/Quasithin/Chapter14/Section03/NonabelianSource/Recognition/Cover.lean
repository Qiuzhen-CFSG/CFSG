module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.Preparation
public import CFSG.Quasithin.Chapter12.Section08.Terminal.Quotients
public import CFSG.Quasithin.ChapterG.Section09.Setup

/-!
# The SQTK cover of the original dotted point normalizer

The nontrivial elementary point makes its normalizer a proper two-local
subgroup of the ambient simple QTKE group. Hence it is SQTK. The defining
quotient map to H/C_H(U/Z(U)) supplies the exact finite cover required by
G.9; no descent of strong quasithinness through an arbitrary quotient is
asserted.

Source: Aschbacher--Smith, the setup for 14.3.11--15 and G.9.1.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The actual point normalizer is a proper two-local SQTK group. -/
theorem pointNormalizer_sqtk (hG : IsSimpleQTKE K G)
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 V] (hn : 1 ≤ n) : IsSQTK K F.H := by
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 hn
  have hne : F.Vi 1 ≠ ⊥ := by intro he; simp [he] at hc
  let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
  exact hG.twoLocal_sqtk ⟨F.Vi 1,hne,IsElementaryAbelian.isPGroup 2 _,rfl⟩

/-- The G.9 cover is H itself and the literal quotient by the U/Z(U)-action kernel. -/
def terminal_sqtkCover (hG : IsSimpleQTKE K G)
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 V] (hn : 1 ≤ n) :
    ChapterG.Section09.SQTKCover K F.TerminalHdot where
  Cover := F.H
  sqtk := pointNormalizer_sqtk hG F hn
  projection := QuotientGroup.mk' F.terminalHatAction.ker
  surjective := QuotientGroup.mk'_surjective _

/-- Immediate G.9 input for any flag constructed from the original rank-two hypothesis. -/
theorem rankTwo_terminal_cover {L M : Subgroup G} (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2) :
    Nonempty (ChapterG.Section09.SQTKCover K F.TerminalHdot) := by
  let := rankTwoSeed_elementary h
  exact ⟨terminal_sqtkCover h.simpleQTKE F (by decide)⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
