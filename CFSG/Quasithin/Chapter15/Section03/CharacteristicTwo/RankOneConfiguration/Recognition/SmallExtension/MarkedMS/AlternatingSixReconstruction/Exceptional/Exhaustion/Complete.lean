module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Source

/-!
# Original exceptional exhaustion assembly

The original Borel and distance-four plane exclusions feed the literal
whole-core dichotomy. Consequently every source of critical distance at
most four exhausts its intrinsic core. Any remaining exceptional obstruction
has the original plane image and critical distance at least six.

Source: Meierfrankenfeld--Stellmacher (1993), (5.11)--(5.12), pp.923--927;
Aschbacher--Smith C.1.32(4), pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
open LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
local notation "Rg" => edge L R

include h e hz

/-- The actual exceptional source exhausts the whole intrinsic core at
every critical distance at most four. -/
theorem coreExhaustion_of_sourceDistance_le_four
    (hb : sourceDistance h ≤ 4) : CoreExhaustion L R := by
  rcases coreExhaustion_or_cubic_plane h e hz with hx | ⟨hk,_hs,hgt,_hcovers,u,hR⟩
  · exact hx
  · have he := sourceDistance_even h
    rw [Nat.even_iff] at he
    have hb4 : sourceDistance h = 4 := by omega
    exact (plane_four_impossible h e hz hk hb4 u hR).elim

/-- The remaining actual cubic obstruction is a plane at distance at least
six, with the original full moving covers and the retained cubic kernel. -/
theorem coreExhaustion_or_cubic_plane_six_le :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      6 ≤ sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S, (Rg).map (CubicAction.projection h e hz hk) =
        D.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_plane h e hz with hx | ⟨hk,hs,hgt,hcovers,u,hR⟩
  · exact Or.inl hx
  · have hne : sourceDistance h ≠ 4 := fun hb => plane_four_impossible h e hz hk hb u hR
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he
    exact Or.inr ⟨hk,hs,by omega,hcovers,u,hR⟩

open ChapterC in
/-- All five original whole-block clauses at critical distance at most four. -/
theorem core_facts_of_sourceDistance_le_four
    (hb : sourceDistance h ≤ 4) :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L :=
  core_facts_of_exhaustion h e hz (coreExhaustion_of_sourceDistance_le_four h e hz hb)

/-- The unchanged original C.1.32 consumer at critical distance at most four. -/
theorem rankTwo_of_sourceDistance_le_four
    (hb : sourceDistance h ≤ 4) : RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz (coreExhaustion_of_sourceDistance_le_four h e hz hb)

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
