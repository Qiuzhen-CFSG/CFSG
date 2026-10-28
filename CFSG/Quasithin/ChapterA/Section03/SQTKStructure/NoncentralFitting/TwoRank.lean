module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting
public import Theory.Quasithin.CoprimeRank
public import Theory.SpecificGroups.SL2.OddCoreAndRank
/-!
# Noncentral-Fitting C-components have two-rank one

A.3.6 identifies the quotient by the odd Fitting subgroup with SL₂(p).
Coprime quotient transport preserves two-rank, and the actual odd-field
SL₂ matrix group has two-rank one. Hence a C-component containing a
rank-two subgroup is quasisimple. This is the noncentral-Fitting exclusion
used for the original A₅ source in C.5.12, printed p.163.
-/
public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

theorem two_rank_eq_one_of_noncentral {κ : GroupClass} (hG : IsSQTK κ G)
    (hO : pCore 2 G = ⊥) (hL : L.IsCComponent)
    (hn : ¬ fittingSubgroup L ≤ center L) : primeRank 2 L = 1 := by
  obtain ⟨p,hp,hp3,⟨e⟩⟩ := primeSL2FittingQuotient_of_noncentral
    RankActions.primeSL2CoverRigidity hG hO hL hn
  let : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro he
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p)
      ((ZMod.natCast_eq_zero_iff 2 p).mp he)
  have heq := primeRank_eq_of_surjective_of_coprime 2 (QuotientGroup.mk' (fittingSubgroup L))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact (fitting_odd_card hL hO).coprime_two_left)
  rw [heq,primeRank_equiv 2 e]
  exact Matrix.SpecialLinearGroup.primeRank_two_eq_one htwo

theorem quasisimple_of_two_le_two_rank {κ : GroupClass} (hG : IsSQTK κ G)
    (hO : pCore 2 G = ⊥) (hL : L.IsCComponent) (hr : 2 ≤ primeRank 2 L) :
    IsQuasisimple L := by
  have hf : fittingSubgroup L ≤ center L := by
    by_contra hn
    rw [two_rank_eq_one_of_noncentral hG hO hL hn] at hr
    omega
  have hs : solvableRadical L = center L := by
    apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
    exact le_solvableRadical (center L) inferInstance
      (Group.isSolvable_of_comm (fun a b => Subtype.ext
        (mem_center_iff.mp a.property b).symm))
  let := hL.perfect
  let := hL.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hs).symm.isSimpleGroup⟩
end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
