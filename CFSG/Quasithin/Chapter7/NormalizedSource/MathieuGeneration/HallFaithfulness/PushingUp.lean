module

public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Source
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Ranks
public import Theory.GroupTheory.CComponent.OddRankNormal
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.FiniteModels.Basic

/-!
# The Mathieu residual forces the original pushing-up escape

Every actual Mathieu central quotient has cubic rank at least two. A
nonnormal C-component in an SQTK group has centerless core quotient; the
commuting-conjugate rank bound therefore rules out nonnormality here.

In the contained generalized-Fitting branch of the original maximal
pushing-up configuration, the proved reciprocal argument identifies the
intersection residual with L and makes it an index-two C-component of H.
Transport through the literal subgroup inclusion preserves its Mathieu
central quotient, so normality contradicts that index. Thus the actual
preimage of F*(H/O₂(H)) escapes N_G(L), with all original witnesses retained.
This is the Mathieu instance of 4.2.5, not the final uniqueness theorem.

Source: Aschbacher--Smith, 4.2.5--8 and 4.2.12--13, printed pp.609--612;
A.3.8(3), printed pp.45--46.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

/-- Every actual Mathieu central quotient in the chosen-module catalogue has cubic rank at least two. -/
theorem mathieu_centralQuotient_threeRank {Q : Type*} [Group Q] [Finite Q]
    (hm : HasMathieuCentralQuotient Q) : 2 ≤ primeRank 3 (Q ⧸ center Q) := by
  open Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne.FiniteModels in
    rcases hm with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · rw [primeRank_congr 3 e]; exact m12_rank_ge_two
    · rw [primeRank_congr 3 e]; exact m22_rank_ge_two
    · rw [primeRank_congr 3 e]; exact m23_rank_ge_two
    · rw [primeRank_congr 3 e]; exact m24_rank_ge_two

/-- A C-component with Mathieu central core quotient is normal in its SQTK ambient group. -/
theorem normal_of_mathieu_central_core_quotient
    {G : Type*} [Group G] [Finite G] (hG : IsSQTK KnownSimple.IsKnownSimple G)
    {B : Subgroup G} (hB : B.IsCComponent) [IsQuasisimple (B ⧸ pCore 2 B)]
    (hm : HasMathieuCentralQuotient (B ⧸ pCore 2 B)) : B.Normal := by
  by_contra hn
  have hz := Chapter4.Section02.RankOneReciprocalEscape.coreQuotient_center_eq_bot_of_nonnormal
    hG hB hn
  let e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* (B ⧸ pCore 2 B) :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  have hr := mathieu_centralQuotient_threeRank hm
  rw [primeRank_congr 3 e] at hr
  exact hn (hB.normal_of_coprime_core_center_primeRank (by decide : Odd 3)
    (by rw [hz]; simp) hr (hG.stronglyQuasithin 3 (by decide) (by decide)))

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Failure of fixed-residual uniqueness forces the genuine generalized-Fitting escape in the selected maximal two-local. -/
theorem sourceOrbit_mathieu_pushingUp_escape
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (ho : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    EscapeCase L V A := by
  have hM := h.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hjoin : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  obtain ⟨J,H,W,hw,hr⟩ := reciprocal_case_of_not_unique h D hjoin A hAN hcomm ho hAV hnot
  refine ⟨J,H,W,hw,?_⟩
  intro hf
  obtain ⟨hB,hcomp,hnorm,hi,hrest⟩ := hr hf
  have hBH : (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype ≤ H :=
    (map_subtype_le _).trans inf_le_right
  have hLH : L ≤ H := hB ▸ hBH
  let e : (L.subgroupOf H) ≃* L := subgroupOfEquivOfLe hLH
  let q : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let := h.quasisimple
  let : IsQuasisimple ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv q.symm
  let z := (centerQuotientCongr q).trans (D.orbitCentralQuotientEquiv h)
  have hm' : HasMathieuCentralQuotient ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) := by
    rcases hm with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · exact Or.inl ⟨z.trans f⟩
    · exact Or.inr (Or.inl ⟨z.trans f⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨z.trans f⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨z.trans f⟩))
  let : (L.subgroupOf H).Normal := normal_of_mathieu_central_core_quotient
    hw.2.2.2.2.2.2.1.sqtk hcomp hm'
  rw [normalizer_eq_top] at hnorm
  rw [←hnorm,index_top] at hi
  norm_num at hi
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

