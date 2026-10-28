module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalTerminalRightCenter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.SuzukiContainment.ReducedPair

/-!
# The terminal central line survives the literal F.1.1 reduction

The original central line is a normal two-subgroup of the full right
parabolic. Its two-core lies in the reduced Sylow subgroup, so the same
line remains central in the reduced right parabolic. This is the endpoint
used by native reduced-amalgam comparisons; no comparison is assumed here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric ChapterF.Source
open SuzukiContainment
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H R : Subgroup G}

/-- F.1.1 reduction retains the actual central line and nontrivial right
center; it does not require a right quotient marking or a second Context. -/
theorem original_terminal_reduced_right_center
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ centralizer (V₁ : Set G)) (hR : R ≤ H)
    (h : HypothesisF11 ![L,R] (Global.sourceS L H)) :
    let P := parabolic ![L,R] (reducedSylow ![L,R] (Global.sourceS L H)) 1
    V₁ ≤ (center P).map P.subtype ∧ center P ≠ ⊥ := by
  dsimp only
  let P := parabolic ![L,R] (Global.sourceS L H) 1
  let Q := parabolic ![L,R] (reducedSylow ![L,R] (Global.sourceS L H)) 1
  have hz : V₁ ≤ (center P).map P.subtype :=
    (original_terminal_right_center d hH hHC hR).1
  have hPC : P ≤ centralizer (V₁ : Set G) := by
    intro y hy x hx
    obtain ⟨z,hz,rfl⟩ := hz hx
    exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)).symm
  have hVcore : V₁ ≤ P.pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      (T.isPGroup'.to_le
        (d.flag.one_le_two.trans (d.flag.two_le_V.trans d.chosen.le_sylow)))
      (hz.trans (map_subtype_le _))
      (hPC.trans (Subgroup.centralizer_le_normalizer _))
  have hVQ : V₁ ≤ Q :=
    (hVcore.trans (parabolic_core_le_reducedSylow h 1)).trans
      (le_sup_right.trans le_sup_left)
  have hQC : Q ≤ centralizer (V₁ : Set G) := (reduced_parabolic_le h 1).trans hPC
  have hzQ : V₁ ≤ (center Q).map Q.subtype := by
    intro x hx
    refine ⟨⟨x,hVQ hx⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext (hQC y.property x hx).symm
  refine ⟨hzQ,?_⟩
  intro he
  change center Q = ⊥ at he
  have hv : V₁ = ⊥ := bot_unique (by simpa only [he,Subgroup.map_bot] using hzQ)
  have hc := d.flag.one_card
  rw [hv] at hc
  norm_num at hc

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
