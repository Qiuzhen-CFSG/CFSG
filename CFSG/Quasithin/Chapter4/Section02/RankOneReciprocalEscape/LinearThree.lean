module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.LinearThreeModels

/-!
# The binary linear-three reciprocal escape

The other conjugate in the reversed component retains the PSL₃(2)
two-core quotient in the literal star image. Source 4.2.10 transfers the
three-rank bound to the star component. The terminal model exclusion
therefore discharges the contrary generalized-Fitting containment on the
original selected witnesses, with no added model or geometry premise.

Source: Aschbacher--Smith 4.2.5--10, printed pp.609--610.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The terminal binary linear-three contradiction discharges the escape on the original witnesses. -/
theorem linearThree_escape_case_of_not_unique {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (e : ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* Matrix.PSL3Two.PSL)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (ho : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (Section04.oddActorResidual L A) (normalizer (L : Set G))) :
    EscapeCase L V A := by
  obtain ⟨J,H,W,hw,hr⟩ := reciprocal_placement_case_of_not_unique h D hM A hAN hcomm ho hAV hnot
  refine ⟨J,H,W,hw,?_⟩
  intro hf
  obtain ⟨hd,_,hz,K,hK,hq,hfK,hout,_,hn,_,hplace⟩ := hr hf
  let := hq
  let := hn
  have hHnot : ¬ H ≤ normalizer (L : Set G) := by
    intro hle
    have he := subgroupOf_eq_top.mpr hle
    have hi := hd.2.2.2.1
    rw [he,index_top] at hi
    norm_num at hi
  obtain ⟨t,htH,htN⟩ := SetLike.not_le_iff_exists.mp hHnot
  have hE := (hplace ⟨t,htH⟩ htN).1
  have hrank := (hplace ⟨t,htH⟩ htN).2.2.2.2.2
  let B := K.map (normalizer (L : Set G)).subtype
  let E := L.map (MulAut.conj t).toMonoidHom
  let c : E ≃* L := (L.equivMapOfInjective (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective).symm
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective (f := c.symm.toMonoidHom) c.symm.surjective
  let q := QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  let a : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.PSL :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans e
  have hEB : E ≤ B := hE.trans inf_le_left
  have hEH : E ≤ H := hE.trans inf_le_right
  have hEN : E ≤ normalizer (H.pCoreIn 2 : Set G) :=
    hEH.trans (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  apply LinearThreeModels.no_source_linearThree_normalizing_radical (reciprocal_source_input hd K hK hfK hout)
    (le_inf (le_inf hEH (hEB.trans (map_subtype_le _))) hEB) hEN (q.trans a)
  apply hrank 3 (by decide) (by decide)
  obtain ⟨b⟩ := (hplace ⟨t,htH⟩ htN).2.2.2.2.1
  have hd3 : 3 ∣ Nat.card (Matrix.PSL3Two.PSL) := by
    rw [Matrix.PSL3Two.card_PSL]
    decide
  rw [←Nat.card_congr (b.trans a).toEquiv] at hd3
  exact hd3.trans (card_quotient_dvd_card _)

end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
