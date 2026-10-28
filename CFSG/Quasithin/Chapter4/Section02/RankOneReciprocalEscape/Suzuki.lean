module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Star
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.SuzukiModels
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry

/-!
# The Suzuki reciprocal escape

The other H-conjugate lies in the reversed component and normalizes O₂(H).
Its perfect image in the literal star quotient retains the Suzuki two-core
quotient. Its order makes the star component larger than 8!, so the proved
C.2.7 action theorem supplies a nontrivial radical intersection. The same
image normalizes this radical, contradicting the complete star-model test.

This discharges the contrary generalized-Fitting containment on the same
pushing-up witnesses. The source theorem preserves the original Sylow,
module, odd actor, quotient marking and failure-of-uniqueness premise.
Source: Aschbacher--Smith, 4.2.5--10, printed pp.609--610, using C.2.7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]

private theorem suzuki_card_lower (m : ℕ) (hm : 0 < m) :
    29120 ≤ Nat.card (SuzukiMatrixGroup m) := by
  rw [suzukiMatrixGroup_card m hm]
  have hq : 8 ≤ 2^(2*m+1) :=
    (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : 3 ≤ 2*m+1))
  have hs : 64 ≤ (2^(2*m+1))^2 := by nlinarith
  have hh := Nat.mul_le_mul (Nat.mul_le_mul (by omega : 65 ≤ (2^(2*m+1))^2+1) hs)
    (by omega : 7 ≤ 2^(2*m+1)-1)
  exact hh

theorem no_source_suzuki_normalizing_radical
    {H R M K J : Subgroup G} (h : Input KnownSimple.IsKnownSimple H R M K)
    (hJ : J ≤ M ⊓ K) (hn : J ≤ normalizer (R : Set G))
    [Group.IsPerfect J] {m : ℕ} (hm : 0 < m)
    (e : (J ⧸ pCore 2 J) ≃* SuzukiMatrixGroup m) : False := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : IsSimpleGroup (J ⧸ pCore 2 J) := e.isSimpleGroup
  let E := starImage K R J
  let C := starImage K R K
  let P := starM K R M
  have hEK : E ≤ C := map_mono (comap_mono (hJ.trans inf_le_right))
  have hEP : E ≤ P := map_mono (comap_mono hJ)
  obtain ⟨a,_⟩ := starSubgroupMap_coreQuotient_equiv h (hJ.trans inf_le_right)
  let b : (E ⧸ pCore 2 E) ≃* SuzukiMatrixGroup m := a.symm.trans e
  have hlo : 29120 ≤ Nat.card E := (suzuki_card_lower m hm).trans (by
    rw [← Nat.card_congr b.toEquiv]
    exact Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card _))
  have hp : 29120 ≤ Nat.card P := hlo.trans (Nat.card_le_card_of_injective
    (inclusion hEP) (inclusion_injective hEP))
  have hPC : P < C := (star_thompson_intersection_from_source h).2
  have hlt : Nat.card P < Nat.card C := lt_of_not_ge (fun hh =>
    hPC.ne (eq_of_le_of_card_ge hPC.le hh))
  obtain ⟨n,he⟩ := card_dvd_of_le hPC.le
  have hn2 : 2 ≤ n := by nlinarith
  have hlarge : 40320 < Nat.card C := by nlinarith
  have hU := (star_intersection_placement_from_source_of_large_order h hlarge).1
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective
    (f := starSubgroupMap K R J (hJ.trans inf_le_right))
    (starSubgroupMap_surjective K R J (hJ.trans inf_le_right))
  have hNR : E ≤ normalizer (starImage K R R : Set (StarQuotient K R)) := by
    let D := K ⊔ R
    let q := QuotientGroup.mk' (starKernel K R)
    have hJD : J.subgroupOf D ≤ normalizer (R.subgroupOf D : Set D) := by
      rw [←subgroupOf_normalizer_eq (show R ≤ D from le_sup_right)]
      exact comap_mono hn
    exact (map_mono hJD).trans (le_normalizer_map q)
  apply SuzukiModels.no_radical_model hm b (star_model_from_source h) hlarge
    ((starImage K R R).subgroupOf C) hU (inclusion hEK) (inclusion_injective hEK)
  rintro _ ⟨j,rfl⟩
  apply mem_normalizer_iff.mpr
  intro u
  exact mem_normalizer_iff.mp (hNR j.property) (u : StarQuotient K R)

/-- The terminal Suzuki contradiction discharges the escape on the original witnesses. -/
theorem suzuki_escape_case_of_not_unique {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    {m : ℕ} (hm : 0 < m)
    (e : ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* SuzukiMatrixGroup m)
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
  let B := K.map (normalizer (L : Set G)).subtype
  let E := L.map (MulAut.conj t).toMonoidHom
  let c : E ≃* L := (L.equivMapOfInjective (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective).symm
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective (f := c.symm.toMonoidHom) c.symm.surjective
  let q := QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  let a : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans e
  have hEB : E ≤ B := hE.trans inf_le_left
  have hEH : E ≤ H := hE.trans inf_le_right
  have hEN : E ≤ normalizer (H.pCoreIn 2 : Set G) :=
    hEH.trans (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  exact no_source_suzuki_normalizing_radical (reciprocal_source_input hd K hK hfK hout)
    (le_inf (le_inf hEH (hEB.trans (map_subtype_le _))) hEB) hEN hm (q.trans a)

end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
