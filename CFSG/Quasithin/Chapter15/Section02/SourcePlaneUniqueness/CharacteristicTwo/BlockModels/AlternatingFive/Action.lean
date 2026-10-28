module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.AlternatingFiveCentralizer
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.AlternatingFive.Normalizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFiveThompson
public import Theory.GroupTheory.PCoreSubnormalExtension

/-!
# Excluding every alternating-five block in the escaping-plane case

The parabolic two-core QI normalizes each A₅ constituent, including the two
constituents exchanged by S. Work inside XQI, where X is normal. The actual
Borel of X normalizes QI, so its binary action puts J(QI) in O₂(XQI).
Subnormality of X and the odd index of KS give O₂(XQI) ≤ QI. The original
Thompson-normalizer control now contradicts X escaping the partner.

This proves the singleton and exchanged-orbit cases with the literal
subgroups and their induced actions. The earlier Kc orbit alternative is
supplied by qt-e-152-plane-geometry and qt-e-152-small-parabolic, with final
discharge retained by qt-e-152-plane-characteristic-two.

Source: Aschbacher--Smith, preliminary 15.2.23, printed p.1115,
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- No A₅ block occurs, whether S fixes it or exchanges it with a commuting block. -/
theorem a5_block_false
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 5) : False := by
  let P0 := (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS
  let Q0 := planeParabolicCore T H ZS
  let P := P0.subgroupOf I
  let Q := Q0.subgroupOf I
  have hPI : P0 ≤ I := (d.residual_sup_planeSylow_le hI).trans inf_le_right
  have hQI : Q0 ≤ I := (pCoreIn_le 2 _).trans hPI
  have heQ : P.pCoreIn 2 = Q := pCoreIn_subgroupOf 2 P0 I hPI
  have hQX : Q ≤ normalizer (X : Set I) := d.a5_parabolic_core_normalizes_block hI hfit hX hb
  have hPodd : Odd P.index := by
    obtain ⟨S,hS⟩ := d.sylow_in_escape hI
    have hSP : (S : Subgroup I) ≤ P := by
      intro s hs
      exact (le_sup_right : planeSylow T ZS ≤ P0) (hS ▸ mem_map_of_mem I.subtype hs)
    exact Nat.not_even_iff_odd.mp (by
      rw [even_iff_two_dvd]
      exact fun hh => S.not_dvd_index (hh.trans (index_dvd_of_le hSP)))
  have hcore : (X ⊔ Q).pCoreIn 2 ≤ Q := by
    rw [←heQ]
    exact subnormal_twoCore_extension_le X P hX.subnormal hPodd (heQ.symm ▸ hQX)
  let N := X ⊔ Q
  let X' := X.subgroupOf N
  let Q' := Q.subgroupOf N
  have hXN : X ≤ N := le_sup_left
  have hQN : Q ≤ N := le_sup_right
  let : X'.Normal := normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hQX)
  let e : X' ≃* X := subgroupOfEquivOfLe hXN
  have hb' : ChapterC.IsAlternatingBlock X' 5 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv e.symm hb
  have hc' : pCore 2 N ≤ Q' := by
    intro x hx
    exact hcore (mem_map_of_mem N.subtype hx)
  have hUQ : (ChapterC.blockU X').map X'.subtype ≤ Q' :=
    ((map_mono ChapterC.blockU_le_core).trans
      (pCoreIn_le_of_subnormal 2 (show X'.IsSubnormal from Normal.isSubnormal inferInstance))).trans hc'
  obtain ⟨hCJ,S,_q,_i,_hS,hJN,_⟩ := d.a5_block_borel_marking_of_source horbit hI hfit hX hb
  have hBQ : (normalizer (S : Set X)).map X.subtype ≤ normalizer (Q : Set I) := by
    rw [←subgroupOf_normalizer_eq hQI]
    rintro b ⟨x,hx,rfl⟩
    have hxC : (x : G) ∈ X.map I.subtype ⊓ centralizer (ZS : Set G) := by
      refine ⟨mem_map_of_mem I.subtype x.property,?_⟩
      have hc : x ∈ (centralizer (ZS : Set G)).comap (I.subtype.comp X.subtype) := by
        rw [hCJ,hJN]
        exact hx
      exact hc
    exact ((d.a5_block_centralizer_le_parabolic horbit hI hfit hX hb).trans
      (P0.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore _))) hxC
  let S' := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hB' : (normalizer (S' : Set X')).map X'.subtype ≤ normalizer (Q' : Set N) := by
    rw [←subgroupOf_normalizer_eq hQN]
    rintro b ⟨x,hx,rfl⟩
    have hs : (normalizer (S' : Set X')).map e.toMonoidHom = normalizer (S : Set X) := by
      change (normalizer ((S' : Subgroup X') : Set X')).map e.toMonoidHom = _
      rw [map_equiv_normalizer_eq]
      have he : (S' : Subgroup X').map e.toMonoidHom = (S : Subgroup X) := by
        change ((S : Subgroup X).map e.symm.toMonoidHom).map e.toMonoidHom = _
        rw [map_map]
        have hh : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id X :=
          MonoidHom.ext (fun x => e.apply_symm_apply x)
        rw [hh,map_id]
      rw [he]
      rfl
    exact hBQ (mem_map_of_mem X.subtype (hs ▸ mem_map_of_mem e.toMonoidHom hx))
  have hj := hb'.normal_thompson_le_core X' Q'
    (isPGroup_pCoreIn 2 _).comap_subtype.comap_subtype hUQ S' hB'
  have hgen : X' ⊔ Q' = ⊤ := by
    rw [←subgroupOf_sup hXN hQN,subgroupOf_self]
  rw [hgen] at hj
  have hj' : elementaryAbelianMaxJ Q' ≤ pCore 2 N := by
    apply hj.trans
    exact pCoreIn_le_of_subnormal 2 (show (⊤ : Subgroup N).IsSubnormal from .top)
  have hm := map_mono (f := N.subtype) hj'
  rw [←elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective,
    map_subgroupOf_eq_of_le hQN] at hm
  change elementaryAbelianMaxJ Q ≤ (X ⊔ Q).pCoreIn 2 at hm
  have hm' := map_mono (f := I.subtype) hm
  rw [←elementaryAbelianMaxJ_map_injective I.subtype I.subtype_injective,
    map_subgroupOf_eq_of_le hQI,map_pCoreIn_of_injective 2 _ I.subtype I.subtype_injective,
    Subgroup.map_sup,map_subgroupOf_eq_of_le hQI] at hm'
  have hcore' := map_mono (f := I.subtype) hcore
  rw [map_pCoreIn_of_injective 2 _ I.subtype I.subtype_injective,
    Subgroup.map_sup,map_subgroupOf_eq_of_le hQI] at hcore'
  exact d.planeParabolicCore_thompson_not_le_core hI
    (d.alternating_block_not_le_partner horbit hI hfit hX (Or.inl rfl) hb) hcore' hm'
end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
