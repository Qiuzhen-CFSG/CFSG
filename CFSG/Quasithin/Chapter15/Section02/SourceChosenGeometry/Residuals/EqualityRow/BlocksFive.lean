module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.BlocksRankOne
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFivePlaneCentralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation
public import Theory.GroupTheory.OddSubgroupBlockNormalizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFiveThompson
public import Theory.GroupTheory.PCoreSubnormalExtension

/-!
# The actual A₅ chi-block exclusion in the equality row

The odd intersection in K∩X gives the original plane centralizer its
actual five-point Borel marking and places that Borel in KS. The parabolic
two-core QI normalizes each A₅ constituent, including an exchanged pair.
Inside XQI the marked action puts J(QI) in O₂(XQI), and odd Sylow index
puts this core in QI. Thompson-normalizer control contradicts equality-row
escape of the original block. No residual-identity packet is assumed.

Source: Aschbacher--Smith, preliminary 15.2.23, printed p.1115,
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem a5_sylowNormalizer_relIndex (P : Sylow 2 G)
    (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 5)) :
    (P : Subgroup G).relIndex (normalizer (P : Set G)) = 3 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker ≤ (P : Subgroup G) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  let R := P.mapSurjective hq
  have hmap : (normalizer (P : Set G)).map q =
      normalizer (R : Set (alternatingGroup (Fin 5))) := P.normalizer_map_surjective q hq
  have he := relIndex_map_map q (P : Subgroup G) (normalizer (P : Set G))
  have hkN : q.ker ≤ normalizer (P : Set G) := hk.trans P.toSubgroup.le_normalizer
  rw [sup_eq_left.mpr hk,sup_eq_left.mpr hkN] at he
  rw [←he,hmap]
  change (R : Subgroup (alternatingGroup (Fin 5))).relIndex
    (normalizer (R : Set (alternatingGroup (Fin 5)))) = 3
  have hc : Nat.card R = 4 := by
    rw [R.card_eq_multiplicity,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    decide +kernel
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R
  have hB : Nat.card (normalizer (R : Set (alternatingGroup (Fin 5)))) = 12 := by
    have hs : ∀ j : Fin 5,
        Nat.card (MulAction.stabilizer (alternatingGroup (Fin 5)) j) = 12 := by
      simp only [Nat.card_eq_fintype_card]
      decide +kernel
    rw [hi]
    exact hs i
  have hRN : (R : Subgroup (alternatingGroup (Fin 5))) ≤
      normalizer (R : Set (alternatingGroup (Fin 5))) := R.toSubgroup.le_normalizer
  have hm := ((R : Subgroup (alternatingGroup (Fin 5))).subgroupOf
    (normalizer (R : Set (alternatingGroup (Fin 5))))).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hRN).toEquiv,hc,hB] at hm
  change 4 * (R : Subgroup (alternatingGroup (Fin 5))).relIndex
    (normalizer (R : Set (alternatingGroup (Fin 5)))) = 12 at hm
  omega

private theorem a5_borel_eq_sylow_sup_odd (P : Sylow 2 G)
    (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 5))
    (D : Subgroup G) (hD : D ≤ normalizer (P : Set G))
    (ho : Odd (Nat.card D)) (hd : D ≠ ⊥) :
    normalizer (P : Set G) = (P : Subgroup G) ⊔ D := by
  let B := normalizer (P : Set G)
  let P' := (P : Subgroup G).subgroupOf B
  let D' := D.subgroupOf B
  have hnot : ¬ D ≤ (P : Subgroup G) := by
    intro hle
    obtain ⟨n,hn⟩ := (P.isPGroup'.to_le hle).exists_card_eq
    have hz : n = 0 := by
      by_contra hz
      exact ho.not_two_dvd_nat (hn ▸ dvd_pow_self 2 hz)
    exact hd (card_eq_one.mp (by simpa only [hz,pow_zero] using hn))
  have hi : P'.index = 3 := a5_sylowNormalizer_relIndex P e
  have hgen : P' ⊔ D' = ⊤ := (isCoatom_of_index_three P' hi).2 _
    (lt_of_le_of_ne le_sup_left (by
      intro he
      apply hnot
      intro a ha
      exact (le_sup_right.trans_eq he.symm) (show (⟨a,hD ha⟩ : B) ∈ D' from ha)))
  have hPB : (P : Subgroup G) ≤ B := P.toSubgroup.le_normalizer
  have hDB : D ≤ B := hD
  have hm := congrArg (map B.subtype) hgen
  simpa only [P',D',Subgroup.map_sup,map_subgroupOf_eq_of_le hPB,
    map_subgroupOf_eq_of_le hDB,← MonoidHom.range_eq_map,range_subtype] using hm.symm

variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (r : ResidualInput hsource H B)
include r

/-- The original A5 block centralizer has its actual Borel marking. -/
theorem a5_block_borel_marking (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I)
    (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 5)
    (hout : ¬ X.map I.subtype ≤ Mc) :
    let f := I.subtype.comp X.subtype
    (centralizer ((⁅V,B⁆ : Subgroup G) : Set G)).comap f = Mc.comap f ∧
      ∃ P : Sylow 2 X, ∃ e : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5),
        ∃ i : Fin 5,
          (P : Subgroup X).map f = planeSylow T (⁅V,B⁆ : Subgroup G) ⊓ X.map I.subtype ∧
          Mc.comap f = normalizer (P : Set X) ∧
          Mc.comap f = (MulAction.stabilizer (alternatingGroup (Fin 5)) i).comap
            (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) := by
  let f := I.subtype.comp X.subtype
  let W := (⁅V,B⁆ : Subgroup G).subgroupOf I
  let J := Mc.comap f
  have hZI : (⁅V,B⁆ : Subgroup G) ≤ I := r.plane_le_escape_for_blocks hI
  have hWQ : W ≤ pCore 2 I := by
    intro z hz
    have hzQ := ((mem_omegaOneCenterAmbient_iff _ _).mp
      (r.plane_le_escape_core_omega hI hfit hz)).1
    obtain ⟨q,hq,he⟩ := hzQ
    exact (Subtype.ext he : q = z) ▸ hq
  obtain ⟨R,hR⟩ := r.sylow_in_escape_for_blocks hI
  obtain ⟨P,hP⟩ := R.exists_subgroupOf_eq_of_subnormal X hX.subnormal
  have hWP : W ≤ centralizer ((P : Subgroup X).map X.subtype : Set I) := by
    rintro z hz p ⟨p,hp,rfl⟩
    apply Subtype.ext
    have hpR : (p : I) ∈ R := by
      change p ∈ (R : Subgroup I).subgroupOf X
      rwa [← hP]
    have hpS : ((p : I) : G) ∈ planeSylow T (⁅V,B⁆ : Subgroup G) :=
      hR ▸ mem_map_of_mem I.subtype hpR
    have hzS := (mem_omegaOneCenterAmbient_iff _ _).mp
      (r.plane_omega_for_blocks ▸ (show (z : G) ∈ (⁅V,B⁆ : Subgroup G) from hz))
    exact hzS.2.2 p hpS
  have hJ : J ≠ ⊤ := by
    intro he
    apply hout
    rintro x ⟨x,hx,rfl⟩
    exact (show (⟨x,hx⟩ : X) ∈ J from he ▸ mem_top _)
  have hCW : (centralizer (W : Set I)).comap X.subtype =
      (centralizer ((⁅V,B⁆ : Subgroup G) : Set G)).comap f := by
    ext x
    constructor
    · intro hx z hz
      exact congrArg I.subtype (hx ⟨z,hZI hz⟩ hz)
    · intro hx z hz
      exact Subtype.ext (hx z hz)
  have hCJ : (centralizer (W : Set I)).comap X.subtype ≤ J := by
    rw [hCW]
    intro x hx
    exact ((r.plane_centralizer_le_intersection hI) hx).1
  obtain ⟨hCJ_eq,hJN,e,i,hei⟩ := hb.centralizer_borel_of_sylow_fixed
    X hX P W hWQ hWP J hJ hCJ
  refine ⟨hCW.symm.trans hCJ_eq,P,e,i,?_,hJN,hei⟩
  rw [← map_map, hP, subgroupOf_map_subtype, map_inf _ _ _ I.subtype_injective, hR]

/-- Equality-row cubic escape discharges the properness premise of the Borel calculation. -/
theorem a5_block_borel_marking_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I)
    (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 5) :
    let f := I.subtype.comp X.subtype
    (centralizer ((⁅V,B⁆ : Subgroup G) : Set G)).comap f = Mc.comap f ∧
      ∃ P : Sylow 2 X, ∃ e : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5),
        ∃ i : Fin 5,
          (P : Subgroup X).map f = planeSylow T (⁅V,B⁆ : Subgroup G) ⊓ X.map I.subtype ∧
          Mc.comap f = normalizer (P : Set X) ∧
          Mc.comap f = (MulAction.stabilizer (alternatingGroup (Fin 5)) i).comap
            (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) :=
  r.a5_block_borel_marking hI hfit hX hb
    (r.alternating_block_not_le_partner_of_eq he (Or.inl rfl) hb)

/-- The actual block centralizer is contained in KS, using the constructed odd intersection. -/
theorem a5_block_centralizer_le_parabolic_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 5) :
    X.map I.subtype ⊓ centralizer ((⁅V,B⁆ : Subgroup G) : Set G) ≤
      (pResidual 2 H).map H.subtype ⊔ planeSylow T (⁅V,B⁆ : Subgroup G) := by
  obtain ⟨D,hDX,ho,hd,hDK⟩ := r.chi_block_odd_intersection hI hfit
    ⟨hX,Or.inr ⟨5,by decide,hb⟩⟩
  obtain ⟨hCJ,P,e,i,hP,hJN,_⟩ := r.a5_block_borel_marking_of_eq he hI hfit hX hb
  let f := I.subtype.comp X.subtype
  let D' := D.subgroupOf X
  have hDC : D' ≤ (centralizer ((⁅V,B⁆ : Subgroup G) : Set G)).comap f := by
    intro a ha
    exact r.residual_centralizes_plane (hDK (mem_map_of_mem I.subtype ha))
  have hDN : D' ≤ normalizer (P : Set X) := by
    rwa [hCJ,hJN] at hDC
  have ho' : Odd (Nat.card D') := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDX).toEquiv]
  have hd' : D' ≠ ⊥ := by
    intro he
    apply hd
    have hm := congrArg (map X.subtype) he
    simpa only [D',map_subgroupOf_eq_of_le hDX,Subgroup.map_bot] using hm
  have hgen := a5_borel_eq_sylow_sup_odd P e D' hDN ho' hd'
  have hm : (normalizer (P : Set X)).map f ≤
      (pResidual 2 H).map H.subtype ⊔ planeSylow T (⁅V,B⁆ : Subgroup G) := by
    rw [hgen,Subgroup.map_sup]
    apply sup_le
    · rw [hP]
      exact inf_le_left.trans le_sup_right
    · have he : D'.map f = D.map I.subtype := by
        rw [←map_map,map_subgroupOf_eq_of_le hDX]
      rw [he]
      exact hDK.trans le_sup_left
  rintro x ⟨⟨x,hx,rfl⟩,hc⟩
  have hn : (⟨x,hx⟩ : X) ∈ normalizer (P : Set X) := by
    rw [←hJN,←hCJ]
    exact hc
  exact hm (mem_map_of_mem f hn)

theorem a5_parabolic_core_normalizes_block
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 5) :
    (planeParabolicCore T H (⁅V,B⁆ : Subgroup G)).subgroupOf I ≤ normalizer (X : Set I) := by
  obtain ⟨D,hDX,ho,hd,hDK⟩ := r.chi_block_odd_intersection hI hfit
    ⟨hX,Or.inr ⟨5,by decide,hb⟩⟩
  let Q := planeParabolicCore T H (⁅V,B⁆ : Subgroup G)
  have hQI : Q ≤ I := (pCoreIn_le 2 _).trans
    ((r.residual_sup_planeSylow_le_for_blocks hI).trans inf_le_right)
  have hDQ : D ≤ normalizer (Q.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hQI]
    intro x hx
    exact r.planeParabolicCore_normalized hI
      (map_subtype_le (pResidual 2 H) (hDK (mem_map_of_mem I.subtype hx)))
  have hZ : IsPGroup 2 (center X) := pCore_isPGroup.to_le (by
    intro z hz
    apply hb.2.1.centralizer_blockU.le
    intro u hu
    exact mem_center_iff.mp hz u)
  apply normalizes_of_odd_subgroup_and_commuting_conjugates X (Q.subgroupOf I) D
    (isPGroup_pCoreIn 2 _).comap_subtype ho hd hDX hDQ hZ
  intro q hq hne
  have hqX : IsQuasisimple (X ⧸ pCore 2 X) := by
    obtain ⟨e⟩ := hb.2.2.quotient_iso
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup (X ⧸ pCore 2 X) := e.isSimpleGroup
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    let : IsQuasisimple (alternatingGroup (Fin 5)) := {
      toIsPerfect := inferInstance
      simple := ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
    exact IsQuasisimple.of_mulEquiv e.symm
  exact hX.commutator_eq_bot_of_quasisimple_quotient (hX.map_equiv (MulAut.conj q)) hqX hne
/-- No A₅ block occurs, whether S fixes it or exchanges it with a commuting block. -/
theorem a5_block_false_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 5) : False := by
  let P0 := (pResidual 2 H).map H.subtype ⊔ planeSylow T (⁅V,B⁆ : Subgroup G)
  let Q0 := planeParabolicCore T H (⁅V,B⁆ : Subgroup G)
  let P := P0.subgroupOf I
  let Q := Q0.subgroupOf I
  have hPI : P0 ≤ I := (r.residual_sup_planeSylow_le_for_blocks hI).trans inf_le_right
  have hQI : Q0 ≤ I := (pCoreIn_le 2 _).trans hPI
  have heQ : P.pCoreIn 2 = Q := pCoreIn_subgroupOf 2 P0 I hPI
  have hQX : Q ≤ normalizer (X : Set I) := r.a5_parabolic_core_normalizes_block hI hfit hX hb
  have hPodd : Odd P.index := by
    obtain ⟨S,hS⟩ := r.sylow_in_escape_for_blocks hI
    have hSP : (S : Subgroup I) ≤ P := by
      intro s hs
      exact (le_sup_right : planeSylow T (⁅V,B⁆ : Subgroup G) ≤ P0) (hS ▸ mem_map_of_mem I.subtype hs)
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
  obtain ⟨hCJ,S,_q,_i,_hS,hJN,_⟩ := r.a5_block_borel_marking_of_eq he hI hfit hX hb
  have hBQ : (normalizer (S : Set X)).map X.subtype ≤ normalizer (Q : Set I) := by
    rw [←subgroupOf_normalizer_eq hQI]
    rintro b ⟨x,hx,rfl⟩
    have hxC : (x : G) ∈ X.map I.subtype ⊓ centralizer ((⁅V,B⁆ : Subgroup G) : Set G) := by
      refine ⟨mem_map_of_mem I.subtype x.property,?_⟩
      have hc : x ∈ (centralizer ((⁅V,B⁆ : Subgroup G) : Set G)).comap (I.subtype.comp X.subtype) := by
        rw [hCJ,hJN]
        exact hx
      exact hc
    exact ((r.a5_block_centralizer_le_parabolic_of_eq he hI hfit hX hb).trans
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
  exact r.planeParabolicCore_thompson_not_le_core hI
    (r.alternating_block_not_le_partner_of_eq he (Or.inl rfl) hb) hcore' hm'
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput
