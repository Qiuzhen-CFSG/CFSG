module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneMS
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneBaumannAt

/-!
# The actual guarded plane MS pair

Baumann saturation identifies the plane radical on L Baum(T).
Relative Sylow restriction proves the odd-index condition; ambient
normalizer uniqueness excludes every nontrivial characteristic
subgroup normal in that product. This constructs the full MS pair
using Structural1222At only at its original guarded component.
Source: Aschbacher--Smith 13.2.2(10), p.878, used in 13.4.7(4), p.903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The Baumann subgroup is inherited by the actual plane radical, and is
exactly that radical's intersection with its product with L. -/
theorem original_plane_radical_baumann_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2)
    (hne : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    ChapterB.baumann (T : Subgroup G) = ChapterB.baumann (B.pCoreIn 2) ∧
      B.pCoreIn 2 ⊓ (L ⊔ ChapterB.baumann (T : Subgroup G)) =
        ChapterB.baumann (T : Subgroup G) := by
  obtain ⟨q,e,he,hk,hc,_,hR,hJq,hSq⟩ :=
    exists_original_plane_full_baumann_marking_at h structural D m eL W hW hTW hB hJ hne
  have hsat := (original_plane_baumann_of_thompson_one_bound_at
    h structural D m eL W hW hTW hB hJ hne).2.2
  let X := L ⊔ (T : Subgroup G)
  let R := B.pCoreIn 2
  let S := ChapterB.baumann (T : Subgroup G)
  let J := L ⊔ S
  have hTB : (T : Subgroup G) ≤ B := hB ▸ le_inf le_sup_right hTW
  have hBX : B ≤ X := hB ▸ inf_le_left
  have hRX : R ≤ X := (pCoreIn_le 2 B).trans hBX
  have hSX : S ≤ X := inf_le_left.trans le_sup_right
  have hRT : R ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow B (T.subtype hTB)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTB] at hh
  have hrank : 1 < ChapterB.twoRank (T : Subgroup G) := by
    have hb := elementary_card_le_maxOrder (T : Subgroup G) V D.le_sylow D.elementary
    rw [m.card_module,ChapterB.maxOrder_eq_two_pow_rank] at hb
    by_contra! hn
    have hh := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2) hn
    norm_num at hh
    omega
  have hJR : elementaryAbelianMaxJ (T : Subgroup G) ≤ R := by
    rw [←ChapterB.thompsonJ_zero]
    exact (ChapterB.lemma_B_2_3_1 _ (by decide) hrank).trans hJ
  have hfull : (R.subgroupOf X).map q = ChapterB.Offenders.D 6 :=
    le_antisymm hR (hJq ▸ map_mono (comap_mono hJR))
  have hQR : X.pCoreIn 2 ≤ R := by
    have hQT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
      have hh := pCoreIn_le_sylow X (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right))
      rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)] at hh
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X) (hQT.trans hTB)
      (hBX.trans (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
  have hSR : S ≤ R := by
    intro s hs
    have hqs : q ⟨s,hSX hs⟩ ∈ (R.subgroupOf X).map q := by
      rw [hfull,←hSq]
      exact mem_map_of_mem q hs
    obtain ⟨r,hr,hrs⟩ := hqs
    have hx : (⟨s,hSX hs⟩ : X) * r⁻¹ ∈ q.ker := by
      change q (⟨s,hSX hs⟩ * r⁻¹) = 1
      rw [map_mul,map_inv,hrs,mul_inv_cancel]
    have hxR : s * r.val⁻¹ ∈ R :=
      hQR (mem_map_of_mem X.subtype (hk ▸ hx))
    have hh : (s * r.val⁻¹) * r.val ∈ R := R.mul_mem hxR hr
    simpa only [inv_mul_cancel_right] using hh
  refine ⟨ChapterB.lemma_B_2_3_4 _ _ hSR hRT,?_⟩
  apply le_antisymm
  · intro r hr
    have hqr : q ⟨r,hRX hr.1⟩ ∈ (S.subgroupOf X).map q := by
      rw [hSq,←hfull]
      exact mem_map_of_mem q hr.1
    obtain ⟨s,hs,hsr⟩ := hqr
    let x : X := ⟨r,hRX hr.1⟩ * s⁻¹
    have hx : x ∈ q.ker := by
      change q (⟨r,hRX hr.1⟩ * s⁻¹) = 1
      rw [map_mul,map_inv,hsr,mul_inv_cancel]
    have hxc : x.val ∈ centralizer (V : Set G) := by
      rw [hc] at hx
      intro v hv
      exact congrArg Subtype.val (hx ⟨v,D.le_sylow.trans le_sup_right hv⟩ hv)
    have hxj : x.val ∈ J := mul_mem hr.2 (inv_mem (mem_sup_right hs))
    have hxs : x.val ∈ S := (hsat.symm ▸ show x.val ∈ J ⊓ centralizer (V : Set G) from ⟨hxj,hxc⟩).1
    have hh : (r * s.val⁻¹) * s.val ∈ S := S.mul_mem hxs hs
    simpa only [inv_mul_cancel_right] using hh
  · exact le_inf hSR le_sup_right

/-- The product, characteristic-two, SQTK and relative component clauses of MS1
on the original augmentation Baumann product. -/
theorem original_plane_baumann_ms1_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    :
    let B := ChapterB.baumann (T : Subgroup G)
    let J := L ⊔ B
    IsSQTK KnownSimple.IsKnownSimple J ∧
      generalizedFitting J = pCore 2 J ∧
      (∀ j ∈ J, ∃ l ∈ L, ∃ b ∈ B, l*b=j) ∧
      (L.subgroupOf J).IsCComponent := by
  let X := L ⊔ (T : Subgroup G)
  let B := ChapterB.baumann (T : Subgroup G)
  let J := L ⊔ B
  have hJX : J ≤ X := sup_le le_sup_left (inf_le_left.trans le_sup_right)
  have hXN : X ≤ normalizer (L : Set G) := sup_le L.le_normalizer D.sylow_normalizes_component
  have hTNB : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)
  have hXNJ : X ≤ normalizer (J : Set G) :=
    sup_le (le_sup_left.trans J.le_normalizer)
      ((le_inf D.sylow_normalizes_component hTNB).trans
        (normalizer_inf_normalizer_le_normalizer_sup L B))
  let Ji := J.subgroupOf X
  let : Ji.Normal := normal_subgroupOf_of_le_normalizer hXNJ
  let ej : Ji ≃* J := subgroupOfEquivOfLe hJX
  have hcore : (pCore 2 J).map (inclusion hJX) = (pCore 2 X) ⊓ Ji := by
    have hm := congrArg (map Ji.subtype) (pCore_map_iso 2 ej.symm)
    rw [pCore_subnormal_eq_comap 2 (inferInstance : Ji.Normal).isSubnormal,
      map_comap_eq,range_subtype,inf_comm] at hm
    have he : Ji.subtype.comp ej.symm.toMonoidHom = inclusion hJX := by
      ext x
      rfl
    simpa only [map_map,he] using hm
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  have hVJ : V ≤ J := D.le_component.trans le_sup_left
  let Ui := V.subgroupOf X
  let : Ui.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.normalizes ((structural L h).2.2 V D).1)
  obtain ⟨q,hq,_,_,hk⟩ := LocalGeometry.exists_core_product_permutation_at D m h structural eL
  let eu : Ui ≃* V := subgroupOfEquivOfLe hVX
  let ei := eu.trans m.coordinate
  have hei (x : X) (v : Ui) : (ei (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (ei v).toAdd := hq x (eu v)
  have hcX : centralizer (Ui : Set X) = pCore 2 X :=
    (ChapterB.Offenders.SixCorePoint.kernel_centralizer Ui q ei hei).symm.trans hk
  have hcJ : centralizer (V.subgroupOf J : Set J) = pCore 2 J := by
    apply map_injective (inclusion_injective hJX)
    rw [hcore]
    apply le_antisymm
    · rintro x ⟨j,hj,rfl⟩
      refine ⟨?_,j.property⟩
      rw [←hcX]
      intro v hv
      exact Subtype.ext (congrArg (fun x : J => (x : G)) (hj ⟨v.val,hVJ hv⟩ hv))
    · intro x hx
      refine ⟨⟨x.val,hx.2⟩,?_,rfl⟩
      intro v hv
      have hh := (hcX.symm ▸ hx.1) ⟨v.val,hVX hv⟩ hv
      exact Subtype.ext (congrArg (fun x : X => (x : G)) hh)
  have hfit : generalizedFitting J = pCore 2 J := by
    let := D.elementary
    have hVQ : V.subgroupOf J ≤ pCore 2 J := by
      rw [←hcJ]
      intro v hv w hw
      exact Subtype.ext (V.le_centralizer hv w.val hw)
    apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    rw [←hcJ]
    exact centralizer_le (hVQ.trans_eq hcJ.symm)
  have hs := h.source_normalizer_sqtk_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hsJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (hJX.trans hXN))).mp
      (hs.subgroup (J.subgroupOf (normalizer (L : Set G))))
  let : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer (hJX.trans hXN)
  refine ⟨hsJ,hfit,?_,?_⟩
  · intro j hj
    have hm : (⟨j,hj⟩ : J) ∈ L.subgroupOf J ⊔ B.subgroupOf J := by
      rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
      exact mem_top _
    obtain ⟨l,hl,b,hb,he⟩ := mem_sup_of_normal_left.mp hm
    exact ⟨l,hl,b,hb,congrArg Subtype.val he⟩
  · have hc : (L.subgroupOf X).IsCComponent := h.maximal_faithful.1.1.1
    exact hc.subgroupOf_of_le le_sup_left hJX


/-- The original plane radical and ambient uniqueness supply the literal
MS2(a) and MS3 conditions on L Baum(T). -/
theorem original_plane_ms_conditions_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hP : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (eP : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2)
    (hne : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hescape : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) :
    let S := ChapterB.baumann (T : Subgroup G)
    ChapterC.MSOddIndexRadical (S.subgroupOf (L ⊔ S)) ∧
      ChapterC.MSCharacteristicCondition (S.subgroupOf (L ⊔ S)) := by
  obtain ⟨hBaum,hRBJ⟩ := original_plane_radical_baumann_at
    h structural D m eL W hW hTW hP hJ hne
  let X := L ⊔ (T : Subgroup G)
  let P := B
  let R := P.pCoreIn 2
  let B := ChapterB.baumann (T : Subgroup G)
  let J := L ⊔ B
  let PJ := P.subgroupOf J
  let BJ := B.subgroupOf J
  have hTP : (T : Subgroup G) ≤ P := by
    dsimp only [P]
    rw [hP]
    exact le_inf le_sup_right hTW
  have hPX : P ≤ X := by
    dsimp only [P]
    rw [hP]
    exact inf_le_left
  have hBR : B ≤ R := by
    change ChapterB.baumann (T : Subgroup G) ≤ R
    rw [hBaum]
    exact inf_le_left
  have hBP : B ≤ P := hBR.trans (pCoreIn_le 2 P)
  have hBX : B ≤ X := hBP.trans hPX
  have hJX : J ≤ X := sup_le le_sup_left hBX
  have hXN : X ≤ normalizer (L : Set G) := sup_le L.le_normalizer D.sylow_normalizes_component
  have hPNB : P ≤ normalizer (B : Set G) := by
    change P ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)
    rw [hBaum]
    exact (P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))).trans
      (normalizer_le_normalizer_baumann R)
  have hPNJ : P ≤ normalizer (J : Set G) :=
    (le_inf (hPX.trans hXN) hPNB).trans (normalizer_inf_normalizer_le_normalizer_sup L B)
  have hTNJ : (T : Subgroup G) ≤ normalizer (J : Set G) := hTP.trans hPNJ
  have hXNJ : X ≤ normalizer (J : Set G) :=
    sup_le (le_sup_left.trans J.le_normalizer) hTNJ
  have hcore : PJ.pCoreIn 2 = BJ := by
    let JP := J.subgroupOf P
    let : JP.Normal := normal_subgroupOf_of_le_normalizer hPNJ
    let f : PJ ≃* JP := {
      toFun := fun x => ⟨⟨x,x.property⟩,x.val.property⟩
      invFun := fun x => ⟨⟨x,x.property⟩,x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
    have hf := pCore_map_iso 2 f
    have hc := pCore_subnormal_eq_comap 2 (inferInstance : JP.Normal).isSubnormal
    have hm := congrArg (fun A : Subgroup JP => (A.map JP.subtype).map P.subtype) hf
    rw [hc,map_comap_eq,range_subtype] at hm
    rw [Subgroup.map_inf _ _ _ P.subtype_injective,subgroupOf_map_subtype] at hm
    have hinter : (J ⊓ P) ⊓ R = R ⊓ J := by
      ext x
      exact ⟨fun h => ⟨h.2,h.1.1⟩,fun h => ⟨⟨h.2,(pCoreIn_le 2 P) h.1⟩,h.1⟩⟩
    change _ = (J ⊓ P) ⊓ R at hm
    rw [hinter,hRBJ] at hm
    have hhom : P.subtype.comp (JP.subtype.comp f.toMonoidHom) = J.subtype.comp PJ.subtype := by
      ext x
      rfl
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le (show B ≤ J from le_sup_right)]
    simpa only [pCoreIn,map_map,hhom] using hm
  have hproper : PJ < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro ht
    have hJP : J ≤ P := fun j hj =>
      (show (⟨j,hj⟩ : J) ∈ PJ from ht ▸ mem_top _)
    have hLP : L ≤ P := le_sup_left.trans hJP
    let : Group.IsSolvable P := SymmetricThreeTwoCore.solvable eP
    have hsL : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective hLP)
    have hc : (L.subgroupOf X).IsCComponent := h.maximal_faithful.1.1.1
    apply hc.not_isSolvable
    let := hsL
    exact Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show L ≤ X from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show L ≤ X from le_sup_left)).injective
  have hodd : Odd PJ.index := by
    let Ji := J.subgroupOf X
    let : Ji.Normal := normal_subgroupOf_of_le_normalizer hXNJ
    obtain ⟨Q,hQ⟩ := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).exists_sylow_map_eq_inf_of_normal Ji
    let ej : Ji ≃* J := subgroupOfEquivOfLe hJX
    let S := Q.mapSurjective (f := ej.toMonoidHom) ej.surjective
    have hST : (S : Subgroup J).map J.subtype ≤ (T : Subgroup G) := by
      change ((Q : Subgroup Ji).map ej.toMonoidHom).map J.subtype ≤ _
      have heq : ((Q : Subgroup Ji).map ej.toMonoidHom).map J.subtype =
          ((Q : Subgroup Ji).map Ji.subtype).map X.subtype := by
        rw [map_map,map_map]
        rfl
      rw [heq,hQ]
      exact (map_mono inf_le_left).trans (by
        rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)])
    have hSP : (S : Subgroup J) ≤ PJ := fun x hx => hTP (hST (mem_map_of_mem J.subtype hx))
    exact (Nat.not_even_iff_odd).mp (fun ht =>
      S.not_dvd_index ((even_iff_two_dvd.mp ht).trans (index_dvd_of_le hSP)))
  refine ⟨⟨PJ,hproper,hodd,hcore⟩,?_⟩
  intro C hC hne hn
  let ej : BJ ≃* B := subgroupOfEquivOfLe (show B ≤ J from le_sup_right)
  let E := C.map ej.toMonoidHom
  have hE : E.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y,hy,rfl⟩ := hx
    let b : MulAut BJ := ej.trans (a.trans ej.symm)
    refine ⟨b y,(characteristic_iff_le_comap.mp hC b) hy,?_⟩
    exact ej.apply_symm_apply _
  have hEne : E ≠ ⊥ := fun hz => hne ((C.map_eq_bot_iff_of_injective ej.injective).mp hz)
  let N := E.map B.subtype
  have hNne : N ≠ ⊥ := fun hz => hEne ((E.map_eq_bot_iff_of_injective B.subtype_injective).mp hz)
  have hmap : N = (C.map BJ.subtype).map J.subtype := by
    dsimp only [N,E]
    rw [map_map,map_map]
    rfl
  have hJN : J ≤ normalizer (N : Set G) := by
    rw [hmap]
    have hh := (C.map BJ.subtype).le_normalizer_map J.subtype
    let := hn
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  let := hE
  have hBN : normalizer (B : Set G) ≤ normalizer (N : Set G) :=
    normalizer_le_normalizer_characteristic_image B E
  have hXN : X ≤ normalizer (N : Set G) :=
    sup_le (le_sup_left.trans hJN) (hTP.trans (hPNB.trans hBN))
  have hNX : N ≤ X := (map_subtype_le E).trans hBX
  have hNM : normalizer (N : Set G) ≤ normalizer (L : Set G) :=
    D.normal_subgroup_normalizer_le h.toHypothesis1221 hNX hNne hXN
  exact hescape (hBN.trans hNM)

omit [Finite G] in
private theorem msOddIndex_of_intrinsic {B : Subgroup G}
    (hB : ChapterC.MSOddIndexRadical (B.subgroupOf (L ⊔ B))) : MSOddIndex L B := by
  let J := L ⊔ B
  obtain ⟨P,hP,ho,hc⟩ := hB
  change P.pCoreIn 2 = B.subgroupOf J at hc
  refine ⟨P.map J.subtype,?_,?_,?_⟩
  · refine lt_of_le_of_ne (map_subtype_le P) ?_
    intro he
    apply hP.ne
    apply map_injective J.subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype]
    exact he
  · have he : (P.map J.subtype).subgroupOf J = P :=
      comap_map_eq_self_of_injective J.subtype_injective P
    rwa [he]
  · rw [←map_pCoreIn_of_injective 2 P J.subtype J.subtype_injective,hc,
      map_subgroupOf_eq_of_le (show B ≤ J from le_sup_right)]

omit [Finite G] in
private theorem msCharacteristic_of_intrinsic {B : Subgroup G}
    (hB : ChapterC.MSCharacteristicCondition (B.subgroupOf (L ⊔ B))) :
    MSNoCharacteristicNormal L B := by
  let J := L ⊔ B
  let BJ := B.subgroupOf J
  let e : B ≃* BJ := (subgroupOfEquivOfLe (show B ≤ J from le_sup_right)).symm
  intro C hC hn
  let E := C.map e.toMonoidHom
  have hE : E.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y,hy,rfl⟩ := hx
    let b : MulAut B := e.trans (a.trans e.symm)
    refine ⟨b y,(characteristic_iff_le_comap.mp hC b) hy,?_⟩
    exact e.apply_symm_apply _
  have heq : E.map BJ.subtype = (C.map B.subtype).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le C).trans le_sup_right)]
    dsimp only [E]
    rw [map_map,map_map]
    congr 1
  by_contra hne
  have hEne : E ≠ ⊥ := fun hz => hne ((C.map_eq_bot_iff_of_injective e.injective).mp hz)
  exact hB E hE hEne (heq.symm ▸ hn)

/-- All MS clauses for the original ordinary plane, assuming its current
near-maximum branch and escape from the original component normalizer. -/
theorem original_plane_smallMSPair_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2)
    (hne : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hescape : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) :
    SmallMSPair KnownSimple.IsKnownSimple L (ChapterB.baumann (T : Subgroup G)) := by
  obtain ⟨hs,hf,hp,hc⟩ := original_plane_baumann_ms1_at h structural D m eL
  obtain ⟨hr,hn⟩ := original_plane_ms_conditions_at h structural D m eL W hW hTW hB eB hJ hne hescape
  refine ⟨inferInstance,hs,hf,hp,hc,?_,msOddIndex_of_intrinsic hr,
    msCharacteristic_of_intrinsic hn⟩
  exact Or.inr (Or.inl ⟨m.quotient.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)).symm⟩)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
