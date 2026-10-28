module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.FirstFlagAlpha
public import Theory.GroupTheory.SylowActionRadical
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryBaumannAt
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# The actual first-flag Baumann MS pair with the covering kernel retained

The preimage of the image two-core in the prescribed Sylow is radical in
its relative normalizer inside M₁. This supplies a local group P containing
T with O₂(P)=R₁, without identifying R₁ with O₂(L₁T) in the covered row.
The full-image alpha calculation gives R₁ ∩ L Baum(R₁)=Baum(R₁).
Restricting O₂(P) to P ∩ L Baum(R₁) now gives MS2(a), including its proper
odd-index condition. Ambient two-local uniqueness supplies MS3.

The literal product L Baum(R₁) is normal in LT and inherits characteristic
two; SQTK and the original relative C-component supply MS1. Thus covered
Baumann-normalizer escape constructs a genuine SmallMSPair on these exact
subgroups. The C.1.32 exclusion of this pair, the resulting normalizer
bound and covered recognition are subsequent source steps.

Source: Aschbacher--Smith C.1.31--32, pp.135--136; C.1.37, pp.142--143;
Notation 13.2.1 and 13.2.2(7), pp.877--878.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Solvable Nonsolvable
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- T normalizes its literal action-core preimage R₁. -/
theorem sylow_normalizes_firstFlagCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    (T : Subgroup G) ≤ normalizer (firstFlagCore h structural D m : Set G) := by
  let f := (firstFlagAction h structural D m).rangeRestrict.comp
    (inclusion (show (T : Subgroup G) ≤ firstFlagNormalizer T L V from sylow_le_firstFlagNormalizer))
  let U := (pCore 2 (firstFlagAction h structural D m).range).comap f
  change (T : Subgroup G) ≤ normalizer (U.map (T : Subgroup G).subtype : Set G)
  have hh := U.le_normalizer_map (T : Subgroup G).subtype
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh

/-- The original R₁ is the two-core of its relative normalizer in M₁,
including in the covered row. -/
theorem firstFlagCore_relative_normalizer_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    (firstFlagNormalizer T L V ⊓
      normalizer (firstFlagCore h structural D m : Set G)).pCoreIn 2 =
        firstFlagCore h structural D m := by
  let P := firstFlagNormalizer T L V
  let S := T.subtype (show (T : Subgroup G) ≤ P from sylow_le_firstFlagNormalizer)
  let f := (firstFlagAction h structural D m).rangeRestrict
  let Ri := (S : Subgroup P) ⊓ (pCore 2 (firstFlagAction h structural D m).range).comap f
  let R := firstFlagCore h structural D m
  have hRm : Ri.map P.subtype = R := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨⟨p.val,hp.1⟩,hp.2,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t.val,sylow_le_firstFlagNormalizer t.property⟩,⟨t.property,ht⟩,rfl⟩
  have hRP : R ≤ P := hRm ▸ map_subtype_le Ri
  have hRi : Ri = R.subgroupOf P := by
    rw [←hRm,subgroupOf,comap_map_eq_self_of_injective P.subtype_injective]
  have hnorm : (normalizer (Ri : Set P)).map P.subtype =
      P ⊓ normalizer (R : Set G) := by
    rw [hRi,←subgroupOf_normalizer_eq hRP,subgroupOf_map_subtype,inf_comm]
  have he := sylow_inf_corePreimage_normalizer_core f
    (firstFlagAction h structural D m).rangeRestrict_surjective S
  have hm := congrArg (map P.subtype) he
  rw [map_pCoreIn_of_injective 2 _ P.subtype P.subtype_injective,hnorm,hRm] at hm
  exact hm

open Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

/-- The original covered full-image Baumann product satisfies MS2(a) and MS3.
The local group is the relative normalizer of the actual R₁ inside M₁. -/
theorem covered_firstFlagCore_ms_conditions_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hescape : ¬ normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G)) :
    let R := firstFlagCore h structural D m
    let B := ChapterB.baumann R
    ChapterC.MSOddIndexRadical (B.subgroupOf (L ⊔ B)) ∧
      ChapterC.MSCharacteristicCondition (B.subgroupOf (L ⊔ B)) := by
  have hRBJ := covered_firstFlagCore_product_intersection_of_escape
    h structural D m hc z hzT hzL hescape
  let X := L ⊔ (T : Subgroup G)
  let R := firstFlagCore h structural D m
  let P := firstFlagNormalizer T L V ⊓ normalizer (R : Set G)
  let B := ChapterB.baumann R
  let J := L ⊔ B
  let PJ := P.subgroupOf J
  let BJ := B.subgroupOf J
  have hRT : R ≤ T := map_subtype_le _
  have hRP : R ≤ P := le_inf (hRT.trans sylow_le_firstFlagNormalizer) R.le_normalizer
  have hPR : P.pCoreIn 2 = R := firstFlagCore_relative_normalizer_core h structural D m
  have hPX : P ≤ X := inf_le_left.trans inf_le_left
  have hBR : B ≤ R := inf_le_left
  have hBP : B ≤ P := hBR.trans hRP
  have hBX : B ≤ X := hBP.trans hPX
  have hJX : J ≤ X := sup_le le_sup_left hBX
  have hTP : (T : Subgroup G) ≤ P := le_inf sylow_le_firstFlagNormalizer
    (sylow_normalizes_firstFlagCore h structural D m)
  have hXN : X ≤ normalizer (L : Set G) := sup_le L.le_normalizer D.sylow_normalizes_component
  have hPNB : P ≤ normalizer (B : Set G) :=
    inf_le_right.trans (normalizer_le_normalizer_baumann R)
  have hPNJ : P ≤ normalizer (J : Set G) :=
    (le_inf (hPX.trans hXN) hPNB).trans (normalizer_inf_normalizer_le_normalizer_sup L B)
  have hXNJ : X ≤ normalizer (J : Set G) :=
    sup_le (le_sup_left.trans J.le_normalizer) (hTP.trans hPNJ)
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
      exact ⟨fun h => ⟨h.2,h.1.1⟩,fun h => ⟨⟨h.2,hRP h.1⟩,h.1⟩⟩
    change _ = (J ⊓ P) ⊓ P.pCoreIn 2 at hm
    rw [hPR] at hm
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
    apply hzL
    have hLP : L ≤ P := le_sup_left.trans hJP
    have hLc : L ≤ centralizer ({z.val} : Set G) := hLP.trans
      ((inf_le_left : P ≤ firstFlagNormalizer T L V).trans
        ((first_flag_normalizer_eq_centralizer h structural D m z hzT hzL).le.trans inf_le_right))
    intro l hl
    exact mem_centralizer_singleton_iff.mp (hLc hl)
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
  have hp : IsPGroup 2 N := ((T.isPGroup'.to_le (hBR.trans hRT)).to_subgroup E).map B.subtype
  have hNM : normalizer (N : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal
      (h.source_normalizer_maximal_unique_at (fun L h => structural G T L h)
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2 hp hNne hXN
  exact hescape (hBN.trans hNM)

/-- The actual first-core Baumann product has characteristic two, is SQTK,
and contains the original component relatively normally, in both rows. -/
theorem firstFlagCore_baumann_ms1
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    let B := ChapterB.baumann (firstFlagCore h structural D m)
    let J := L ⊔ B
    IsSQTK KnownSimple.IsKnownSimple J ∧
      generalizedFitting J = pCore 2 J ∧
      (∀ j ∈ J, ∃ l ∈ L, ∃ b ∈ B, l*b=j) ∧
      (L.subgroupOf J).IsCComponent := by
  let X := L ⊔ (T : Subgroup G)
  let R := firstFlagCore h structural D m
  let B := ChapterB.baumann R
  let J := L ⊔ B
  have hRT : R ≤ T := map_subtype_le _
  have hJX : J ≤ X := sup_le le_sup_left
    ((inf_le_left : B ≤ R).trans (hRT.trans le_sup_right))
  have hXN : X ≤ normalizer (L : Set G) := sup_le L.le_normalizer D.sylow_normalizes_component
  have hTNB : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    (sylow_normalizes_firstFlagCore h structural D m).trans (normalizer_le_normalizer_baumann R)
  have hXNJ : X ≤ normalizer (J : Set G) :=
    sup_le (le_sup_left.trans J.le_normalizer)
      ((le_inf D.sylow_normalizes_component hTNB).trans
        (normalizer_inf_normalizer_le_normalizer_sup L B))
  let Ji := J.subgroupOf X
  let : Ji.Normal := normal_subgroupOf_of_le_normalizer hXNJ
  let ej : Ji ≃* J := subgroupOfEquivOfLe hJX
  have hcX : HasCharacteristicTwo X :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)
      ⟨h.maximal_faithful.1.1.2.2,
        fun _ hx => (le_sup_right : (T : Subgroup G) ≤ X) hx⟩)
  have hc := normal_core_selfCentralizing hcX Ji
  have hcJ : centralizer (pCore 2 J : Set J) ≤ pCore 2 J :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 ej).mp hc
  have hfit := generalizedFitting_eq_pCore_of_selfCentralizing 2 hcJ
  have hs := h.source_normalizer_sqtk_at (fun L h => structural G T L h)
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

/-- The full-image source construction gives the genuine covered MS pair
on L Baum(R₁), with no supplied radical, kernel or characteristic premise. -/
theorem covered_firstFlagCore_smallMSPair_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hescape : ¬ normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G)) :
    SmallMSPair KnownSimple.IsKnownSimple L (ChapterB.baumann (firstFlagCore h structural D m)) := by
  obtain ⟨hs,hf,hp,hcmp⟩ := firstFlagCore_baumann_ms1 h structural D m
  obtain ⟨hr,hn⟩ := covered_firstFlagCore_ms_conditions_of_escape h structural D m hc z hzT hzL hescape
  refine ⟨inferInstance,hs,hf,hp,hcmp,?_,msOddIndex_of_intrinsic hr,
    msCharacteristic_of_intrinsic hn⟩
  exact Or.inr (Or.inl ⟨m.quotient.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)).symm⟩)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
