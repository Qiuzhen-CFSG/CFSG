module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryAugmentationAt
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs
public import Theory.GroupTheory.SylowNormalRestriction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.RankTwoReconstruction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Recognition.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.Application
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.Complete.Source
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.A6Irreducibility

/-!
# The actual ordinary Baumann alternative with local earlier inputs

In the full-image case, kernel saturation identifies the proper odd-index
radical in L Baum(R), and ambient uniqueness excludes a nontrivial normal
characteristic subgroup of Baum(R). The same product has characteristic
two and inherits the SQTK and component clauses. This constructs every
SmallMSPair hypothesis on the original subgroups. Natural reconstruction
then gives shortness, completing the alternative with the small images.

Every structural call is guarded by Hypothesis1223 at the same G,T.
The independent Natural.Exhaustion.LargeDistanceInput remains explicit;
it is used for the actual ordinary quotient, never a covered quotient.
OrdinaryFusionAt applies the alternative to control the Sylow normalizer.
The existing universal augmentation and reconstruction APIs are preserved.

Source: Aschbacher--Smith C.1.31--32, C.1.37 and 13.2.2(7),
printed pp.135--136,142--143,878.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable Solvable
open Section08.TransvectionRecognition.Component.ModelExtension
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Theory.SpecificGroups.SymmetricSix.BinaryFlags (pointCore)
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Full point images and Baumann-normalizer escape supply MS2(a) and MS3
for the original augmentation product, independently of a component row. -/
theorem ordinary_augmentation_full_ms_conditions_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom
        ⟨x.val,(sup_le D.normalizes ((structural L h).2.2 V D).1) x.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd)
    (hfull : let X := L ⊔ (T : Subgroup G)
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    Function.Surjective q ∧ ∃ a : alternatingGroup (Fin 6),
      ((elementaryAbelianMaxJ R).subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
      ((ChapterB.baumann R).subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
      (R.subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom)
    (hescape : let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
      ¬ normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G)) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    let B := ChapterB.baumann R
    ChapterC.MSOddIndexRadical (B.subgroupOf (L ⊔ B)) ∧
      ChapterC.MSCharacteristicCondition (B.subgroupOf (L ⊔ B)) := by
  have hBker := (ordinary_augmentation_full_baumann_kernel_at
    h structural D m eL z hzT hzL q hq hfull).2
  obtain ⟨_,a,_,hBfull,hRfull⟩ := hfull
  let X := L ⊔ (T : Subgroup G)
  let P := Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  let B := ChapterB.baumann R
  let J := L ⊔ B
  let PJ := P.subgroupOf J
  let BJ := B.subgroupOf J
  have hPX : P ≤ X :=
    (ordinary_augmentation_point_parabolic D m eL z hzT hzL).le.trans inf_le_left
  have hRX : R ≤ X := (pCoreIn_le 2 P).trans hPX
  have hBR : B ≤ R := inf_le_left
  have hBP : B ≤ P := hBR.trans (pCoreIn_le 2 P)
  have hBX : B ≤ X := hBP.trans hPX
  have hJX : J ≤ X := sup_le le_sup_left hBX
  have hXN : X ≤ normalizer (L : Set G) := sup_le L.le_normalizer D.sylow_normalizes_component
  have hPNB : P ≤ normalizer (B : Set G) :=
    (P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))).trans
      (normalizer_le_normalizer_baumann R)
  have hPNJ : P ≤ normalizer (J : Set G) :=
    (le_inf (hPX.trans hXN) hPNB).trans (normalizer_inf_normalizer_le_normalizer_sup L B)
  have hTNJ : (T : Subgroup G) ≤ normalizer (J : Set G) := le_sup_right.trans hPNJ
  have hXNJ : X ≤ normalizer (J : Set G) :=
    sup_le (le_sup_left.trans J.le_normalizer) hTNJ
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  let Ui := V.subgroupOf X
  let : Ui.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.normalizes (((structural L h).2.2 V D).1))
  let eu : Ui ≃* V := subgroupOfEquivOfLe hVX
  let ei := eu.trans m.coordinate
  have hei (x : X) (v : Ui) : (ei (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (ei v).toAdd := hq x (eu v)
  have hkc := ChapterB.Offenders.SixCorePoint.kernel_centralizer Ui q ei hei
  have hRBJ : R ⊓ J = B := by
    apply le_antisymm
    · intro r hr
      have hqr : q ⟨r,hRX hr.1⟩ ∈ (B.subgroupOf X).map q := by
        rw [hBfull,←hRfull]
        exact mem_map_of_mem q hr.1
      obtain ⟨b,hb,hbr⟩ := hqr
      let x : X := ⟨r,hRX hr.1⟩ * b⁻¹
      have hx : x ∈ q.ker := by
        change q (⟨r,hRX hr.1⟩ * b⁻¹) = 1
        rw [map_mul,map_inv,hbr,mul_inv_cancel]
      have hc : x.val ∈ centralizer (V : Set G) := by
        rw [hkc] at hx
        intro v hv
        exact congrArg Subtype.val (hx ⟨v,hVX hv⟩ hv)
      have hj : x.val ∈ J := mul_mem hr.2 (inv_mem (mem_sup_right hb))
      have hb' : x.val ∈ B := (hBker.symm ▸ show x.val ∈ J ⊓ centralizer (V : Set G) from ⟨hj,hc⟩).1
      have hh : (r * b.val⁻¹) * b.val ∈ B := B.mul_mem hb' hb
      simpa only [inv_mul_cancel_right] using hh
    · exact le_inf hBR le_sup_right
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
    apply hzL
    have hLP : L ≤ P := le_sup_left.trans hJP
    have hLc : L ≤ centralizer ({z.val} : Set G) := hLP.trans
      ((ordinary_augmentation_point_parabolic D m eL z hzT hzL).le.trans inf_le_right)
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
    have hSP : (S : Subgroup J) ≤ PJ := fun x hx => mem_sup_right (hST (mem_map_of_mem J.subtype hx))
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
    sup_le (le_sup_left.trans hJN) (le_sup_right.trans (hPNB.trans hBN))
  have hp : IsPGroup 2 N := (((isPGroup_pCoreIn 2 P).to_le hBR).to_subgroup E).map B.subtype
  have hNM : normalizer (N : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal
      (h.source_normalizer_maximal_unique_at structural
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2 hp hNne hXN
  exact hescape (hBN.trans hNM)

/-- The product, characteristic-two, SQTK and relative component clauses of MS1
on the original augmentation Baumann product. -/
theorem ordinary_augmentation_baumann_ms1_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    let B := ChapterB.baumann R
    let J := L ⊔ B
    IsSQTK KnownSimple.IsKnownSimple J ∧
      generalizedFitting J = pCore 2 J ∧
      (∀ j ∈ J, ∃ l ∈ L, ∃ b ∈ B, l*b=j) ∧
      (L.subgroupOf J).IsCComponent := by
  let X := L ⊔ (T : Subgroup G)
  let P := Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  let B := ChapterB.baumann R
  let J := L ⊔ B
  have hPX : P ≤ X :=
    (ordinary_augmentation_point_parabolic D m eL z hzT hzL).le.trans inf_le_left
  have hBP : B ≤ P := inf_le_left.trans (pCoreIn_le 2 P)
  have hJX : J ≤ X := sup_le le_sup_left (hBP.trans hPX)
  have hXN : X ≤ normalizer (L : Set G) := sup_le L.le_normalizer D.sylow_normalizes_component
  have hPNB : P ≤ normalizer (B : Set G) :=
    (P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))).trans
      (normalizer_le_normalizer_baumann R)
  have hPNJ : P ≤ normalizer (J : Set G) :=
    (le_inf (hPX.trans hXN) hPNB).trans (normalizer_inf_normalizer_le_normalizer_sup L B)
  have hXNJ : X ≤ normalizer (J : Set G) :=
    sup_le (le_sup_left.trans J.le_normalizer) (le_sup_right.trans hPNJ)
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
  obtain ⟨q,hq,_,_,hk⟩ := exists_core_product_permutation_at D m h structural eL
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

/-- Assemble the literal MS pair from MS1 and the intrinsic MS2(a), MS3
conditions, preserving the original central quotient marking. -/
theorem ordinary_augmentation_smallMSPair_of_ms_conditions_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hms : let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
      let B := ChapterB.baumann R
      ChapterC.MSOddIndexRadical (B.subgroupOf (L ⊔ B)) ∧
        ChapterC.MSCharacteristicCondition (B.subgroupOf (L ⊔ B))) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    SmallMSPair KnownSimple.IsKnownSimple L (ChapterB.baumann R) := by
  obtain ⟨hs,hf,hp,hc⟩ := ordinary_augmentation_baumann_ms1_at h structural D m eL z hzT hzL
  obtain ⟨hr,hn⟩ := hms
  refine ⟨inferInstance,hs,hf,hp,hc,?_,msOddIndex_of_intrinsic hr,
    msCharacteristic_of_intrinsic hn⟩
  exact Or.inr (Or.inl ⟨m.quotient.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)).symm⟩)

/-- The full ordinary augmentation alternative, pending only the independent
natural large-distance theorem. It applies at either nonconstant weight. -/
theorem ordinary_augmentation_baumann_alternative_of_largeDistance_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G) ∨ ChapterC.IsShort L := by
  let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
  let B := ChapterB.baumann R
  by_cases hbound : normalizer (B : Set G) ≤ normalizer (L : Set G)
  · exact Or.inl hbound
  obtain ⟨q,hq,_,_,_⟩ := exists_core_product_permutation_at D m h structural eL
  rcases ordinary_augmentation_baumann_images_at h structural D m eL z hzT hzL q hq with hs | hf
  · exact ordinary_augmentation_small_baumann_at h structural D m eL z hzT hzL q hq hs
  have hcond := ordinary_augmentation_full_ms_conditions_at h structural D m eL z hzT hzL q hq hf hbound
  have hms : SmallMSPair KnownSimple.IsKnownSimple L B :=
    ordinary_augmentation_smallMSPair_of_ms_conditions_at h structural D m eL z hzT hzL hcond
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hh : eL x ∈ center (alternatingGroup (Fin 6)) := (centerCongr eL ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp)] at hh
    exact eL.map_eq_one_iff.mp hh
  let eA : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) := m.quotient.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)).symm
  have hn := naturalCore_of_distance_inputs initialRecognition_knownSimple hl
    DistanceTwo.distanceTwo_knownSimple
  obtain ⟨hel,hcent,hmodel⟩ := hn G L B hms eA hz
  exact Or.inr (hms.short_of_core hel hcent h.quasisimple hmodel.alternating_six_irreducible)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
