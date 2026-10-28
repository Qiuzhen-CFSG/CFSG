module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Literal MS2(a) and MS3 in the augmentation doubled-component branch

Let R = O₂(L₁T), B = Baum(R), and J = LB in the original five-dimensional
augmentation setup. Equality of the full point images, together with
Baumann kernel saturation, gives R ∩ J = B. Relative normality then identifies
O₂((L₁T) ∩ J) with B. The actual Sylow intersection supplies odd index, and
the escaping point makes this parabolic proper.

A characteristic subgroup of B normal in J is normalized by T as well,
hence by LT. The original unique-maximal-two-local bound would then force
the Baumann normalizer into N_G(L), contradicting its proved escape.
Thus both MS2(a) and MS3 hold with the literal subgroup embeddings.

This consumes the full-image and kernel calculations without a shortness,
containing-component, or four-dimensional submodule premise. Connecting
MS1 and the natural large-distance input to the existing chief-factor
exclusion is now done in AugmentationAlternative and AugmentationDoubledExclusion.
Discharge of that independent input remains part of the source assembly, as do the
other rows and comparison/commutator/graph arguments. Nonsolvability at
both escaping weights is still required for that final assembly.

Source: Aschbacher–Smith C.1.31, p.135; C.1.37, pp.142–143;
13.2.2(7), p.878; 13.4.10(4), p.909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix.BinaryFlags (pointCore)
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Full point images and Baumann-normalizer escape supply MS2(a) and MS3
for the original augmentation product, independently of a component row. -/
theorem ordinary_augmentation_full_ms_conditions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom
        ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
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
  have hBker := (ordinary_augmentation_full_baumann_kernel
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
    (sup_le D.normalizes (((structural G T L h).2.2 V D).1))
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
      (h.source_normalizer_maximal_unique structural
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2 hp hNne hXN
  exact hescape (hBN.trans hNM)

/-- The original doubled-component specialization. -/
theorem ordinary_doubled_ms_conditions
    {K : Subgroup G}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    let B := ChapterB.baumann R
    ChapterC.MSOddIndexRadical (B.subgroupOf (L ⊔ B)) ∧
      ChapterC.MSCharacteristicCondition (B.subgroupOf (L ⊔ B)) := by
  obtain ⟨q,hq,_,_,_⟩ := exists_core_product_permutation D m h structural eL
  have hf := ordinary_doubled_baumann_full_image h₀ h structural D m eL z hzT hzL
    hKz hHN hTK hKM eK e he q hq
  have hescape := (ordinary_doubled_original_baumann
    h₀ h structural D m eL z hzT hzL hKz hHN hTK hKM eK e he).2.2
  exact ordinary_augmentation_full_ms_conditions h structural D m eL z hzT hzL q hq hf hescape

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
