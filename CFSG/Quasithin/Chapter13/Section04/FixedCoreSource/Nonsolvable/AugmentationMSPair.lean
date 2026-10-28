module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationMS
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.RankTwoReconstruction
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# All MS hypotheses on the original augmentation Baumann product

For R = O₂(L₁T), B = Baum(R), the literal product J = LB is normal in LT.
The faithful augmentation action identifies C_J(V) with O₂(J), proving
F*(J) = O₂(J). The original local SQTK and component hypotheses restrict
to J. The marking of L/O₂,Z(L) gives the actual Sp₄(2)′ quotient.

In the doubled-component branch, the previously proved full-image and
kernel-saturation argument supplies MS2(a) and MS3. Transporting their
subgroups through the actual inclusions constructs the SmallMSPair used
by the existing whole-core reconstruction. The radical remains the
proper odd-index subgroup's two-core; it is not assumed to be Sylow.

AugmentationDoubledExclusion applies this result to the original chief-factor
contradiction. Natural large-distance exhaustion remains an independent
source input, owned by qt-e-ms-small-a6-exhaustion-large-distance. Final
13.4.10–17 assembly remains with qt-d-1341-nonsolvable-source and still
requires universal nonsolvability at both escaping weights.

Source: Aschbacher–Smith C.1.31–32, pp.135–136;
13.2.2(7), pp.877–878, and 13.4.10(4), p.909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The product, characteristic-two, SQTK and relative component clauses of MS1
on the original augmentation Baumann product. -/
theorem ordinary_augmentation_baumann_ms1
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    (sup_le D.normalizes ((structural G T L h).2.2 V D).1)
  obtain ⟨q,hq,_,_,hk⟩ := exists_core_product_permutation D m h structural eL
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
  have hs := h.source_normalizer_sqtk structural
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
theorem ordinary_augmentation_smallMSPair_of_ms_conditions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
  obtain ⟨hs,hf,hp,hc⟩ := ordinary_augmentation_baumann_ms1 h structural D m eL z hzT hzL
  obtain ⟨hr,hn⟩ := hms
  refine ⟨inferInstance,hs,hf,hp,hc,?_,msOddIndex_of_intrinsic hr,
    msCharacteristic_of_intrinsic hn⟩
  exact Or.inr (Or.inl ⟨m.quotient.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)).symm⟩)

/-- All MS clauses on the literal original L and point-radical Baumann subgroup,
with the rank-two quotient supplied by the original augmentation marking. -/
theorem ordinary_doubled_smallMSPair
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
    SmallMSPair KnownSimple.IsKnownSimple L (ChapterB.baumann R) := by
  exact ordinary_augmentation_smallMSPair_of_ms_conditions h structural D m eL z hzT hzL
    (ordinary_doubled_ms_conditions h₀ h structural D m eL z hzT hzL
      hKz hHN hTK hKM eK e he)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
