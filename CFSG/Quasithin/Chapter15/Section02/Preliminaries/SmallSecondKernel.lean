module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallCoreAction
public import Theory.GroupAction.RankTwoCosetGeometry.SecondBallKernel

/-!
# The original elementary span lies in the second graph kernel

Let P = Y₁(H ∩ M), and retain the literal graph with vertices P and H.
An H-normal subgroup C of T centralizing V satisfies [Y₁,C] ≤ O₂(Y₁).
The overlap normalizes both Y₁ and C, so C O₂(Y₁) is normal in P and
contained in H ∩ M. It fixes the first ball at P. Normality of C in H
then places C in the second-ball kernel at H.

Apply this first to C_H(U_H), using the exact chief-factor kernels to
place that centralizer in O₂(H), and then to the elementary span U_H.
In the S₅ row both original natural chief factors contribute, giving
|G_H^[2]| ≥ 256 on the actual graph. This supplies the lower-bound side
of the radius-two exclusion, independently of the radius-one bound 512.
The separate upper bound |G_H^[2]| ≤ 32 remains unproved. The final
source application below keeps it explicit; it does not complete 15.2.8.
The centered (5,3) recognition and marked-five wreath exclusion also
remain with their existing owners.

Source: Aschbacher--Smith 15.1.12(1--3), 15.2.6--8 and F.3.2--4,
printed pp.1090,1109--1110,270, refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizes_join_of_commutator
    (Y R C : Subgroup G) (hn : Y ≤ normalizer (R : Set G))
    (hc : ⁅Y,C⁆ ≤ R) : Y ≤ normalizer ((C ⊔ R : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro y hy x hx
  have hm : (C ⊔ R).map (MulAut.conj y).toMonoidHom ≤ C ⊔ R := by
    rw [Subgroup.map_sup]
    refine sup_le (map_le_iff_le_comap.mpr ?_) ?_
    · intro c hcC
      change y * c * y⁻¹ ∈ C ⊔ R
      have hh := (C ⊔ R).mul_mem
        ((show R ≤ C ⊔ R from le_sup_right) (hc (commutator_mem_commutator hy hcC)))
        ((show C ≤ C ⊔ R from le_sup_left) hcC)
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
    · apply map_le_iff_le_comap.mpr
      intro r hr
      exact (show R ≤ C ⊔ R from le_sup_right) (le_normalizer_iff.mp hn y hy r hr)
  exact hm (mem_map_of_mem _ hx)

private theorem overlap_normalizes_witness
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    H ⊓ M ≤ normalizer (Y₁ : Set G) := by
  have hTI : (T : Subgroup G) ≤ H ⊓ M := le_inf hH.1.1.2 h.maximal.1.2
  have hs := congrArg (Subgroup.map (H ⊓ M).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTI))
  rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTI,
    ←MonoidHom.range_eq_map,range_subtype] at hs
  rw [←hs]
  exact sup_le ((le_inf ((map_subtype_le _).trans inf_le_right)
    (h.prepared.intersection_residual H hH)).trans
      (h.centralizer_normalizes_residual_subgroup hw.le_residual hw.perfect hw.invariant))
    hw.invariant

open Subgroup.CosetGeometry.RankTwo in
private theorem central_normal_le_second_kernel
    {T : Sylow 2 G} {M Mc V Y₁ H C : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hCT : C ≤ (T : Subgroup G)) (hCV : C ≤ Subgroup.centralizer (V : Set G))
    (hHC : H ≤ normalizer (C : Set G)) :
    let F : Bool → Subgroup G := fun i => if i then H else Y₁ ⊔ (H ⊓ M)
    C ≤ ballKernel F (base F true) 2 := by
  let B := H ⊓ M
  let P := Y₁ ⊔ B
  let R := Y₁.pCoreIn 2
  let D := C ⊔ R
  let F : Bool → Subgroup G := fun i => if i then H else P
  have hCB : C ≤ B := hCT.trans (le_inf hH.1.1.2 h.maximal.1.2)
  have hYM : Y₁ ≤ M := hw.le_residual.trans
    (source_caseIIResidual_le T h.maximal.1.2 (map_subtype_le _))
  have hBN := overlap_normalizes_witness hw hH
  have hYN : Y₁ ≤ normalizer (R : Set G) := Y₁.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Y₁ (pCore 2 Y₁))
  have hRN : B ≤ normalizer (R : Set G) := hBN.trans
    (normalizer_le_normalizer_characteristic_image Y₁ (pCore 2 Y₁))
  have hRT : R ≤ (T : Subgroup G) := by
    have hn : (T : Subgroup G) ≤ normalizer (R : Set G) := hw.invariant.trans
      (normalizer_le_normalizer_characteristic_image Y₁ (pCore 2 Y₁))
    exact sup_eq_right.mp (T.is_maximal'
      ((pCore_isPGroup.map Y₁.subtype).to_sup_of_normal_left' T.isPGroup' hn) le_sup_right)
  have hcomm : ⁅Y₁,C⁆ ≤ R := by
    change ⁅Y₁,C⁆ ≤ Y₁.pCoreIn 2
    rw [←hw.centralizer]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp (hCT.trans hw.invariant))
      ((commutator_mono le_rfl hCV).trans
        (le_normalizer_iff_commutator_le_right.mp
          ((hYM.trans h.prepared.normalized).trans (normalizer_le_normalizer_centralizer V))))
  have hND : P ≤ normalizer (D : Set G) := sup_le
    (normalizes_join_of_commutator Y₁ R C hYN hcomm)
    ((le_inf (inf_le_left.trans hHC) hRN).trans
      (normalizer_inf_normalizer_le_normalizer_sup C R))
  have hDB : D ≤ B := sup_le hCB (hRT.trans (le_inf hH.1.1.2 h.maximal.1.2))
  have hDH : D ≤ H := hDB.trans inf_le_left
  have hDP : D ≤ P := hDB.trans le_sup_right
  let : (D.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hND
  have hDk : D ≤ ballKernel F (base F false) 1 := by
    have hh : D.subgroupOf P ≤ ((P ⊓ H).subgroupOf P).normalCore :=
      normal_le_normalCore.mpr (fun x hx => ⟨hDP hx,hDH hx⟩)
    have hk := base_ballKernel_one F false
    change (ballKernel F (base F false) 1).subgroupOf P =
      ((P ⊓ H).subgroupOf P).normalCore at hk
    rw [←hk] at hh
    exact fun x hx => hh (show (⟨x,hDP hx⟩ : P) ∈ D.subgroupOf P from hx)
  have hCH : C ≤ H := hCB.trans inf_le_left
  let : (C.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHC
  have hCk : C ≤ ballKernel F (base F true) 1 := by
    have hh : C.subgroupOf H ≤ ((P ⊓ H).subgroupOf H).normalCore :=
      normal_le_normalCore.mpr (fun x hx => ⟨hCB.trans le_sup_right hx,hCH hx⟩)
    have hk := base_ballKernel_one F true
    change (ballKernel F (base F true) 1).subgroupOf H =
      ((P ⊓ H).subgroupOf H).normalCore at hk
    rw [←hk] at hh
    exact fun x hx => hh (show (⟨x,hCH hx⟩ : H) ∈ C.subgroupOf H from hx)
  have hh : C.subgroupOf H ≤
      ((ballKernel F (base F false) 1 ⊓ ballKernel F (base F true) 1).subgroupOf H).normalCore :=
    normal_le_normalCore.mpr (fun x hx => ⟨hDk ((show C ≤ D from le_sup_left) hx),hCk hx⟩)
  have hk := base_ballKernel_two F true
  change (ballKernel F (base F true) 2).subgroupOf H =
    ((ballKernel F (base F false) 1 ⊓ ballKernel F (base F true) 1).subgroupOf H).normalCore at hk
  rw [←hk] at hh
  exact fun x hx => hh (show (⟨x,hCH hx⟩ : H) ∈ C.subgroupOf H from hx)

open Subgroup.CosetGeometry.RankTwo in
/-- The whole-span centralizer fixes the actual radius-two ball. The
first full parabolic is Y₁(H ∩ M), with the original overlap retained. -/
theorem SmallResidualWitness.span_centralizer_le_second_kernel
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    let F : Bool → Subgroup G := fun i => if i then H else Y₁ ⊔ (H ⊓ M)
    H ⊓ Subgroup.centralizer (conjugateSpan H V : Set G) ≤ ballKernel F (base F true) 2 := by
  let U := conjugateSpan H V
  let C := H ⊓ Subgroup.centralizer (U : Set G)
  have hCQ : C ≤ H.pCoreIn 2 := by
    intro c hc
    refine ⟨⟨c,hc.1⟩,?_,rfl⟩
    apply (h.HStar_span_centralizer_lt_core hprior hH).le
    intro u hu
    exact Subtype.ext ((hc.2) u hu)
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    rintro x ⟨y,hy,rfl⟩
    exact (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2)) hy
  have hVU : V ≤ U := by
    dsimp only [U]
    rw [UniqueFactor.conjugateSpan_eq]
    exact le_conjugateSpanBy _ _
  have hHU : H ≤ normalizer (U : Set G) := by
    dsimp only [U]
    rw [UniqueFactor.conjugateSpan_eq]
    exact le_normalizer_conjugateSpanBy _ _
  exact central_normal_le_second_kernel hw hH (hCQ.trans hQT)
    (inf_le_right.trans (centralizer_le hVU))
    ((le_inf H.le_normalizer (hHU.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf)

open Subgroup.CosetGeometry.RankTwo in
/-- The whole original elementary H-span fixes the radius-two ball.
Consequently both distinct chief factors contribute to its order. -/
theorem SmallResidualWitness.span_le_second_kernel
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    let F : Bool → Subgroup G := fun i => if i then H else Y₁ ⊔ (H ⊓ M)
    conjugateSpan H V ≤ ballKernel F (base F true) 2 := by
  let := h.prepared.elementary
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  exact (le_inf hUH (le_centralizer (conjugateSpan H V))).trans
    (hw.span_centralizer_le_second_kernel hprior hH)

open Subgroup.CosetGeometry.RankTwo in
/-- The single S₅ branch has radius-two kernel of order at least 256.
The separate upper bound remains a recognition obligation. -/
theorem SmallResidualWitness.symmetricFive_second_kernel_card
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    let F : Bool → Subgroup G := fun i => if i then H else Y₁ ⊔ (H ⊓ M)
    256 ≤ Nat.card (ballKernel F (base F true) 2) := by
  exact (h.symmetricFive_span_card hprior hH he).trans
    (card_le_of_le (hw.span_le_second_kernel hprior hH))

open Subgroup.CosetGeometry.RankTwo in
/-- The genuine radius-two upper bound would exclude S₅ on the literal
source graph. Constructing this bound is an outstanding recognition step
of qt-e-152-small-parabolic; the radius-one lower bound cannot replace it. -/
theorem SmallResidualWitness.not_symmetricFive_of_second_kernel_bound
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hbound : let F : Bool → Subgroup G := fun i => if i then H else Y₁ ⊔ (H ⊓ M)
      Nat.card (ballKernel F (base F true) 2) ≤ 32) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) := by
  intro he
  have hl := hw.symmetricFive_second_kernel_card hprior hH he
  dsimp only at hbound hl
  omega

end CFSG.Quasithin.Chapter15.Section02
