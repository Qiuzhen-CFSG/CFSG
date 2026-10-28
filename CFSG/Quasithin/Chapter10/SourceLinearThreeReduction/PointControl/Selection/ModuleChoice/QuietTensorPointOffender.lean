module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorPointCore
public import CFSG.Quasithin.ChapterG.Section02.CentralClosureConsequences
public import Theory.Representation.BinaryConjugationSection.Descent
public import Theory.Representation.BinaryConjugationSection.DualOffenderIndex
public import Theory.ElementaryAbelian.Injective

/-!
# The actual dual offender in the tensor point-core argument

Assume the original full module V is not contained in Q=O₂(C_G(z)).
The previous irreducible-interval argument identifies V intersect Q with
V₅. Its full point-centralizer closure U lies in Q and in the original
Sylow, so [U,V] lies in V₅ and [U,V,V]=1. Both V's image modulo Q and
V₅ modulo the original point have order sixteen.

G.2.2 kills the entire Q-action on U/⟨z⟩, constructing a representation
of the literal C_G(z)/Q with the original quotient coordinates. The
commutator bound then gives its quadratic dual offender. The V-image is
contained and normal in the original XT image. No faithfulness or
natural-module coordinates on this new section are assumed.

This proves the dual-offender reduction of 8.3.12. Identifying the actor
as a Sylow subgroup, bounding the section by two conjugate four-spaces,
and the final module contradiction remain with the source assembly.
Source: Aschbacher--Smith 8.3.12, printed p.726, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 Chapter8.Section03 Chapter1 BinaryTensorThree
variable {G : Type*} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private theorem fullModule_normalized_by_sylow :
    (T : Subgroup G) ≤ normalizer (D.fullModule : Set G) :=
  (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule

private theorem fullModule_card (b : Additive D.fullModule ≃ₗ[ZMod 2] Space) :
    Nat.card D.fullModule = 512 := by
  rw [show Nat.card D.fullModule = Nat.card (Additive D.fullModule) from rfl,
    Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,b.finrank_eq,
    Module.finrank_matrix]
  norm_num

private theorem five_card (b : Additive D.fullModule ≃ₗ[ZMod 2] Space) :
    Nat.card (quietTensorFive D b) = 32 := by
  let : IsElementaryAbelian 2 (quietTensorFive D b) := IsElementaryAbelian.of_le (quietTensorFive_le D b)
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 (quietTensorFive D b)).exists_card_eq
  have hr := quietTensorFive_rank D b
  rw [rank,hn,Nat.log_pow Nat.one_lt_two] at hr
  simpa [hr] using hn

private theorem image_card_mul {H E : Type*} [Group H] [Finite H] [Group E]
    (f : H →* E) (A : Subgroup H) :
    Nat.card (A.map f) * Nat.card (A ⊓ f.ker : Subgroup H) = Nat.card A := by
  let g := f.comp A.subtype
  have hr : g.range = A.map f := by rw [MonoidHom.range_comp,range_subtype]
  let c : g.ker ≃ (A ⊓ f.ker : Subgroup H) :=
    { toFun := fun x => ⟨x.val.val,x.val.property,x.property⟩
      invFun := fun x => ⟨⟨x.val,x.property.1⟩,x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [←hr,←Nat.card_congr c,←index_ker,index_mul_card]

variable (q : localJoin T L →* PointParabolic.Actor) (hq : Function.Surjective q)
  (b : Additive D.fullModule ≃ₗ[ZMod 2] Space)
  (hb : ∀ (a : localJoin T L) (v : Additive D.fullModule),
    quietTensorLinearAction D b a (b v) = action (PointParabolic.tensorHom (q a)) (b v))
  {z : G} (hzV : z ∈ D.fullModule)
  (hbz : b (Additive.ofMul ⟨z,hzV⟩) = point)
  (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
  (hz1 : z ≠ 1)

include hq hb hbz hzT hz1 in
/-- In the contrary branch, the closure's displacement by V lies in the literal five-space. -/
theorem quiet_tensor_point_closure_commutator
    (hcore : ¬ D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2) :
    ⁅(quietTensorPointFlagSetup D b z).U,D.fullModule⁆ ≤ quietTensorFive D b := by
  let s := quietTensorPointFlagSetup D b z
  have hs := quiet_tensor_point_flag_hypothesis D q hq b hb hzV hbz hzT hz1
  have hUQ := hs.U_le_core
  have hUT := hs.U_normal_in_T.1
  have hV : ⁅s.U,D.fullModule⁆ ≤ D.fullModule :=
    le_normalizer_iff_commutator_le_right.mp
      (hUT.trans (fullModule_normalized_by_sylow D))
  have hQN : s.H ≤ normalizer (s.QH : Set G) := by
    simpa only [ChapterG.Section02.Setup.QH,pCoreIn,normalizer_eq_top,
      ←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 s.H).le_normalizer_map s.H.subtype
  have hVH : D.fullModule ≤ s.H :=
    (D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)).trans hzT
  have hQ : ⁅s.U,D.fullModule⁆ ≤ s.QH :=
    (commutator_mono hUQ le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hVH.trans hQN))
  exact (le_inf hV hQ).trans
    (quiet_tensor_point_core_intersection D q hq b hb hzV hbz hzT hz1 hcore).le

include hq hb hbz hzT hz1 in
/-- The original actor V is quadratic on the full closure, even before quotienting by z. -/
theorem quiet_tensor_point_closure_quadratic
    (hcore : ¬ D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2) :
    ⁅⁅(quietTensorPointFlagSetup D b z).U,D.fullModule⁆,D.fullModule⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact (quiet_tensor_point_closure_commutator D q hq b hb hzV hbz hzT hz1 hcore).trans
    ((quietTensorFive_le D b).trans (Subgroup.le_centralizer (H := D.fullModule)))

include hq hb hbz hzT hz1 in
/-- The literal image of V in G_z/O₂(G_z) has order sixteen in the contrary branch. -/
theorem quiet_tensor_point_core_image_card
    (hcore : ¬ D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2) :
    Nat.card ((D.fullModule.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) = 16 := by
  let H := centralizer ({z} : Set G)
  let f := QuotientGroup.mk' (pCore 2 H)
  have hVH : D.fullModule ≤ H :=
    (D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)).trans hzT
  have hQ : ((H.pCoreIn 2).subgroupOf H) = pCore 2 H :=
    comap_map_eq_self_of_injective H.subtype_injective _
  have he : D.fullModule.subgroupOf H ⊓ f.ker = (quietTensorFive D b).subgroupOf H := by
    rw [QuotientGroup.ker_mk',←hQ]
    change (D.fullModule ⊓ H.pCoreIn 2).subgroupOf H = _
    exact congrArg (fun A : Subgroup G => A.subgroupOf H)
      (quiet_tensor_point_core_intersection D q hq b hb hzV hbz hzT hz1 hcore)
  have hc := image_card_mul f (D.fullModule.subgroupOf H)
  rw [he,Nat.card_congr (subgroupOfEquivOfLe ((quietTensorFive_le D b).trans hVH)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv,five_card D b,fullModule_card D b] at hc
  change Nat.card ((D.fullModule.subgroupOf H).map f) = 16
  omega

include hq hb hbz hzT hz1 in
/-- The five-space modulo the actual fixed point has order sixteen. -/
theorem quiet_tensor_point_tilde_five_card :
    let s := quietTensorPointFlagSetup D b z
    Nat.card (s.tilde (quietTensorFive D b)) = 16 := by
  let s := quietTensorPointFlagSetup D b z
  have hs := quiet_tensor_point_flag_hypothesis D q hq b hb hzV hbz hzT hz1
  let f := QuotientGroup.mk' (s.V₁.subgroupOf s.G₁)
  have h5G : quietTensorFive D b ≤ s.G₁ :=
    (le_conjugateSpanBy _ _).trans (hs.U_le_H.trans hs.H_le)
  have hzG : zpowers z ≤ s.G₁ := s.V₁.le_normalizer
  have he : (quietTensorFive D b).subgroupOf s.G₁ ⊓ f.ker = s.V₁.subgroupOf s.G₁ := by
    rw [QuotientGroup.ker_mk']
    exact inf_eq_right.mpr (subgroupOf_mono _ hs.point_le)
  have hc := image_card_mul f ((quietTensorFive D b).subgroupOf s.G₁)
  have hzcard : Nat.card (s.V₁.subgroupOf s.G₁) = 2 := by
    change Nat.card ((zpowers z).subgroupOf s.G₁) = 2
    rw [Nat.card_congr (subgroupOfEquivOfLe hzG).toEquiv,Nat.card_zpowers]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  rw [he,hzcard,Nat.card_congr (subgroupOfEquivOfLe h5G).toEquiv,five_card D b] at hc
  change Nat.card (((quietTensorFive D b).subgroupOf s.G₁).map f) = 16
  omega


include hzT in
/-- The original image of V is normal in the image of XT, the original Borel.
This is relative normality in that subgroup, not normality in the point centralizer. -/
theorem quiet_tensor_point_image_borel_normal :
    let H := centralizer ({z} : Set G)
    let π := QuotientGroup.mk' (pCore 2 H)
    let A := (D.fullModule.subgroupOf H).map π
    let B := ((CentralizerSetup.XT ⟨T,localOrbit T L,z⟩).subgroupOf H).map π
    A ≤ B ∧ (A.subgroupOf B).Normal := by
  dsimp only
  let H := centralizer ({z} : Set G)
  let π := QuotientGroup.mk' (pCore 2 H)
  let X := CentralizerSetup.XT ⟨T,localOrbit T L,z⟩
  have hVH : D.fullModule ≤ H :=
    (D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)).trans hzT
  have hX : X ≤ normalizer (D.fullModule : Set G) := by
    change CentralizerSetup.XT ⟨T,localOrbit T L,z⟩ ≤ _
    rw [quiet_XT_eq_point_centralizer (T := T) (L := L) hzT]
    exact inf_le_left.trans
      ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)).trans
        D.maximalLocal_normalizes_fullModule)
  have hn : X.subgroupOf H ≤ normalizer (D.fullModule.subgroupOf H : Set H) := by
    rw [←subgroupOf_normalizer_eq hVH]
    exact subgroupOf_mono _ hX
  have hVX : D.fullModule ≤ X :=
    (D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)).trans le_sup_right
  exact ⟨map_mono (subgroupOf_mono _ hVX),normal_subgroupOf_of_le_normalizer
    ((map_mono (f := π) hn).trans (le_normalizer_map π))⟩

include hq hb hbz hzT hz1 in
/-- The intrinsic closure/point quotient is elementary, by its injective tilde marking. -/
theorem quiet_tensor_point_closure_quotient_elementary
    [((zpowers z).subgroupOf (quietTensorPointFlagSetup D b z).U).Normal] :
    IsElementaryAbelian 2 ((quietTensorPointFlagSetup D b z).U ⧸
      (zpowers z).subgroupOf (quietTensorPointFlagSetup D b z).U) := by
  let s := quietTensorPointFlagSetup D b z
  have hs := quiet_tensor_point_flag_hypothesis D q hq b hb hzV hbz hzT hz1
  have hUG := hs.U_le_H.trans hs.H_le
  let f := (QuotientGroup.mk' (s.V₁.subgroupOf s.G₁)).comp (inclusion hUG)
  have hk : f.ker = (zpowers z).subgroupOf s.U := by
    ext u
    exact QuotientGroup.eq_one_iff (N := s.V₁.subgroupOf s.G₁) (inclusion hUG u)
  have hr : f.range = s.tilde s.U := by
    rw [MonoidHom.range_comp]
    have hi : (inclusion hUG).range = s.U.subgroupOf s.G₁ := by
      ext u
      exact ⟨fun ⟨v,he⟩ => he ▸ v.property,fun hu => ⟨⟨u,hu⟩,rfl⟩⟩
    rw [hi]
    rfl
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  let : IsElementaryAbelian 2 f.range := hr.symm ▸ hs.tilde_U_elementary
  exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective

include hq hb hbz hzT hz1 in
/-- The original contrary branch constructs its actual dual FF module and quadratic
order-sixteen offender, retaining the point denominator and the full two-core. -/
theorem quiet_tensor_point_dual_offender
    [((zpowers z).subgroupOf (quietTensorPointFlagSetup D b z).U).Normal]
    (hcore : ¬ D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2) :
    let s := quietTensorPointFlagSetup D b z
    let := quiet_tensor_point_closure_quotient_elementary D q hq b hb hzV hbz hzT hz1
    let π := QuotientGroup.mk' (pCore 2 s.H)
    let A := (D.fullModule.subgroupOf s.H).map π
    ∃ (σ : Representation (ZMod 2) (s.H ⧸ pCore 2 s.H)
        (Additive (s.U ⧸ (zpowers z).subgroupOf s.U)))
      (c : Representation.BinaryConjugationSection s.H s.U (zpowers z) (σ.comp π)),
      (∀ u : s.U, (c.coordinates u).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((zpowers z).subgroupOf s.U) u)) ∧
      Nat.card A = 16 ∧ IsOffender σ.dual A ∧ IsQuadratic σ A := by
  dsimp only
  let s := quietTensorPointFlagSetup D b z
  have hs := quiet_tensor_point_flag_hypothesis D q hq b hb hzV hbz hzT hz1
  let := quiet_tensor_point_closure_quotient_elementary D q hq b hb hzV hbz hzT hz1
  let π := QuotientGroup.mk' (pCore 2 s.H)
  let A := (D.fullModule.subgroupOf s.H).map π
  have hk (a : s.H) (ha : π a = 1) (u : G) (hu : u ∈ s.U) :
      ⁅(a : G),u⁆ ∈ zpowers z := by
    have haQ : (a : G) ∈ s.QH :=
      mem_map_of_mem s.H.subtype ((QuotientGroup.eq_one_iff a).mp ha)
    have hc := hs.commutator_U_core_le_point
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator haQ hu)
  obtain ⟨σ,c,hc⟩ := Representation.BinaryConjugationSection.exists_descended_actor
    s.H s.U (zpowers z) hs.U_le_H (hs.point_le.trans (le_conjugateSpanBy _ _))
    (le_normalizer_conjugateSpanBy _ _) hs.H_le π (QuotientGroup.mk'_surjective _) hk
  have hcA : Nat.card A = 16 :=
    quiet_tensor_point_core_image_card D q hq b hb hzV hbz hzT hz1 hcore
  have hVH : D.fullModule ≤ s.H :=
    (D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)).trans hzT
  have hEA : IsElementaryTwo A := by
    refine ⟨fun he => ?_,?_⟩
    · rw [he,card_bot] at hcA
      norm_num at hcA
    · let : IsElementaryAbelian 2 (D.fullModule.subgroupOf s.H) :=
        IsElementaryAbelian.subgroupOf hVH
      exact IsElementaryAbelian.map _
  have h5U : quietTensorFive D b ≤ s.U := le_conjugateSpanBy _ _
  have hindex : (zpowers z).relIndex (quietTensorFive D b) = 16 := by
    have ht := relIndex_mul_relIndex (⊥ : Subgroup G) (zpowers z) (quietTensorFive D b)
      bot_le hs.point_le
    have hzcard : Nat.card (zpowers z) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
    simp only [relIndex_bot_left,hzcard,five_card D b] at ht
    omega
  have hm : ⁅D.fullModule,s.U⁆ ≤ quietTensorFive D b := by
    rw [commutator_comm]
    exact quiet_tensor_point_closure_commutator D q hq b hb hzV hbz hzT hz1 hcore
  have hf : ⁅D.fullModule,quietTensorFive D b⁆ ≤ zpowers z := by
    have hh : ⁅D.fullModule,quietTensorFive D b⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        (centralizer_le (quietTensorFive_le D b) |>.trans' (Subgroup.le_centralizer (H := D.fullModule)))
    exact hh.le.trans bot_le
  exact ⟨σ,c,hc,hcA,
    Representation.BinaryConjugationSection.dual_offender_of_commutator_index σ π c D.fullModule (quietTensorFive D b) h5U hm hEA
      (by rw [hindex,hcA]),
    Representation.BinaryConjugationSection.quadratic_of_commutator_bounds σ π c D.fullModule (quietTensorFive D b) hm hf⟩

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
