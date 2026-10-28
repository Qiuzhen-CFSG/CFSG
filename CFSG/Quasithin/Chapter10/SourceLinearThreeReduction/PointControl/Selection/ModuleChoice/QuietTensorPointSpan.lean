module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorPointSylow
public import Theory.GroupTheory.ConjugateSpanTwoCoreGenerators
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.Representation.BinaryConjugationSection.OffenderIndex

/-!
# The two-conjugate dimension bound in the tensor point-core argument

The full point-core kernel moves the original closure only into the fixed
point line. Together with the two quotient generators and the original
V-displacement bound, this makes the closure the join of two conjugate
five-spaces. Their intersection contains that same fixed line, so the
closure has order at most 512, and its literal quotient by the line has
binary dimension at most eight. The fixed five-space then makes the same
actor an offender on the section itself. No natural-module recognition
is assumed.
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

variable (q : localJoin T L →* PointParabolic.Actor) (hq : Function.Surjective q)
  (b : Additive D.fullModule ≃ₗ[ZMod 2] Space)
  (hb : ∀ (a : localJoin T L) (v : Additive D.fullModule),
    quietTensorLinearAction D b a (b v) = action (PointParabolic.tensorHom (q a)) (b v))
  {z : G} (hzV : z ∈ D.fullModule)
  (hbz : b (Additive.ofMul ⟨z,hzV⟩) = point)
  (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
  (hz1 : z ≠ 1)

include hq hb hbz hzT hz1 in
/-- The actual closure is the join of the two original conjugate five-spaces. -/
theorem quiet_tensor_point_closure_two_spaces
    (hcore : ¬ D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (hspan : (quietTensorPointFlagSetup D b z).U = conjugateSpanBy (quietTensorFive D b)
      (CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩))
    (k : CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩)
    (hgen : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      let π := QuotientGroup.mk' (pCore 2 d.Gz)
      let A := (D.fullModule.subgroupOf d.Gz).map π
      A ⊔ A.map (MulAut.conj (π (inclusion d.Kz_le_Gz k))).toMonoidHom =
        (d.Kz.subgroupOf d.Gz).map π) :
    (quietTensorPointFlagSetup D b z).U = quietTensorFive D b ⊔ (quietTensorFive D b).conjBy k := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let s := quietTensorPointFlagSetup D b z
  have hs := quiet_tensor_point_flag_hypothesis D q hq b hb hzV hbz hzT hz1
  exact conjugateSpan_eq_two_conjugates_mod_twoCore d.Gz d.Kz s.U D.fullModule
    (quietTensorFive D b) (zpowers z) d.Kz_le_Gz (le_normalizer_conjugateSpanBy _ _)
    hs.point_le (le_conjugateSpanBy _ _)
    (quiet_tensor_point_closure_commutator D q hq b hb hzV hbz hzT hz1 hcore)
    hs.commutator_U_core_le_point hspan k hgen.ge

private theorem five_card : Nat.card (quietTensorFive D b) = 32 := by
  let : IsElementaryAbelian 2 (quietTensorFive D b) := IsElementaryAbelian.of_le (quietTensorFive_le D b)
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 (quietTensorFive D b)).exists_card_eq
  have hr := quietTensorFive_rank D b
  rw [rank,hn,Nat.log_pow Nat.one_lt_two] at hr
  simpa [hr] using hn

include hq hb hbz hzT hz1 in
/-- The common fixed line lowers the order bound from 1024 to 512. -/
theorem quiet_tensor_point_closure_card_le
    (k : CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩)
    (hspan : (quietTensorPointFlagSetup D b z).U =
      quietTensorFive D b ⊔ (quietTensorFive D b).conjBy k) :
    Nat.card (quietTensorPointFlagSetup D b z).U ≤ 512 := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let s := quietTensorPointFlagSetup D b z
  let E := quietTensorFive D b
  let B := E.conjBy (k : G)
  have hs := quiet_tensor_point_flag_hypothesis D q hq b hb hzV hbz hzT hz1
  have hEU : E ≤ s.U := le_conjugateSpanBy _ _
  have hkU : s.U.map (MulAut.conj (k : G)).toMonoidHom = s.U :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy _ _ (d.Kz_le_Gz k.property))
  have hBU : B ≤ s.U := (map_mono hEU).trans hkU.le
  have hcomm : ⁅s.U,s.U⁆ ≤ zpowers z :=
    (commutator_mono le_rfl hs.U_le_core).trans hs.commutator_U_core_le_point
  have hBN : B ≤ normalizer (E : Set G) := le_normalizer_iff_commutator_le_left.mpr
    (((commutator_mono hEU hBU).trans hcomm).trans hs.point_le)
  have hZk : (zpowers z).map (MulAut.conj (k : G)).toMonoidHom = zpowers z :=
    mem_normalizer_iff_map_conj_eq.mp (hs.H_le (d.Kz_le_Gz k.property))
  have hZB : zpowers z ≤ B := hZk ▸ map_mono (f := (MulAut.conj (k : G)).toMonoidHom) hs.point_le
  have hZcard : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  have hI : 2 ≤ Nat.card (E ⊓ B : Subgroup G) :=
    hZcard ▸ card_le_of_le (le_inf hs.point_le hZB)
  have hEcard : Nat.card E = 32 := five_card D b
  have hBcard : Nat.card B = 32 := (card_map_of_injective (MulAut.conj (k : G)).injective).trans hEcard
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes E B hBN
  rw [hEcard,hBcard,←hspan] at hc
  have hi := Nat.mul_le_mul_right (Nat.card s.U) hI
  change Nat.card s.U ≤ 512
  nlinarith

include hq hb hbz hzT hz1 in
/-- The literal U/⟨z⟩, with its canonical binary structure, has dimension at most eight. -/
theorem quiet_tensor_point_section_dimension_le_eight
    [((zpowers z).subgroupOf (quietTensorPointFlagSetup D b z).U).Normal]
    (hc : Nat.card (quietTensorPointFlagSetup D b z).U ≤ 512) :
    let s := quietTensorPointFlagSetup D b z
    let := quiet_tensor_point_closure_quotient_elementary D q hq b hb hzV hbz hzT hz1
    Module.finrank (ZMod 2) (Additive (s.U ⧸ (zpowers z).subgroupOf s.U)) ≤ 8 := by
  dsimp only
  let s := quietTensorPointFlagSetup D b z
  let := quiet_tensor_point_closure_quotient_elementary D q hq b hb hzV hbz hzT hz1
  have hs := quiet_tensor_point_flag_hypothesis D q hq b hb hzV hbz hzT hz1
  have hzU : zpowers z ≤ s.U := hs.point_le.trans (le_conjugateSpanBy _ _)
  have hZcard : Nat.card ((zpowers z).subgroupOf s.U) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hzU).toEquiv,Nat.card_zpowers]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  have he := ((zpowers z).subgroupOf s.U).card_mul_index
  rw [hZcard,index_eq_card] at he
  have hqcard : Nat.card (Additive (s.U ⧸ (zpowers z).subgroupOf s.U)) ≤ 256 := by
    change Nat.card (s.U ⧸ (zpowers z).subgroupOf s.U) ≤ 256
    change Nat.card s.U ≤ 512 at hc
    omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hqcard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hqcard

include hq hb hbz hzT hz1 in
/-- The same original actor is now an offender on the section itself, as well as its dual. -/
theorem quiet_tensor_point_full_offender
    (hcore : ¬ D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2)
      ((quietTensorPointFlagSetup D b z).H ⧸ pCore 2 (quietTensorPointFlagSetup D b z).H) W)
    (c : Representation.BinaryConjugationSection (quietTensorPointFlagSetup D b z).H
      (quietTensorPointFlagSetup D b z).U (zpowers z)
      (σ.comp (QuotientGroup.mk' (pCore 2 (quietTensorPointFlagSetup D b z).H))))
    (hc : Nat.card (quietTensorPointFlagSetup D b z).U ≤ 512) :
    IsOffender σ ((D.fullModule.subgroupOf (quietTensorPointFlagSetup D b z).H).map
      (QuotientGroup.mk' (pCore 2 (quietTensorPointFlagSetup D b z).H))) := by
  let s := quietTensorPointFlagSetup D b z
  let π := QuotientGroup.mk' (pCore 2 s.H)
  let A := (D.fullModule.subgroupOf s.H).map π
  have hs := quiet_tensor_point_flag_hypothesis D q hq b hb hzV hbz hzT hz1
  have hEU : quietTensorFive D b ≤ s.U := le_conjugateSpanBy _ _
  have hAcard : Nat.card A = 16 :=
    quiet_tensor_point_core_image_card D q hq b hb hzV hbz hzT hz1 hcore
  have hEA : IsElementaryTwo A := by
    refine ⟨fun he => ?_,?_⟩
    · rw [he,card_bot] at hAcard
      norm_num at hAcard
    · let : IsElementaryAbelian 2 (D.fullModule.subgroupOf s.H) :=
        IsElementaryAbelian.subgroupOf
          ((D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)).trans hzT)
      exact IsElementaryAbelian.map π
  have hi : (quietTensorFive D b).relIndex s.U ≤ Nat.card A := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (quietTensorFive D b) s.U bot_le hEU
    simp only [relIndex_bot_left,five_card D b] at hh
    rw [hAcard]
    change Nat.card s.U ≤ 512 at hc
    omega
  have hcomm : ⁅D.fullModule,quietTensorFive D b⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      ((Subgroup.le_centralizer (H := D.fullModule)).trans (centralizer_le (quietTensorFive_le D b)))
  exact Representation.BinaryConjugationSection.offender_of_fixed_index σ π c D.fullModule
    (quietTensorFive D b) hEU hs.point_le hcomm hEA hi

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
