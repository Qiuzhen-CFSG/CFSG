module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineNaturalSource
public import Theory.Representation.FullLinearOuterAction.Four
public import Theory.SpecificGroups.BinaryLinear.FourOuterSylowActor
public import Theory.SpecificGroups.BinaryLinear.OrderFour

/-!
# Completing the original large exchanged constituent

The original half-degree actor equality excludes a full linear constituent.
A noncentral constituent kernel would force elementary Sylow groups in its
full linear image. For a central kernel, faithful full-linear coordinates and
the elementary outer Sylow calculation force degree four. The full-center
obstruction makes that constituent escape the marked axis, so its exchanged
pair spans the whole module. The original rank equality then bounds the actor
by order eight, contradicting the actual outer-action lower bound sixteen.

Properness now gives complementary exchanged summands and faithfulness of the
literal stabilizer on the constituent and component orbit. Its index two gives
the exact equation dim(I) = dim(N_X(I)) + 2. If the constituent is isotropic,
the same form pairs it with its literal conjugate dual and proves a faithful,
non-self-dual action. The original-flag consumer retains the nondegenerate
alternative, the original markings and every preceding source premise.

This completes the geometric input for the remaining G.11.6 recognition; it
does not assert that recognition or the full large-case exclusion. The
independent mixed-size input remains explicit. In particular, the exceptional
full GL₄(2) action is excluded using the original actor bound, not by the
invalid general outer-involution shortcut discussed in the proof basis.

Source: Aschbacher--Smith G.10.15(1)--(3), G.11.6 and 14.4.2, printed
pp.361--366,1006--1007; refs/quasithin.pdf. The full-linear arguments adapt the
existing Section03 exchanged-constituent proofs to this original rank-three
flag without importing their rank-two or Theorem E source assumptions.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedGeometry
variable {D U : Type*} [Group D] [Finite D] [AddCommGroup U]
  [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {B : LinearMap.BilinForm (ZMod 2) U}
  {v : U} {W : Submodule (ZMod 2) U} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
  (hn : ¬ Group.IsSolvable D) {C : Subgroup D} (hC : IsComponent D C)
  (hm : ⁅C,X⁆ ≠ ⊥) (S : Sylow 2 D)
  (hXS : X ≤ (S : Subgroup D)) (hSX : (S : Subgroup D) ≤ normalizer (X : Set D))
  (hind : (normalizer (C : Set D)).index ≤ 2)
  {I : Submodule (ZMod 2) U}
  (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I) (hv : v ∉ I)

include h hn hC hm S hSX hind hI in
private theorem orbitSpan_of_not_axis (haxis : ¬ I ≤ (B v).ker) :
    Homogeneous.orbitSpan ρ X I = ⊤ := by
  let O := Homogeneous.orbitSpan ρ X I
  have hHI := Homogeneous.orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus
  have hXI := Homogeneous.orbitSpan_invariant ρ X I
  have horth : B.orthogonal O = ⊥ := by
    by_contra hne
    have hvO := h.point_mem_normal_component_subspace hn hC hm S hSX hind
      (B.orthogonal O) (orthogonal_invariant ρ B h.preserves hHI)
      (orthogonal_invariant ρ B h.preserves hXI) hne
    apply haxis
    intro u hu
    exact h.alternating.isRefl u v (hvO u (Homogeneous.le_orbitSpan ρ X I hu))
  have hh := B.orthogonal_orthogonal h.nondegenerate h.alternating.isRefl O
  rw [horth,LinearMap.BilinForm.orthogonal_bot] at hh
  exact hh.symm

include h hn hC hm S hSX hind hI hv in
private theorem noncentral_not_full
    (hk : ¬ (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation.asGroupHom.ker ≤
      center (componentOrbit C ⊤)) :
    ¬ Function.Surjective
      (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation.asGroupHom := by
  intro hs
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  let R := invariantSubspace ρ H I hI.invariant
  let N := R.toRepresentation.asGroupHom.ker
  obtain ⟨x,_,hsep⟩ := h.exchanged_pair_separates hn hC hm S hSX hind hI hv
  let : IsElementaryAbelian 2 ((((S : Subgroup D).subgroupOf H) ⊓ N) : Subgroup H) :=
    ExchangedKernel.kernel_sylow_elementary ρ H X S hSX R x hsep
  have hcomp (P : Sylow 2 C) : IsElementaryAbelian 2 P :=
    ExchangedKernel.component_sylow_elementary_of_kernel hC S N hk P
  have htwo : (normalizer (C : Set D)).index = 2 := by
    have hpos := (normalizer (C : Set D)).index_ne_zero_of_finite
    have h1 : (normalizer (C : Set D)).index ≠ 1 := by
      intro he
      let : C.Normal := normalizer_eq_top_iff.mp (index_eq_one.mp he)
      have heH : H = C := le_antisymm
        (iSup_conjugates_le_of_le_normalizer C ⊤ C le_rfl (by rw [normalizer_eq_top]))
        (le_componentOrbit C ⊤)
      let : IsQuasisimple H := heH.symm ▸ hC.2
      rcases IsQuasisimple.normal_le_center_or_eq_top N with hc | ht
      · exact hk hc
      · have hf := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
          (h.irreducible_of_not_solvable hn) H hC.componentOrbit_top_ne_bot
        have hle : I ≤ fixedSpace ρ H := by
          intro u hu a
          have ha : R.toRepresentation.asGroupHom a = 1 := MonoidHom.mem_ker.mp
            (by change a ∈ N; rw [ht]; exact mem_top a)
          exact congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) I => (f.val ⟨u,hu⟩ : U)) ha
        exact hI.isIrrPlus.ne_bot ρ (bot_unique (hf ▸ hle))
    omega
  let f : H →* LinearMap.GeneralLinearGroup (ZMod 2) I := R.toRepresentation.asGroupHom
  let : Finite (LinearMap.GeneralLinearGroup (ZMod 2) I) := Finite.of_surjective f hs
  exact BinaryLinear.not_elementary_sylow_of_finrank_ge_three
    (by have := hI.isIrrPlus.finrank_gt_two ρ H; omega)
    (ExchangedOrbit.elementary_sylow_image f hs
      (ExchangedOrbit.orbit_sylow_elementary hC htwo hcomp))

include h hn hC hm S hSX hind hI hv in
private theorem full_four_not_axis
    (e : (componentOrbit C ⊤) ≃* LinearMap.GeneralLinearGroup (ZMod 2) I)
    (he : ∀ a, e a = (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation.asGroupHom a)
    (hd : finrank (ZMod 2) I = 4) : ¬ I ≤ (B v).ker := by
  intro haxis
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  obtain ⟨x,hx,_,_,_,hgeo⟩ := h.exchanged_constituent_geometry hn hC hm S hSX hind hI hv
  have haxis' : I ⊓ (B v).ker = I := inf_eq_left.mpr haxis
  dsimp only at hgeo
  rw [haxis'] at hgeo
  obtain ⟨i,hi0,_,_,hfull⟩ := hgeo
  have hxi : (x : D)⁻¹ = x := inv_eq_iff_mul_eq_one.mpr (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : D) x.property)
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
    (h.irreducible_of_not_solvable hn) H hC.componentOrbit_top_ne_bot
  have ho := hI.conjugation_not_inner ρ hfix x (by rwa [hxi])
  let a := MulAut.congr e (MulAut.conjNormal (x : D))
  have hoa : a ∉ MulAut.innerSubgroup _ := by
    intro ha
    rw [← MulAut.map_innerSubgroup_congr e] at ha
    obtain ⟨b,hb,heb⟩ := ha
    exact ho ((MulAut.congr e).injective heb ▸ hb)
  apply fullCenterOuterObstruction_four hd a hoa i (fun hz => hi0 (congrArg Subtype.val hz))
  intro f hf
  obtain ⟨y,hy⟩ := hfull.full f hf
  let y' : subspaceStabilizer ρ I := ⟨(y.val : D),y.property⟩
  have haction : (stabilizerRepresentation ρ I).asGroupHom y' =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).symm
        (BinaryLinear.transvection i f hf) := by
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).injective
    apply LinearEquiv.ext
    intro u
    apply Subtype.ext
    exact hy u
  have hcomm : Commute (y' : D) (x : D) := congrArg Subtype.val (mul_comm y.val x)
  have hf := normal_full_action_fixed_of_commute ρ H I hI.invariant e he
    (binary_full_center_eq_bot (by omega)) x y' hcomm
  rw [haction] at hf
  exact hf

include h hn hC hm S hXS hSX hind hI hv in
/-- The original half-degree actor bound excludes the full linear constituent,
including the exceptional degree-four outer action. -/
theorem not_full_linear
    (hbalance : 2 * (Group.rank X + 1) = finrank (ZMod 2) U) :
    ¬ Function.Surjective
      (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation.asGroupHom := by
  intro hs
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  let R := invariantSubspace ρ H I hI.invariant
  have hdim : 3 ≤ finrank (ZMod 2) I := by
    have := hI.isIrrPlus.finrank_gt_two ρ H
    omega
  have hk : R.toRepresentation.asGroupHom.ker ≤ center H := by
    by_contra hk
    exact noncentral_not_full h hn hC hm S hSX hind hI hv hk hs
  have hj := faithful_constituent_of_centerless_surjective ρ h.faithful
    (h.irreducible_of_not_solvable hn) H I hI.invariant (hI.isIrrPlus.ne_bot ρ)
    hs (binary_full_center_eq_bot (by omega)) hk
  let e : H ≃* LinearMap.GeneralLinearGroup (ZMod 2) I :=
    MulEquiv.ofBijective R.toRepresentation.asGroupHom ⟨hj,hs⟩
  obtain ⟨x,hx,_,_,_,_⟩ := h.exchanged_constituent_geometry hn hC hm S hSX hind hI hv
  have hxi : (x : D)⁻¹ = x := inv_eq_iff_mul_eq_one.mpr (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : D) x.property)
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
    (h.irreducible_of_not_solvable hn) H hC.componentOrbit_top_ne_bot
  have ho := hI.conjugation_not_inner ρ hfix x (by rwa [hxi])
  let a := ElementaryOuterSylowAction.of_normal_elementary H S X hXS hSX x ho
  have hd := BinaryLinear.ElementaryOuterSylow.finrank_eq_four a e hdim
  have haxis := full_four_not_axis h hn hC hm S hSX hind hI hv e (fun _ => rfl) hd
  have hspan := orbitSpan_of_not_axis h hn hC hm S hSX hind hI haxis
  obtain ⟨y,_,hpair,hdis,_,_⟩ := h.exchanged_constituent_geometry hn hC hm S hSX hind hI hv
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq I (I.map (ρ y))
  rw [hdis.eq_bot,finrank_bot,add_zero,finrank_map_action,hd,← hpair,hspan,finrank_top] at hsum
  have hr : Group.rank X = 3 := by omega
  let : CommGroup X := IsMulCommutative.instCommGroup
  have hu : Nat.card X ≤ 8 := by
    have hh := card_dvd_exponent_pow_rank' X
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 X))
    rw [hr] at hh
    exact Nat.le_of_dvd (by decide) hh
  have hl := BinaryLinear.FourOuterSylowActor.normal_elementary_outer_actor_card
    H S X hXS hSX hd e x ho
  omega

include h hn hC hm S hXS hSX hind hI hv in
/-- Properness gives spanning on the original two exchanged summands, and the
literal stabilizer acts faithfully on both the constituent and its normal actor. -/
theorem completion
    (hbalance : 2 * (Group.rank X + 1) = finrank (ZMod 2) U) :
    (¬ Function.Surjective
      (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation.asGroupHom) ∧
    Homogeneous.orbitSpan ρ X I = ⊤ ∧
    (∃ x : X, I.map (ρ x) ≠ I ∧ IsCompl I (I.map (ρ x)) ∧
      finrank (ZMod 2) U = 2 * finrank (ZMod 2) I) ∧
    let Y := (subspaceStabilizer ρ I).subgroupOf X
    (∀ y : Y, (∀ u : I, ρ ((y : X) : D) u = u) → y = 1) ∧
    (∀ y : Y, ((y : X) : D) ∈ centralizer (componentOrbit C ⊤ : Set D) → y = 1) := by
  have hp := not_full_linear h hn hC hm S hXS hSX hind hI hv hbalance
  obtain ⟨hg,hgen,hfaith,hcent⟩ := h.exchanged_constituent_completion hn hC hm S hSX hind hI hv hp
  obtain ⟨x,hx,hpair,hdis,_,_⟩ := hg
  have hcompl : IsCompl I (I.map (ρ x)) :=
    ⟨hdis,codisjoint_iff.mpr (hpair.symm.trans hgen)⟩
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq I (I.map (ρ x))
  rw [hdis.eq_bot,finrank_bot,add_zero,finrank_map_action,hcompl.sup_eq_top,finrank_top] at hsum
  exact ⟨hp,hgen,⟨x,hx,hcompl,by omega⟩,hfaith,hcent⟩

private theorem binary_card (A : Type*) [Group A] [Finite A] [IsElementaryAbelian 2 A] :
    Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) := by
  rw [Nat.card_congr Additive.ofMul]
  simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)

private theorem binary_rank (A : Type*) [Group A] [Finite A] [IsElementaryAbelian 2 A] :
    Group.rank A = finrank (ZMod 2) (Additive A) := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  apply le_antisymm (IsElementaryAbelian.rank_le_finrank (p := 2) A)
  have hc : Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [← hc]
  exact Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' A
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A)))

include h hn hC hm S hXS hSX hind hI hv in
/-- The literal index-two constituent stabilizer has the sharp degree required
by G.11.6. The equality uses the original half-degree actor balance. -/
theorem stabilizer_degree
    (hbalance : 2 * (Group.rank X + 1) = finrank (ZMod 2) U) :
    let Y := (subspaceStabilizer ρ I).subgroupOf X
    letI : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
    finrank (ZMod 2) I = finrank (ZMod 2) (Additive Y) + 2 := by
  let Y := (subspaceStabilizer ρ I).subgroupOf X
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
  obtain ⟨_,_,⟨_,_,_,hd⟩,_⟩ := completion h hn hC hm S hXS hSX hind hI hv hbalance
  obtain ⟨_,_,_,_,hindex,_⟩ := h.exchanged_constituent_geometry hn hC hm S hSX hind hI hv
  have hc := Y.card_mul_index
  rw [show Y.index = 2 from hindex,binary_card Y,binary_card X,← pow_succ] at hc
  have hr := (Nat.pow_right_injective (by decide : 2 ≤ 2)) hc
  rw [binary_rank X] at hbalance
  change finrank (ZMod 2) I = finrank (ZMod 2) (Additive Y) + 2
  omega

include h hn hC hm S hXS hSX hind hI hv in
/-- If the original constituent is isotropic, the spanning pair gives its
faithful non-self-dual action and the literal contragredient companion. -/
theorem faithful_dual_of_isotropic
    (hbalance : 2 * (Group.rank X + 1) = finrank (ZMod 2) U)
    (hiso : ∀ u ∈ I, ∀ w ∈ I, B u w = 0) :
    let H := componentOrbit C ⊤
    letI : H.Normal := componentOrbit_top_normal C
    let R := invariantSubspace ρ H I hI.invariant
    Function.Injective R.toRepresentation.asGroupHom ∧
    ¬ Nonempty (Representation.Equiv R.toRepresentation R.toRepresentation.dual) ∧
    ∀ x : X, I.map (ρ (x : D)) ≠ I → Nonempty (Representation.Equiv
      R.toRepresentation (conjugateSubrepresentation ρ H R (x : D)).toRepresentation.dual) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  obtain ⟨_,hgen,⟨x,hx,_,_⟩,_⟩ := completion h hn hC hm S hXS hSX hind hI hv hbalance
  have hxi (y : X) : (y : D)⁻¹ = y := inv_eq_iff_mul_eq_one.mpr (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (y : D) y.property)
  have hi := h.irreducible_of_not_solvable hn
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful hi H
    hC.componentOrbit_top_ne_bot
  have hpair (y : X) (hy : I.map (ρ (y : D)⁻¹) ≠ I) : I ⊔ I.map (ρ (y : D)⁻¹) = ⊤ := by
    rw [hxi] at hy ⊢
    exact (h.independent_orbit_pair I (by have := hI.isIrrPlus.finrank_gt_two ρ H; omega)
      (hI.independent_orbit_of_fixedSpace_eq_bot ρ hfix) y hy).1.symm.trans hgen
  obtain ⟨hf,hns,hd⟩ := hI.faithful_dual_of_isotropic_pair ρ h.faithful B h.nondegenerate
    h.preserves hfix (hI.isIrrPlus.irreducible_of_normal_restriction ρ hi H) hiso
    ⟨x,by rwa [hxi]⟩ hpair
  exact ⟨hf,hns,fun y hy => hd y (by rwa [hxi])⟩
/-- Completion data on the same exchanged constituent and literal stabilizer.
The form alternative keeps the faithful dual companion when the constituent
is isotropic. -/
@[expose] def CompletedData
    (ρ : Representation (ZMod 2) D U) (B : LinearMap.BilinForm (ZMod 2) U)
    (C X : Subgroup D) [IsElementaryAbelian 2 X]
    (I : Submodule (ZMod 2) U)
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I) : Prop :=
    (¬ Function.Surjective (invariantSubspace ρ
      (componentOrbit C ⊤) I hI.invariant).toRepresentation.asGroupHom) ∧
    Homogeneous.orbitSpan ρ X I = ⊤ ∧
    (∃ x : X, I.map (ρ x) ≠ I ∧
      IsCompl I (I.map (ρ x)) ∧
      finrank (ZMod 2) U = 2 * finrank (ZMod 2) I) ∧
    let Y := (subspaceStabilizer ρ I).subgroupOf X
    letI : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
    finrank (ZMod 2) I = finrank (ZMod 2) (Additive Y) + 2 ∧
    (∀ y : Y, (∀ w : I, ρ ((y : X) : D) w = w) → y = 1) ∧
    (∀ y : Y, ((y : X) : D) ∈
      centralizer (componentOrbit C ⊤ : Set D) → y = 1) ∧
    ((B.restrict I).Nondegenerate ∨
      let H := componentOrbit C ⊤
      letI : H.Normal := componentOrbit_top_normal C
      let R := invariantSubspace ρ H I hI.invariant
      (∀ a ∈ I, ∀ b ∈ I, B a b = 0) ∧
      Function.Injective R.toRepresentation.asGroupHom ∧
      ¬ Nonempty (Representation.Equiv R.toRepresentation R.toRepresentation.dual) ∧
      ∀ x : X, I.map (ρ (x : D)) ≠ I →
        Nonempty (Representation.Equiv R.toRepresentation
          (conjugateSubrepresentation ρ H R (x : D)).toRepresentation.dual))

include h hn hC hm S hXS hSX hind hI hv in
private theorem complete_data
    (hbalance : 2 * (Group.rank X + 1) = finrank (ZMod 2) U) :
    CompletedData ρ B C X I hI := by
  obtain ⟨hp,hgen,hpair,hfaith⟩ := completion h hn hC hm S hXS hSX hind hI hv hbalance
  refine ⟨hp,hgen,hpair,stabilizer_degree h hn hC hm S hXS hSX hind hI hv hbalance,
    hfaith.1,hfaith.2,?_⟩
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  rcases hI.isIrrPlus.isotropic_or_nondegenerate_of_normal_restriction ρ
    (h.irreducible_of_not_solvable hn) H B h.alternating h.preserves with hiso | hnd
  · exact Or.inr ⟨hiso,faithful_dual_of_isotropic h hn hC hm S hXS hSX
      hind hI hv hbalance hiso⟩
  · exact Or.inl hnd

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedGeometry

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor CoreGeometry
open LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Original-flag application of the exchanged completion. In particular, the
full-linear exclusion and the spanning pair are deductions, not recognition
premises added to the source. -/
theorem source_exchanged_completion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit C ⊤)
      (F.terminalDot (F.X g)) I) (hv : v ∉ I) :
    ExchangedGeometry.CompletedData F.terminalRepresentation B C (F.terminalDot (F.X g)) I hI := by
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hns := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := Chapter14.Section03.NonabelianSource.Recognition.terminal_component_normalizer_index_le_two
    d.qtke F (by decide) C hC
  obtain ⟨_,hE,hX,_⟩ := source_terminal_ranks_of_no_lowRank d earlier hq chosen
    structural alternatives F hne hZ g hgP hgH v hline hn
  have hb : 2 * (Group.rank (F.terminalDot (F.X g)) + 1) =
      finrank (ZMod 2) (Additive F.Uhat) := by omega
  have hPX : (P : Subgroup F.TerminalHdot) ≤ normalizer (F.terminalDot (F.X g) : Set F.TerminalHdot) :=
    (normal_subgroupOf_iff_le_normalizer hXP).mp hN
  exact ExchangedGeometry.complete_data hyp hns hC hm P hXP hPX hind hI hv hb

namespace FixedLineReduction
/-- The surviving original branch now has a proper constituent action and a
spanning exchanged pair with the exact stabilizer degree. All original marked
geometry and the independent mixed-size input are retained. -/
theorem source_large_completed_exchanged_remainder_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g)) ∧
      ∃ C : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot C ∧
        ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
        ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B C ∧
        ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
        ∃ hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
            (componentOrbit C ⊤) (F.terminalDot (F.X g)) I,
          v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
            (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I ∧
          ExchangedGeometry.CompletedData F.terminalRepresentation B C
            (F.terminalDot (F.X g)) I hI := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo⟩ :=
    source_large_exchanged_remainder_of_mixed_size d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  exact ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo,
    source_exchanged_completion d earlier hq chosen structural alternatives F hne hZ hlarge
      g hgP hgH hyp hline hn hC hm hI hv⟩
end FixedLineReduction
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
