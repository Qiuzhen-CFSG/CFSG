module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.EvenActorFaithful
public import CFSG.Quasithin.Chapter10.SourceCubicResidual

/-!
# The original moved component and three-divisible actor faithfulness

Identify the actual component image on W = [V_M,L] with L/O2(L), before
selecting a constituent or a model. In either separated seed orientation,
the opposite component acts trivially. The source cubic residual then makes
the component centralizer three-free. The same normalized/exchanged Suzuki
exclusions used in the even-linear row make every starred actor faithful
on this original quotient. The odd-prime and Janko applications use this
without assuming moved minimality.

Source: Aschbacher--Smith D.3.9, D.3.21 and 10.1.3, pp.199--207,742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance originalComponentElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance originalComponentFiniteDimensional : FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
  Module.Finite.of_finite
private theorem component_le_stabilizer : L ≤ D.maximalLocal ⊓ normalizer (L : Set G) :=
  le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer
local instance originalComponentNormal : (movedStabilizerComponent D).Normal :=
  (normal_subgroupOf_iff_le_normalizer (component_le_stabilizer D)).mpr inf_le_right

/-- The literal two-core quotient map on the stabilizer's component. -/
@[expose] def originalMovedComponentProjection :
    movedStabilizerComponent D →* (L ⧸ pCore 2 L) :=
  (QuotientGroup.mk' (pCore 2 L)).comp
    (subgroupOfEquivOfLe (by exact component_le_stabilizer D)).toMonoidHom

/-- The original quotient marking is surjective. -/
theorem originalMovedComponentProjection_surjective :
    Function.Surjective (originalMovedComponentProjection D) :=
  (QuotientGroup.mk'_surjective _).comp
    (subgroupOfEquivOfLe (component_le_stabilizer D)).surjective

/-- The original component action has exactly the marked two-core kernel. -/
theorem originalMovedComponent_kernel
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ((actionHom (movedStabilizerAction D)).comp (movedStabilizerComponent D).subtype).ker =
      (originalMovedComponentProjection D).ker := by
  ext l
  constructor
  · intro hl
    let lL : L := ⟨l.val.val,l.property⟩
    have hfix := (actionHom_eq_one_iff (movedStabilizerAction D) l.val).mp hl
    have htriv : movedQuotientAction D hn (QuotientGroup.mk' (pCore 2 L) lL) = 1 := by
      apply LinearMap.ext
      intro v
      obtain ⟨w,hw⟩ := (movedQuotientSection D hn).onto (Multiplicative.ofAdd v)
      have he := (movedQuotientSection D hn).equivariant lL w
      have hh : (⟨(lL:G) * (w:G) * (lL:G)⁻¹,
          (mem_normalizer_iff.mp ((movedQuotientSection D hn).normalized lL.property) w).mp w.property⟩ :
          (⁅D.fullModule,L⁆ : Subgroup G)) = w := by
        exact congrArg Additive.toMul (hfix (Additive.ofMul w))
      rw [hh,hw] at he
      exact he.symm
    change QuotientGroup.mk' (pCore 2 L) lL = 1
    rw [show QuotientGroup.mk' (pCore 2 L) lL = 1 from
      movedQuotientAction_faithful D hn (htriv.trans (movedQuotientAction D hn).map_one.symm)]
  · intro hl
    have hlcore : (⟨l.val.val,l.property⟩ : L) ∈ pCore 2 L := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact hl
    apply (actionHom_eq_one_iff (movedStabilizerAction D) l).mpr
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l.val : G) * (w.toMul : G) * (l.val : G)⁻¹ = (w.toMul : G)
    have hc := mem_centralizer_iff.mp (source_component_core_centralizes_fullModule D
      (mem_map_of_mem L.subtype hlcore)) w.toMul (moved_le_fullModule D w.toMul.property)
    change (w.toMul : G) * (l.val : G) = (l.val : G) * (w.toMul : G) at hc
    rw [←hc,mul_inv_cancel_right]

/-- The full moved component image is the original two-core quotient. -/
@[expose] def originalMovedComponentEquiv
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    movedStabilizerComponentImage D ≃* (L ⧸ pCore 2 L) :=
  (QuotientGroup.quotientKerEquivRange
    ((actionHom (movedStabilizerAction D)).comp (movedStabilizerComponent D).subtype)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (originalMovedComponent_kernel D hn)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (originalMovedComponentProjection D)
        (originalMovedComponentProjection_surjective D)))

/-- Conjugation on the original component quotient through the faithful moved image. -/
@[expose] def originalMovedQuotientAction
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    actionImage (movedStabilizerAction D) →* MulAut (L ⧸ pCore 2 L) :=
  (MulAut.congr (originalMovedComponentEquiv D hn)).toMonoidHom.comp MulAut.conjNormal

/-- The quotient action has precisely the actual component centralizer as kernel. -/
theorem originalMovedQuotientAction_kernel
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (originalMovedQuotientAction D hn).ker =
      centralizer (movedStabilizerComponentImage D : Set (actionImage (movedStabilizerAction D))) := by
  exact (MonoidHom.ker_comp_of_injective
    (MulAut.conjNormal : actionImage (movedStabilizerAction D) →* MulAut (movedStabilizerComponentImage D))
    (MulAut.congr (originalMovedComponentEquiv D hn)).toMonoidHom
    (MulAut.congr (originalMovedComponentEquiv D hn)).injective).trans
      (MulAut.conjNormal_ker_eq_centralizer _)

/-- The literal quotient-action kernel is three-free in every three-divisible row. -/
theorem originalMovedQuotientAction_kernel_three_free
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) :
    Nat.Coprime 3 (Nat.card (originalMovedQuotientAction D c.nonnormal).ker) := by
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  let R := (localOrbit T L).subgroupOf N
  let ρ := movedStabilizerAction D
  let f := actionHom ρ
  let α := originalMovedQuotientAction D c.nonnormal
  let S := movedStabilizerComponentImage D
  have hLN : L ≤ N := component_le_stabilizer D
  have hRN : localOrbit T L ≤ N := le_inf (localOrbit T L).le_normalizer
    (source_nonnormal_orbit_le_normalizer D c.nonnormal)
  have hpair : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 c.nonnormal)
      inf_le_right ht htn
  have hLtN : L.map (MulAut.conj t).toMonoidHom ≤ N :=
    (le_sup_right.trans hpair.symm.le).trans hRN
  have hkill : (L.map (MulAut.conj t).toMonoidHom).subgroupOf N ≤ f.ker := by
    intro l hl
    apply (actionHom_eq_one_iff ρ l).mpr
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * (w.toMul : G) * (l : G)⁻¹ = (w.toMul : G)
    have hc := mem_centralizer_iff.mp
      (full_moved_centralizes_opposite_of_seed_separated D ht htn hsep w.toMul.property) l hl
    rw [hc,mul_assoc,mul_inv_cancel,mul_one]
  have hRS : R.map f = S := by
    change ((localOrbit T L).subgroupOf N).map f = _
    rw [hpair,subgroupOf_sup hLN hLtN,Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff (f := f) _).mpr hkill,sup_bot_eq]
    change (L.subgroupOf N).map f = ((actionHom ρ).comp (movedStabilizerComponent D).subtype).range
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let eS := originalMovedComponentEquiv D c.nonnormal
  let : IsSimpleGroup S := eS.isSimpleGroup
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv eS.symm
  have hdis : S ⊓ α.ker = ⊥ := by
    rw [show α.ker = centralizer (S : Set (actionImage ρ)) from
      originalMovedQuotientAction_kernel D c.nonnormal]
    apply bot_unique
    rintro a ⟨ha,hac⟩
    have hz : (⟨a,ha⟩ : S) ∈ center S := by
      apply mem_center_iff.mpr
      intro s
      exact Subtype.ext (mem_centralizer_iff.mp hac s s.property)
    rw [center_eq_bot_of_simple_perfect] at hz
    exact congrArg Subtype.val (mem_bot.mp hz)
  have hc : Nat.card α.ker ∣ S.index := by
    have hh := S.relIndex_dvd_index_of_normal α.ker
    rwa [←inf_relIndex_right,hdis,relIndex_bot_left] at hh
  have hindex : R.index ∣ ((localOrbit T L).subgroupOf D.maximalLocal).index := by
    change (localOrbit T L).relIndex N ∣ _
    rw [←relIndex_subgroupOf (H := localOrbit T L) (L := D.maximalLocal) inf_le_left]
    exact relIndex_dvd_index_of_le (subgroupOf_mono D.maximalLocal hRN)
  have hS : S.index ∣ ((localOrbit T L).subgroupOf D.maximalLocal).index := by
    rw [←hRS]
    exact (R.index_map_dvd ρ.asGroupHom.rangeRestrict_surjective).trans hindex
  have hres : (localOrbit T L).subgroupOf D.maximalLocal = primeToResidual 3 D.maximalLocal := by
    apply map_injective D.maximalLocal.subtype_injective
    rw [map_subgroupOf_eq_of_le (localOrbit T L).le_normalizer,
      source_nonnormal_cubic_residual D c.nonnormal hd]
  have hcop : Nat.Coprime 3 ((localOrbit T L).subgroupOf D.maximalLocal).index := by
    rw [hres]
    exact primeToResidual_index_coprime 3
  exact hcop.of_dvd_right (hc.trans hS)

/-- Every starred cubic actor is faithful on the original three-divisible quotient. -/
theorem original_three_divisible_starred_actor_faithful
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D))) :
    Function.Injective ((originalMovedQuotientAction D c.nonnormal).comp A.subtype) := by
  classical
  let ρ := movedStabilizerAction D
  let σ := imageRepresentation ρ
  let α := originalMovedQuotientAction D c.nonnormal
  let S := movedStabilizerComponentImage D
  let : FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
    Module.Finite.of_finite
  let eS := (originalMovedComponentEquiv D c.nonnormal).symm
  have hC := originalMovedQuotientAction_kernel D c.nonnormal
  let := D.quasisimple
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv eS
  let : ρ.IsIrreducible := movedStabilizerAction_irreducible D c ht htn hsep
  have hi : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective σ).mp
      (inferInstance : ρ.IsIrreducible)
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let : Nontrivial S := eS.injective.nontrivial
  have hSn : S ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot S).mp inferInstance
  have hfull := subspaceCommutator_top_eq_top_of_normal_faithful_irreducible σ
    (imageRepresentation_injective ρ) hi S hSn
  have hcore := movedStabilizerImage_twoCore_eq_bot D c ht htn hsep
  have h3 := originalMovedQuotientAction_kernel_three_free D c ht htn hsep hd
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  apply Subtype.ext
  by_contra hne
  have hAn : A ⊓ centralizer (S : Set (actionImage ρ)) ≠ ⊥ := by
    intro hz
    have hm : a.val ∈ A ⊓ centralizer (S : Set (actionImage ρ)) := ⟨a.property,hC ▸ ha⟩
    exact hne (mem_bot.mp (hz ▸ hm))
  obtain ⟨X,hXC,_,hXn,hm,hcase⟩ :=
    ChosenSource325.exists_starred_moved_subgroup_in_component_centralizer σ
      (imageRepresentation_injective ρ) S hcore hfull hA hAn
  rcases hcase with ⟨_,hXp⟩ | ⟨J,hJ,hJC,hXorbit⟩
  · have hXK : X ≤ α.ker := hXC.trans hC.symm.le
    have hcX : Nat.Coprime 3 (Nat.card X) := h3.of_dvd_right (card_dvd_of_le hXK)
    obtain ⟨k,hk⟩ := hXp.exists_card_eq
    apply hXn
    apply Subgroup.card_eq_one.mp
    rw [hk] at hcX ⊢
    exact Nat.eq_one_of_dvd_coprimes (hcX.pow_left k) dvd_rfl dvd_rfl
  · have hJK : J ≤ α.ker := hJC.trans hC.symm.le
    have hJ3 := h3.of_dvd_right (card_dvd_of_le hJK)
    obtain ⟨r,hr,⟨eJ⟩⟩ := movedStabilizerImage_component_suzuki D c ht htn hsep J hJ hJ3
    let := hJ.2
    have hnot : ¬ A ≤ normalizer (J : Set (actionImage ρ)) := by
      intro hn
      have horbit : componentOrbit J A = J :=
        le_antisymm (iSup_conjugates_le_of_le_normalizer J A J le_rfl hn) (le_componentOrbit J A)
      have hXJ : X = J := hXorbit.trans horbit
      have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible σ
        (imageRepresentation_injective ρ) hi S hSn
      apply ChosenSource325.no_normalized_suzuki_support σ (imageRepresentation_injective ρ)
        S J A (A ⊓ centralizer (S : Set (actionImage ρ))) hfix hJC
        (movedStabilizerImage_component_sqtk D J hJ) (hXJ ▸ hXn) hn hA inf_le_left _ hr eJ
      simpa only [hXJ] using hm
    have hlay := movedStabilizerImage_semisimple_sqtk D
      (componentLayer (actionImage ρ)) componentLayer_idempotent
    have hindex : (normalizer (J : Set (actionImage ρ))).index = 2 :=
      (hJ.normal_or_index_two_of_layer_odd_rank_le_two hlay.stronglyQuasithin).resolve_left
        (fun hj => hnot (by
          let := hj
          exact le_top.trans (show normalizer (J : Set (actionImage ρ)) = ⊤ from normalizer_eq_top J).ge))
    obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hnot
    let N := normalizer (J : Set (actionImage ρ))
    let : N.Normal := normal_of_index_eq_two hindex
    have hdiv : N.relIndex A ∣ 2 := by
      simpa only [show N.index = 2 from hindex] using N.relIndex_dvd_index_of_normal A
    have hirel : N.relIndex A = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
        (fun he => hnot (Subgroup.relIndex_eq_one.mp he))
    have horbit : componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom :=
      componentOrbit_eq_sup_of_index_two J A N hirel inf_le_right ha han
    exact ChosenSource325.not_starred_exchanged_suzuki_support σ (imageRepresentation_injective ρ)
      hcore J A hJ hindex a ha han horbit hA r hr eJ

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
