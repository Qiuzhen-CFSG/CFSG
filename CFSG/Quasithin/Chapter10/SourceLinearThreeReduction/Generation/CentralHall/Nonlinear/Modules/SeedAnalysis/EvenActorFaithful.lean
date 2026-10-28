module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.MovedComponent
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalSuzuki
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSuzukiExchange

/-!
# Faithfulness of every original even-linear starred actor

The exact component-action kernel has order prime to three. If a starred
actor meets it nontrivially, D.3.9 supplies a moved three-subgroup or a
component orbit in that kernel. The first is impossible. Every remaining
component is a concrete Suzuki group: normalized support contradicts the
strict constituent ratio drop, and exchanged support contradicts the Suzuki
displacement bound. The actual semisimple layer's odd-rank bound supplies
the required orbit of length two.

This removes both the constituent and five-divisibility hypotheses from
actor faithfulness, in either original separated seed orientation. The
EvenConstituent consumer constructs the constituent and proves the literal
Hall exponent. Source separation and ambient natural-tensor exclusion
remain with qt-d-10-nona5-central-hall-orders.
Source: Aschbacher--Smith D.3.9, D.3.21 and 10.1.3, pp.199--207,742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance evenActorFaithfulElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance evenActorFaithfulFiniteDimensional :
    FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
  Module.Finite.of_finite
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every starred cubic actor is faithful on the original binary SL2 quotient,
with no assumed constituent or parity restriction on the field degree. -/
theorem moved_starred_actor_faithful
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D))) :
    Function.Injective ((movedImageQuotientAction D c.nonnormal e).comp A.subtype) := by
  classical
  let ρ := movedStabilizerAction D
  let σ := imageRepresentation ρ
  let α := movedImageQuotientAction D c.nonnormal e
  let S := movedStabilizerComponentImage D
  let : FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
    Module.Finite.of_finite
  obtain ⟨⟨eS⟩,hC⟩ := movedImage_component_and_centralizer D c.nonnormal e
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
  have h3 : Nat.Coprime 3 (Nat.card α.ker) := by
    apply movedImageQuotientAction_ker_card_coprime D c ht htn hsep e 3 (by decide)
    rw [Nat.card_congr e.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_two _
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
