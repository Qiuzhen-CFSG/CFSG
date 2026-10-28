module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaResidualStructure
public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.PlaneGeometry
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.Sylow
public import Theory.Representation.BinaryOffender.FourDimensionalFixedLine

/-!
# Intersection-core noncentrality for the full Omega module

The actual Sylow image is elementary of order four. Cubic ratio three
halves makes its fixed space a line. The original central seed embeds in
that line, and its conjugates generate the nontrivial full local module,
so the seed has order two. Original 14.1.12 supplies distinctness of the
selected local and its centralizer partner. Core growth 14.1.14 then gives
14.1.17(1) on the original module, removing the noncentrality premise in
this full-module branch of 15.2.3.

The proper moved-module branch requires its separate source core argument.
Source: Aschbacher--Smith, printed pp.979--980,1104--1105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

theorem omega_full_centralInvolutions_card (T : Sylow 2 G) (M : Subgroup G)
    [IsElementaryAbelian 2 (localModule T M)]
    (hTM : (T : Subgroup G) ≤ M)
    (ho : SourceCases.Omega (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _))) :
    Nat.card (centralInvolutions T) = 2 := by
  let V := localModule T M
  let Z := centralInvolutions T
  let hn : M ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  let D := (actionHom M V hn).range
  let ρ := imageRepresentation M V hn
  let f : M →* D := (actionHom M V hn).rangeRestrict
  let S := (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  obtain ⟨hS,hSc⟩ := SymmetricThreeProductResidual.sylow_elementary_four
    (D := D) ho.2.2.2.1.some S
  have hfix : Nat.card (fixedSpace ρ (S : Subgroup D)) = 2 :=
    fixed_card_of_four_group_cubic_ratio ρ ho.2.2.1 ho.2.1 _ hS hSc
  have hZV : Z ≤ V := le_conjugateSpanBy _ _
  have hmem (z : Z) : Additive.ofMul (⟨z,hZV z.property⟩ : V) ∈
      fixedSpace ρ (S : Subgroup D) := by
    rintro ⟨s,hs⟩
    obtain ⟨t,ht,rfl⟩ := hs
    apply Additive.toMul.injective
    apply Subtype.ext
    change (t : G) * (z : G) * (t : G)⁻¹ = z
    rw [centralInvolutions_le_centralizer_sylow T z.property t ht,mul_inv_cancel_right]
  let j : Z → fixedSpace ρ (S : Subgroup D) :=
    fun z => ⟨Additive.ofMul ⟨z,hZV z.property⟩,hmem z⟩
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (congrArg (fun v : fixedSpace ρ (S : Subgroup D) =>
      (v.val.toMul : G)) h)
  have hle : Nat.card Z ≤ 2 := hfix ▸ Nat.card_le_card_of_injective j hj
  have hne : Z ≠ ⊥ := by
    intro he
    have hV : V = ⊥ := bot_unique (conjugateSpanBy_le he.le le_normalizer_of_normal)
    have hc : Nat.card V = 16 := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
      rw [Nat.card_zmod,ho.2.2.1] at h
      exact (Nat.card_congr Additive.toMul).symm.trans h
    rw [hV,card_bot] at hc
    contradiction
  have hpos : 1 < Nat.card Z :=
    Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot Z).mpr hne)
  change Nat.card Z = 2
  omega

theorem source_omega_full_core_noncentral
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} [IsElementaryAbelian 2 (localModule T M)]
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (ho : SourceCases.Omega (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _))) :
    ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (localModule T M : Set G) := by
  have hZ := omega_full_centralInvolutions_card T M hM.1.2 ho
  obtain ⟨D,hD,Mf,hMf,hne,hmax,hBaum,hdom,hoff,hall,hC⟩ :=
    InitialSource.UniformControl.source_lemma_14_1_12_selection hG T hempty hu hmany
  have hMMf := hall hZ M hM
  have hMMc : M ≠ Mc := fun he => hne (hMMf.symm.trans he)
  exact (Chapter14.SourcePreliminaries.plane_intersection_core_inputs
    hG T hempty hM.1 hu hmany hZ hMMc).2.1
end CFSG.Quasithin.Chapter15.Section02
