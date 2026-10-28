module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.InnerPairCalculation

/-!
# Transport of the inner Sylow-pair invariant through a section

A surjective section map with two-group kernel is faithful on an order-nine
subgroup. If the normalizer of the pair preserves the section, the intrinsic
degree-four invariant pulls back to the original odd subgroup. Restriction
of the Sylow subgroup and permutation of the pair are retained explicitly.

Source: Aschbacher–Smith, Proposition 1.3.4, printed pp.509–511, and the
binary outer-action conclusion in the proof of 15.4.20, printed p.1164.
-/

@[expose] public section
open Subgroup BinaryLinear BinaryLinear.OuterCyclic
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.BinaryAction.FiveOuter

local instance : Finite (LinearGroup 4) :=
  Finite.of_equiv _ (matrixEquivLinear 4).toEquiv

variable {Q : Type*} [Group Q]

/-- A proper nontrivial subgroup preserved by the inner automorphisms of the pair. -/
def InnerSubgroupInvariant (S R : Subgroup Q) : Prop :=
  ∃ K : Subgroup R, K ≠ ⊥ ∧ K ≠ ⊤ ∧
    ∀ α : MulAut R,
      (∃ q : Q, (∀ x : Q, MulAut.conj q x ∈ S ↔ x ∈ S) ∧
        ∀ x : R, (α x : Q) = MulAut.conj q x) →
      ∀ x ∈ K, α x ∈ K

theorem normalizes_of_extension (R : Subgroup Q) (α : MulAut R) (q : Q)
    (he : ∀ x : R, (α x : Q) = MulAut.conj q x) :
    q ∈ normalizer (R : Set Q) := by
  intro x
  change x ∈ R ↔ MulAut.conj q x ∈ R
  constructor
  · intro hx
    rw [← he ⟨x, hx⟩]
    exact (α ⟨x, hx⟩).property
  · intro hx
    obtain ⟨r, hr⟩ := α.surjective ⟨MulAut.conj q x, hx⟩
    have hrx : (r : Q) = x := (MulAut.conj q).injective
      ((he r).symm.trans (congrArg Subtype.val hr))
    exact hrx ▸ r.property

private theorem permutes_subgroupOf (R S A : Subgroup Q) (hRA : R ≤ A) (hSA : S ≤ A)
    (hp : (R : Set Q) * (S : Set Q) = (S : Set Q) * (R : Set Q)) :
    (R.subgroupOf A : Set A) * (S.subgroupOf A : Set A) =
      (S.subgroupOf A : Set A) * (R.subgroupOf A : Set A) := by
  apply Set.image_injective.mpr A.subtype_injective
  simpa only [Set.image_mul, ← coe_map, map_subgroupOf_eq_of_le hRA,
    map_subgroupOf_eq_of_le hSA] using hp

/-- Reduction to the proved four-dimensional calculation on a faithful section. -/
theorem invariant_from_four_section [Finite Q] (S : Sylow 2 Q) (R A : Subgroup Q)
    (hR : Nat.card R = 9) (hRA : R ≤ A) (hSA : (S : Subgroup Q) ≤ A)
    (hN : normalizer (R : Set Q) ⊓ normalizer (S : Set Q) ≤ A)
    (hperm : (R : Set Q) * (S : Set Q) = (S : Set Q) * (R : Set Q))
    (f : A →* LinearGroup 4) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    InnerSubgroupInvariant (S : Subgroup Q) R := by
  let g := f.comp (inclusion hRA)
  have hrp : IsPGroup 3 R := IsPGroup.of_card (show Nat.card R = 3 ^ 2 from hR)
  have hdis := (hrp.comap_subtype (K := A)).disjoint_of_coprime hker
    (by decide : Nat.Coprime 3 2)
  have hg : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro r hr
    exact Subtype.ext (congrArg (fun a : A => (a : Q))
      ((Subgroup.disjoint_def.mp hdis) (show inclusion hRA r ∈ R.subgroupOf A from r.property) hr))
  let R' := g.range
  let eR : R ≃* R' := MonoidHom.ofInjective hg
  let S' := (S.subtype hSA).mapSurjective hf
  have heR : R' = (R.subgroupOf A).map f := by
    change (f.comp (inclusion hRA)).range = _
    rw [MonoidHom.range_comp, inclusion_range]
  have hc : Nat.card R' = 9 := (Nat.card_congr eR.toEquiv).symm.trans hR
  have hp : (R' : Set (LinearGroup 4)) * (S' : Set (LinearGroup 4)) =
      (S' : Set (LinearGroup 4)) * (R' : Set (LinearGroup 4)) := by
    change (R' : Set (LinearGroup 4)) *
      (((S : Subgroup Q).subgroupOf A).map f : Set (LinearGroup 4)) =
      (((S : Subgroup Q).subgroupOf A).map f : Set (LinearGroup 4)) *
        (R' : Set (LinearGroup 4))
    rw [heR]
    simpa only [coe_map, ← Set.image_mul] using congrArg (Set.image f)
      (permutes_subgroupOf R (S : Subgroup Q) A hRA hSA hperm)
  obtain ⟨K', hKb, hKt, hK⟩ :=
    Chapter1.Terminal.LinearFourActions.InnerPairCalculation.invariant_subgroup_of_linear_equiv
      (MulEquiv.refl (LinearGroup 4)) S' R' hc hp
  let K := K'.comap eR.toMonoidHom
  refine ⟨K, ?_, ?_, ?_⟩
  · intro hb
    apply hKb
    apply comap_injective (f := eR.toMonoidHom) eR.surjective
    simpa only [MonoidHom.comap_bot, MonoidHom.ker_eq_bot eR.toMonoidHom eR.injective] using hb
  · intro ht
    apply hKt
    apply comap_injective (f := eR.toMonoidHom) eR.surjective
    simpa only [comap_top] using ht
  · rintro α ⟨q, hqS, hqR⟩ x hx
    have hqNR := normalizes_of_extension R α q hqR
    have hqNS : q ∈ normalizer (S : Set Q) := fun x => (hqS x).symm
    let a : A := ⟨q, hN ⟨hqNR, hqNS⟩⟩
    have hqSA : a ∈ normalizer ((S : Subgroup Q).subgroupOf A : Set A) := by
      rw [← subgroupOf_normalizer_eq hSA]
      exact hqNS
    have hqS' : f a ∈ normalizer (S' : Set (LinearGroup 4)) :=
      ((S : Subgroup Q).subgroupOf A).le_normalizer_map f (mem_map_of_mem f hqSA)
    have hα' (r : R') :
        ((MulAut.congr eR α) r : LinearGroup 4) = MulAut.conj (f a) r := by
      change f (inclusion hRA (α (eR.symm r))) = _
      have he : inclusion hRA (α (eR.symm r)) =
          a * inclusion hRA (eR.symm r) * a⁻¹ := Subtype.ext (hqR (eR.symm r))
      rw [he, map_mul, map_mul, map_inv]
      have hr : f (inclusion hRA (eR.symm r)) = r :=
        congrArg Subtype.val (eR.apply_symm_apply r)
      rw [hr]
      rfl
    have hx' := hK (MulAut.congr eR α)
      ⟨f a, fun x => (hqS' x).symm, hα'⟩ (eR x) hx
    change eR (α (eR.symm (eR x))) ∈ K' at hx'
    change eR (α x) ∈ K'
    simpa only [eR.symm_apply_apply] using hx'

/-- An elementary complement has trivial Frattini subgroup, so its invariant descends. -/
theorem InnerSubgroupInvariant.toInnerPairInvariant [Finite Q] (S R : Subgroup Q)
    [IsElementaryAbelian 3 R] (h : InnerSubgroupInvariant S R) :
    Chapter1.Terminal.LinearFourActions.InnerPairInvariant S R := by
  let _ : Fact (IsPGroup 3 R) := ⟨IsElementaryAbelian.isPGroup 3 R⟩
  obtain ⟨K, hKb, hKt, hK⟩ := h
  let π := QuotientGroup.mk' (frattini R)
  have hπ : Function.Injective π := by
    apply (MonoidHom.ker_eq_bot_iff π).mp
    rw [QuotientGroup.ker_mk']
    exact frattini_eq_bot_of_isElementaryAbelian (p := 3)
  refine ⟨K.map π, ?_, ?_, ?_⟩
  · exact fun hb => hKb ((K.map_eq_bot_iff_of_injective hπ).mp hb)
  · intro ht
    apply hKt
    apply map_injective hπ
    rw [ht, map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
  · intro α hα x hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨α r, hK α hα r hr, (quotientAut_apply_mk _ _ _).symm⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.BinaryAction.FiveOuter
