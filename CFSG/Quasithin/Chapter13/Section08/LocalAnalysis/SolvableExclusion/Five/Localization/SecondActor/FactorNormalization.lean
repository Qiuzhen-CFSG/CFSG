module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.Data

/-!
# Normalization of the canonical five-factors

Commuting factors with disjoint moved subgroups fix each other's supports.
Coprime restriction faithfulness consequently identifies each factor as the
pointwise kernel on the other support. The rank-one actor centralizes the
second factor, so it preserves that support and normalizes the first factor.
Prime order and noncentrality then identify the first factor with [P*,Uγ*].
As Vγ* normalizes P* and centralizes Uγ*, it normalizes this commutator;
the other support-kernel identity gives normalization of the second factor.
With only one factor, normality of P* settles the claim directly.

All images are the actual subgroups of H/O₂(H), acting faithfully on UH/V₁.
Normality of P* is relative to this starred group; no normality in G is used.
This proves a conditional algebraic step. The second-actor assembly supplies
its source inputs and remains responsible for constructing the complement.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951 (PDF p.968), final two paragraphs.
-/

public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.FactorNormalization

variable {W : Type*} [Group W]

private theorem cross_fixed (A B : Subgroup (MulAut W))
    (hc : ⁅A, B⁆ = ⊥)
    (hd : Disjoint (commutatorAction A W) (commutatorAction B W)) :
    ∀ a ∈ A, ∀ w ∈ commutatorAction B W, (a : MulAut W) w = w := by
  have hn : A ≤ normalizer (B : Set (MulAut W)) :=
    (commutator_eq_bot_iff_le_centralizer.mp hc).trans (centralizer_le_normalizer _)
  let : IsInvariant A W (commutatorAction B W) :=
    commutatorAction_isInvariant_of_normalizing_actor A B hn
  intro a ha w hw
  have hA : w⁻¹ * a w ∈ commutatorAction A W := by
    rw [commutatorAction_eq_closure]
    exact subset_closure ⟨⟨a, ha⟩, w, rfl⟩
  have hB : w⁻¹ * a w ∈ commutatorAction B W :=
    (commutatorAction B W).mul_mem ((commutatorAction B W).inv_mem hw)
      ((IsInvariant.invariant (⟨a, ha⟩ : A) w).mp hw)
  exact (inv_mul_eq_one.mp ((Subgroup.disjoint_def.mp hd) hA hB)).symm

private theorem support_kernel [Finite W] [IsMulCommutative W]
    (A B : Subgroup (MulAut W))
    (hcop : Nat.Coprime (Nat.card B) (Nat.card W))
    (hc : ⁅A, B⁆ = ⊥)
    (hd : Disjoint (commutatorAction A W) (commutatorAction B W)) :
    A = (A ⊔ B) ⊓ fixingSubgroup (MulAut W) (commutatorAction B W : Set W) := by
  have hfix := cross_fixed A B hc hd
  apply le_antisymm
  · exact le_inf le_sup_left (fun a ha => (mem_fixingSubgroup_iff (MulAut W)).mpr (hfix a ha))
  · intro p hp
    have hn : A ≤ normalizer (B : Set (MulAut W)) :=
      (commutator_eq_bot_iff_le_centralizer.mp hc).trans (centralizer_le_normalizer _)
    have hprod := hp.1
    change p ∈ ((A ⊔ B : Subgroup (MulAut W)) : Set (MulAut W)) at hprod
    rw [coe_mul_of_left_le_normalizer_right A B hn] at hprod
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod
    have hb1 : b = 1 := by
      apply ActionSupport.eq_one_of_fixes_support B hcop ⟨b, hb⟩
      intro w hw
      have hab := (mem_fixingSubgroup_iff (MulAut W)).mp hp.2 w hw
      change a (b w) = w at hab
      exact a.injective (hab.trans (hfix a ha w hw).symm)
    change a * b ∈ A
    rw [hb1, mul_one]
    exact ha

private theorem normalizes_kernel (P : Subgroup (MulAut W)) (S : Subgroup W)
    (B : Subgroup (MulAut W)) (hn : B ≤ normalizer (P : Set (MulAut W)))
    (hi : ∀ b ∈ B, ∀ w ∈ S, (b : MulAut W) w ∈ S) :
    B ≤ normalizer (P ⊓ fixingSubgroup (MulAut W) (S : Set W) : Subgroup (MulAut W)) := by
  apply le_normalizer_iff.mpr
  intro b hb p hp
  refine ⟨(mem_normalizer_iff.mp (hn hb) p).mp hp.1, ?_⟩
  apply (mem_fixingSubgroup_iff (MulAut W)).mpr
  intro w hw
  change b (p (b⁻¹ w)) = w
  have he := (mem_fixingSubgroup_iff (MulAut W)).mp hp.2 (b⁻¹ w) (hi b⁻¹ (B.inv_mem hb) w hw)
  change p (b⁻¹ w) = b⁻¹ w at he
  rw [he]
  exact b.apply_symm_apply w

private theorem normalizes_other_factor [Finite W] [IsMulCommutative W]
    (P A C B : Subgroup (MulAut W))
    (hP : P = A ⊔ C) (hc : ⁅A, C⁆ = ⊥)
    (hd : Disjoint (commutatorAction A W) (commutatorAction C W))
    (hcop : Nat.Coprime (Nat.card C) (Nat.card W))
    (hnP : B ≤ normalizer (P : Set (MulAut W)))
    (hnC : B ≤ normalizer (C : Set (MulAut W))) :
    B ≤ normalizer (A : Set (MulAut W)) := by
  have hA := support_kernel A C hcop hc hd
  rw [← hP] at hA
  rw [hA]
  apply normalizes_kernel P (commutatorAction C W) B hnP
  let : IsInvariant B W (commutatorAction C W) :=
    commutatorAction_isInvariant_of_normalizing_actor B C hnC
  intro b hb w hw
  exact (IsInvariant.invariant (⟨b, hb⟩ : B) w).mp hw

private theorem commutator_eq_first {K : Type*} [Group K]
    (P A C U : Subgroup K)
    (hP : P = A ⊔ C) (hAC : ⁅A, C⁆ = ⊥)
    (hUA : U ≤ normalizer (A : Set K)) (hUC : ⁅U, C⁆ = ⊥)
    (hAcard : (Nat.card A).Prime) (hm : ⁅U, A⁆ ≠ ⊥) :
    ⁅P, U⁆ = A := by
  have hle : ⁅P, U⁆ ≤ A := by
    apply commutator_le.mpr
    intro p hp u hu
    rw [hP] at hp
    change p ∈ ((A ⊔ C : Subgroup K) : Set K) at hp
    rw [coe_mul_of_left_le_normalizer_right A C
      ((commutator_eq_bot_iff_le_centralizer.mp hAC).trans (centralizer_le_normalizer _))] at hp
    obtain ⟨a, ha, c, hc, rfl⟩ := hp
    have hcu : c * u = u * c :=
      mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hUC) hu) c hc
    have he : ⁅a * c, u⁆ = ⁅a, u⁆ := by
      simp only [commutatorElement_def, mul_inv_rev]
      calc
        a * c * u * (c⁻¹ * a⁻¹) * u⁻¹ = a * (c * u) * c⁻¹ * a⁻¹ * u⁻¹ := by group
        _ = a * (u * c) * c⁻¹ * a⁻¹ * u⁻¹ := by rw [hcu]
        _ = a * u * a⁻¹ * u⁻¹ := by group
    rw [he]
    exact (le_normalizer_iff_commutator_le_left.mp hUA) (commutator_mem_commutator ha hu)
  let : Fact (Nat.card A).Prime := ⟨hAcard⟩
  rcases (⁅P, U⁆.subgroupOf A).eq_bot_or_eq_top_of_prime_card with hz | ht
  · have he : ⁅P, U⁆ = ⊥ := by
      have := congrArg (fun X : Subgroup A => X.map A.subtype) hz
      simpa only [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] using this
    apply False.elim
    apply hm
    apply bot_unique
    rw [commutator_comm]
    exact (commutator_mono (hP ▸ le_sup_left) le_rfl).trans he.le
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp ht)

private theorem normalizes_commutator {K : Type*} [Group K]
    (P U V : Subgroup K) (hP : V ≤ normalizer (P : Set K))
    (hU : V ≤ normalizer (U : Set K)) :
    V ≤ normalizer (⁅P, U⁆ : Subgroup K) := by
  intro v hv
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hP hv),
    mem_normalizer_iff_map_conj_eq.mp (hU hv)]


variable {G : Type*} [Group G]
variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]

private theorem actors_commute (a : StarAction H UH V₁)
    {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) (hc : ⁅X, Y⁆ = ⊥) :
    ⁅a.actors X, a.actors Y⁆ = ⊥ := by
  have hsub : ⁅X.subgroupOf H, Y.subgroupOf H⁆ = ⊥ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hX, map_subgroupOf_eq_of_le hY,
      hc, Subgroup.map_bot]
  rw [a.actors_eq, a.actors_eq, ← map_commutator, hsub, Subgroup.map_bot]

private theorem actors_sup (a : StarAction H UH V₁)
    {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    a.actors (X ⊔ Y) = a.actors X ⊔ a.actors Y := by
  simp only [StarAction.actors, Source.starImage, subgroupOf_sup hX hY, Subgroup.map_sup]

private theorem star_normalizes_of_actors (a : StarAction H UH V₁)
    (hf : Function.Injective a.action) (B X : Subgroup G)
    (hn : a.actors B ≤ normalizer (a.actors X : Set _)) :
    Source.starImage H B ≤ normalizer (Source.starImage H X : Set _) := by
  apply le_normalizer_iff.mpr
  intro b hb x hx
  have hm : a.action (b * x * b⁻¹) ∈ a.actors X := by
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hn (mem_map_of_mem _ hb)) _).mp (mem_map_of_mem _ hx)
  obtain ⟨y, hy, he⟩ := hm
  exact hf he ▸ hy

private theorem actors_coprime [Finite G]
    [IsElementaryAbelian 2 (UH ⧸ V₁.subgroupOf UH)]
    (a : StarAction H UH V₁) (hf : Function.Injective a.action)
    {P : Subgroup G} (f : Factorization a P) (i : Fin f.count) :
    Nat.Coprime (Nat.card (a.actors (f.factor i))) (Nat.card (UH ⧸ V₁.subgroupOf UH)) := by
  have hcard : Nat.card (a.actors (f.factor i)) = 5 :=
    (card_map_of_injective hf).trans (f.star_card i)
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 (UH ⧸ V₁.subgroupOf UH)).exists_card_eq
  rw [hcard, hn]
  exact (by decide : Nat.Coprime 5 2).pow_right n

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.FactorNormalization

namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open Localization.FactorNormalization
variable {G : Type*} [Group G] [Finite G]
variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]
    [IsElementaryAbelian 2 (UH ⧸ V₁.subgroupOf UH)]

/-- Every canonical starred five-factor is normalized by Vγ*. Neither the
number of factors nor their normalization is assumed. -/
theorem RankOneFactors.star_normalizes_factors
    (a : StarAction H UH V₁) (hf : Function.Injective a.action)
    {P Uγ Vγ : Subgroup G} (f : RankOneFactors a P Uγ)
    (hP : P ≤ H) (hPn : (Source.starImage H P).Normal)
    (hUV : Uγ ≤ Vγ) (_hV : Vγ ≤ H)
    (hVc : IsMulCommutative (Source.starImage H Vγ)) :
    ∀ i : Fin f.factors.count, Source.starImage H Vγ ≤
      normalizer (Source.starImage H (f.factors.factor i) : Set _) := by
  let : (Source.starImage H P).Normal := hPn
  have hnP : a.actors Vγ ≤ normalizer (a.actors P : Set _) :=
    (Subgroup.map_mono (show Source.starImage H Vγ ≤
      normalizer (Source.starImage H P : Set _) from le_normalizer_of_normal)).trans
        (le_normalizer_map a.action)
  have hUVs : Source.starImage H Uγ ≤ Source.starImage H Vγ :=
    Subgroup.map_mono (subgroupOf_mono H hUV)
  have hUVa : a.actors Uγ ≤ a.actors Vγ := Subgroup.map_mono hUVs
  have hcVU : ⁅a.actors Vγ, a.actors Uγ⁆ = ⊥ := by
    have hz : ⁅Source.starImage H Vγ, Source.starImage H Uγ⁆ = ⊥ :=
      bot_unique ((commutator_mono le_rfl hUVs).trans
        (commutator_self_eq_bot_iff.mpr hVc).le)
    rw [StarAction.actors, StarAction.actors, ← map_commutator, hz, Subgroup.map_bot]
  by_cases hone : f.factors.count = 1
  · intro i
    have he : P = f.factors.factor i := by
      refine f.factors.generated.trans ?_
      apply le_antisymm
      · refine iSup_le fun j => ?_
        have hji : j = i := Fin.ext (by have := j.isLt; have := i.isLt; omega)
        exact hji ▸ le_rfl
      · exact le_iSup f.factors.factor i
    rw [← he]
    exact le_normalizer_of_normal
  · have htwo : f.factors.count = 2 := by
      have := f.factors.count_pos
      have := f.factors.count_le_two
      omega
    let i : Fin f.factors.count := ⟨0, f.factors.count_pos⟩
    let j : Fin f.factors.count := ⟨1, by omega⟩
    have hij : i ≠ j := by intro he; have := congrArg Fin.val he; change 0 = 1 at this; omega
    have hgen : P = f.factors.factor i ⊔ f.factors.factor j := by
      refine f.factors.generated.trans ?_
      apply le_antisymm
      · refine iSup_le fun k => ?_
        have hk : k = i ∨ k = j := by
          have := k.isLt
          have : k.val = 0 ∨ k.val = 1 := by omega
          exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
        rcases hk with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      · exact sup_le (le_iSup f.factors.factor i) (le_iSup f.factors.factor j)
    have hiH := (f.factors.factor_le i).trans hP
    have hjH := (f.factors.factor_le j).trans hP
    have hgena : a.actors P = a.actors (f.factors.factor i) ⊔ a.actors (f.factors.factor j) := by
      exact (congrArg a.actors hgen).trans (actors_sup a hiH hjH)
    have hcomm := actors_commute a hiH hjH (f.factors.commute i j hij)
    have hdisj := f.factors.support_disjoint i j hij
    have hfix : ⁅a.actors Uγ, a.actors (f.factors.factor j)⁆ = ⊥ := by
      rw [StarAction.actors, StarAction.actors, ← map_commutator,
        f.remaining_fixed j (by simp [j]), Subgroup.map_bot]
    have hnUi : a.actors Uγ ≤ normalizer (a.actors (f.factors.factor i) : Set _) :=
      normalizes_other_factor _ _ _ _ hgena hcomm hdisj (actors_coprime a hf f.factors j)
        (hUVa.trans hnP)
        ((commutator_eq_bot_iff_le_centralizer.mp hfix).trans (centralizer_le_normalizer _))
    have hmove : ⁅a.actors Uγ, a.actors (f.factors.factor i)⁆ ≠ ⊥ := by
      intro hz
      apply f.first_moved
      apply Subgroup.map_injective hf
      simpa only [map_commutator, Subgroup.map_bot, StarAction.actors] using hz
    have hcard : Nat.card (a.actors (f.factors.factor i)) = 5 :=
      (card_map_of_injective hf).trans (f.factors.star_card i)
    have hcommFirst : ⁅a.actors P, a.actors Uγ⁆ = a.actors (f.factors.factor i) :=
      commutator_eq_first _ _ _ _ hgena hcomm hnUi hfix
        (by rw [hcard]; decide) hmove
    have hnVi : a.actors Vγ ≤ normalizer (a.actors (f.factors.factor i) : Set _) := by
      rw [← hcommFirst]
      exact normalizes_commutator _ _ _ hnP
        ((commutator_eq_bot_iff_le_centralizer.mp hcVU).trans (centralizer_le_normalizer _))
    have hnVj : a.actors Vγ ≤ normalizer (a.actors (f.factors.factor j) : Set _) :=
      normalizes_other_factor _ _ _ _ (hgena.trans (sup_comm _ _))
        ((commutator_comm _ _).trans hcomm) hdisj.symm (actors_coprime a hf f.factors i) hnP hnVi
    intro k
    have hk : k = i ∨ k = j := by
      have := k.isLt
      have : k.val = 0 ∨ k.val = 1 := by omega
      exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
    rcases hk with rfl | rfl
    · exact star_normalizes_of_actors a hf _ _ hnVi
    · exact star_normalizes_of_actors a hf _ _ hnVj


/-- The rank-one subgroup also normalizes the first canonical starred factor. -/
theorem RankOneFactors.star_normalizes_first
    (a : StarAction H UH V₁) (hf : Function.Injective a.action)
    {P Uγ Vγ : Subgroup G} (f : RankOneFactors a P Uγ)
    (hP : P ≤ H) (hPn : (Source.starImage H P).Normal)
    (hUV : Uγ ≤ Vγ) (hV : Vγ ≤ H)
    (hVc : IsMulCommutative (Source.starImage H Vγ)) :
    Source.starImage H Uγ ≤ normalizer
      (Source.starImage H (f.factors.factor ⟨0, f.factors.count_pos⟩) : Set _) :=
  (Subgroup.map_mono (subgroupOf_mono H hUV)).trans
    (f.star_normalizes_factors a hf hP hPn hUV hV hVc ⟨0, f.factors.count_pos⟩)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five

end
