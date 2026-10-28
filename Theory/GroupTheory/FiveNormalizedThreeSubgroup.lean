module

public import Theory.GroupAction.FrobeniusFiveSmallFixed

/-!
# Five-normalized three-subgroups and a self-centralizing two-group

Let Q be a normal self-centralizing two-subgroup with a nonidentity element
central in the ambient group. An order-five subgroup A with at most four
fixed points on Q cannot normalize a nontrivial three-subgroup T with
trivial A-centralizer. Indeed T A is a Frobenius group, so the small-fixed
Wielandt argument makes T centralize Q. Self-centralization and coprime
orders then give T = 1.

This is the source-neutral local exclusion used in Thompson VI, p.630.
The action formula is proved in `FrobeniusFiveSmallFixed`.
-/

open Subgroup
universe u
namespace Subgroup
/-- A small five-fixed subgroup excludes a fixed-free normalized three-subgroup
when the self-centralizing two-group contains an ambient central element. -/
public theorem three_subgroup_eq_bot_of_small_five_fixed
    {G : Type u} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hcent : centralizer (Q : Set G) ≤ Q)
    (y : Q) (hy : y ≠ 1) (hycentral : (y : G) ∈ center G)
    (A T : Subgroup G) (hA : Nat.card A = 5) (hT : IsPGroup 3 T)
    (hAT : A ≤ normalizer (T : Set G))
    (hfixed : T ⊓ centralizer (A : Set G) = ⊥)
    (hsmall : Nat.card ((centralizer (A : Set G)).subgroupOf Q) ≤ 4) : T = ⊥ := by
  classical
  by_contra hTne
  let H := T ⊔ A
  let K := T.subgroupOf H
  let B := A.subgroupOf H
  have hTH : T ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  let _ : K.Normal := (normal_subgroupOf_iff_le_normalizer hTH).mpr
    (sup_le T.le_normalizer hAT)
  have hK : IsPGroup 3 K := hT.of_equiv (subgroupOfEquivOfLe hTH).symm
  have hBcard : Nat.card B = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv).trans hA
  have hB : IsPGroup 5 B := IsPGroup.of_card (n := 1) (by simpa using hBcard)
  have hdisj : Disjoint K B := hK.disjoint_of_coprime hB (by decide)
  have hsup : K ⊔ B = ⊤ := by
    rw [← subgroupOf_sup hTH hAH]
    exact subgroupOf_self H
  have hcomp : K.IsComplement' B := by
    apply isComplement'_of_disjoint_and_mul_eq_univ hdisj
    rw [← normal_mul, hsup]
    rfl
  have hKne : K ≠ ⊥ := by
    intro he
    apply hTne
    rw [← map_subgroupOf_eq_of_le hTH]
    change K.map H.subtype = ⊥
    rw [he, map_bot]
  have hfixed' : subgroupCentralizerIn K B = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    have hxC : (x : G) ∈ centralizer (A : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      have he := mem_centralizer_iff.mp hx.2 ⟨a, hAH ha⟩ ha
      exact congrArg H.subtype he
    exact show (x : G) ∈ (⊥ : Subgroup G) from hfixed ▸ ⟨hx.1, hxC⟩
  have hfrob : IsFrobeniusGroupWithKernelComplement K B :=
    theorem_3_7_frobenius K B inferInstance hcomp hKne
      (by rw [hBcard]; decide) hfixed'
  let ρ : G →* MulAut Q := MulAut.conjNormal
  let _ : MulDistribMulAction H Q := MulDistribMulAction.compHom Q (ρ.comp H.subtype)
  have hyfix : y ∈ fixedPointSubgroup H Q := by
    intro g
    apply Subtype.ext
    change (g : G) * (y : G) * (g : G)⁻¹ = (y : G)
    exact mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp hycentral g)
  have hcommon : 2 ≤ Nat.card (fixedPointSubgroup H Q) := by
    apply (one_lt_card_iff_ne_bot _).mpr
    intro he
    exact hy (mem_bot.mp (he ▸ hyfix))
  let _ : MulDistribMulAction B Q := MulDistribMulAction.compHom Q B.subtype
  have hfixeq : fixedPointSubgroup B Q = (centralizer (A : Set G)).subgroupOf Q := by
    ext q
    constructor
    · intro hq
      rw [mem_subgroupOf, mem_centralizer_iff]
      intro a ha
      have hh := congrArg Q.subtype (hq ⟨⟨a, hAH ha⟩, ha⟩)
      change a * (q : G) * a⁻¹ = (q : G) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hq b
      apply Subtype.ext
      change (b.val : G) * (q : G) * (b.val : G)⁻¹ = (q : G)
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hq _ b.property)
  have htriv := Wielandt.three_kernel_fixes_two_group_of_small_five_fixed
    K B hfrob hK hBcard hQ hcommon (by
      change Nat.card (fixedPointSubgroup B Q) ≤ 4
      rw [hfixeq]
      exact hsmall)
  have hTC : T ≤ centralizer (Q : Set G) := by
    intro t ht
    rw [mem_centralizer_iff]
    intro q hq
    have hqfix : (⟨q, hq⟩ : Q) ∈ fixedPointSubgroup K Q := htriv ▸ mem_top _
    have he := congrArg Q.subtype (hqfix ⟨⟨t, hTH ht⟩, ht⟩)
    change t * q * t⁻¹ = q at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hd : Disjoint T Q := hT.disjoint_of_coprime hQ (by decide)
  exact hTne (eq_bot_iff.mpr fun _ ht => hd.le_bot ⟨ht, hcent (hTC ht)⟩)
end Subgroup
