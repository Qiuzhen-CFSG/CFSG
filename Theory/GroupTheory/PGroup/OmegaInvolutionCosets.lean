module

public import Theory.GroupTheory.PGroup.OmegaCyclicImage
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.ElementaryAbelian.Join

/-!
# Omega subgroups with one extra involution coset

Let U be an elementary abelian two-subgroup. If every involution centralizes U
and all involutions outside U belong to one U-coset, then the first omega is
U or the elementary join of U with one additional involution. In particular,
its order is the order of U or twice that order.

The proof uses the defining generators of omega, so it does not require U to
be normal in the whole group. This is the group-theoretic counting step in
Parrott's outer-centralizer calculation (1972, pp.675–676).
-/

open Subgroup

namespace Subgroup

/-- One possible extra coset of involutions gives an elementary omega with
at most twice the order of the given elementary subgroup. -/
public theorem omega₁_elementary_card_of_involution_cosets
    {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hcentral : ∀ a : G, a ^ 2 = 1 → a ∈ centralizer (U : Set G))
    (hcoset : ∀ a b : G, a ^ 2 = 1 → b ^ 2 = 1 →
      a ∉ U → b ∉ U → a⁻¹ * b ∈ U) :
    IsElementaryAbelian 2 (omega₁ G (p := 2)) ∧
      (Nat.card (omega₁ G (p := 2)) = Nat.card U ∨
        Nat.card (omega₁ G (p := 2)) = 2 * Nat.card U) := by
  classical
  have hU : U ≤ omega₁ G (p := 2) := elementaryAbelian_le_omega₁
  by_cases hex : ∃ a : G, a ^ 2 = 1 ∧ a ∉ U
  · obtain ⟨a, ha2, haU⟩ := hex
    let V := zpowers a ⊔ U
    let : IsElementaryAbelian 2 (zpowers a) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one ha2
    have haC := hcentral a ha2
    let : IsElementaryAbelian 2 V := IsElementaryAbelian.sup_of_le_centralizer
      (le_centralizer_iff.mpr (zpowers_le.mpr haC))
    have heq : omega₁ G (p := 2) = V := by
      apply le_antisymm
      · refine (closure_le _).mpr ?_
        intro b hb
        change b ∈ V
        have hb2 : b ^ 2 = 1 := by simpa only [Set.mem_ofPred_eq, pow_one] using hb
        by_cases hbU : b ∈ U
        · exact (le_sup_right : U ≤ V) hbU
        · have hmul := V.mul_mem
            ((le_sup_left : zpowers a ≤ V) (mem_zpowers a))
            ((le_sup_right : U ≤ V) (hcoset a b ha2 hb2 haU hbU))
          simpa only [mul_inv_cancel_left] using hmul
      · exact sup_le (zpowers_le.mpr (subset_closure (by
          simpa only [Set.mem_ofPred_eq, pow_one] using ha2))) hU
    rw [heq]
    refine ⟨inferInstance, Or.inr ?_⟩
    simpa only [V, sup_comm] using card_sup_zpowers_of_normalizing_involution
      U a ha2 haU ((centralizer_le_normalizer _) haC)
  · have heq : omega₁ G (p := 2) = U := by
      apply le_antisymm _ hU
      refine (closure_le _).mpr ?_
      intro a ha
      by_contra haU
      exact hex ⟨a, by simpa only [Set.mem_ofPred_eq, pow_one] using ha, haU⟩
    rw [heq]
    exact ⟨inferInstance, Or.inl rfl⟩

/-- A central involution with nontrivial cyclic image doubles the elementary
kernel omega obtained from the one-extra-coset criterion. -/
public theorem omega₁_elementary_card_of_cyclic_image_involution_cosets
    {G K : Type*} [Group G] [Finite G] [Group K] [Finite K] [IsCyclic K]
    (f : G →* K) (y : G) (hy : y ^ 2 = 1)
    (hycentral : ∀ a : G, Commute a y) (hfy : orderOf (f y) = 2)
    (U : Subgroup G) [IsElementaryAbelian 2 U] (hU : U ≤ f.ker)
    (hcentral : ∀ a : G, a ∈ f.ker → a ^ 2 = 1 →
      a ∈ centralizer (U : Set G))
    (hcoset : ∀ a b : G, a ∈ f.ker → b ∈ f.ker →
      a ^ 2 = 1 → b ^ 2 = 1 → a ∉ U → b ∉ U → a⁻¹ * b ∈ U) :
    IsElementaryAbelian 2 (omega₁ G (p := 2)) ∧
      (Nat.card (omega₁ G (p := 2)) = 2 * Nat.card U ∨
        Nat.card (omega₁ G (p := 2)) = 4 * Nat.card U) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U₀ := U.subgroupOf f.ker
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.subgroupOf hU
  have hcent₀ (a : f.ker) (ha : a ^ 2 = 1) : a ∈ centralizer (U₀ : Set f.ker) := by
    intro b hb
    exact Subtype.ext (hcentral a a.property (congrArg f.ker.subtype ha) b hb)
  have hcoset₀ (a b : f.ker) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
      (haU : a ∉ U₀) (hbU : b ∉ U₀) : a⁻¹ * b ∈ U₀ :=
    hcoset a b a.property b.property (congrArg f.ker.subtype ha)
      (congrArg f.ker.subtype hb) haU hbU
  obtain ⟨hW, hcard⟩ := omega₁_elementary_card_of_involution_cosets U₀ hcent₀ hcoset₀
  let : IsElementaryAbelian 2 (omega₁ f.ker (p := 2)) := hW
  let W := (omega₁ f.ker (p := 2)).map f.ker.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map f.ker.subtype
  let : IsElementaryAbelian 2 (zpowers y) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hy
  have hyC : y ∈ centralizer (W : Set G) := fun a _ => hycentral a
  have hyW : y ∉ W := by
    intro hh
    have hker : y ∈ f.ker := (map_subtype_le _) hh
    have hne : f y ≠ 1 := by
      intro heq
      rw [heq, orderOf_one] at hfy
      omega
    exact hne hker
  have hsplit := omega₁_eq_sup_kernel_omega_of_central_involution f y hy hycentral hfy
  change omega₁ G (p := 2) = zpowers y ⊔ W at hsplit
  let : IsElementaryAbelian 2 (zpowers y ⊔ W : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer
      (le_centralizer_iff.mpr (zpowers_le.mpr hyC))
  have hdouble : Nat.card (omega₁ G (p := 2)) = 2 * Nat.card W := by
    rw [hsplit, sup_comm]
    exact card_sup_zpowers_of_normalizing_involution W y hy hyW
      (centralizer_le_normalizer _ hyC)
  have hWcard : Nat.card W = Nat.card (omega₁ f.ker (p := 2)) :=
    card_map_of_injective f.ker.subtype_injective
  have hUcard : Nat.card U₀ = Nat.card U :=
    Nat.card_congr (subgroupOfEquivOfLe hU).toEquiv
  refine ⟨by rw [hsplit]; infer_instance, ?_⟩
  rw [hdouble, hWcard]
  rw [hUcard] at hcard
  rcases hcard with hc | hc
  · exact Or.inl (congrArg (2 * ·) hc)
  · exact Or.inr (by rw [hc]; omega)

end Subgroup
