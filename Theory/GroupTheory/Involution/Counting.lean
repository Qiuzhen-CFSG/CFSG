module

public import Theory.GroupTheory.Involution.Basic
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.OddKernelInvolutionFibers
public import Mathlib.Data.Set.Card

/-!
# Counting involutions in subgroups and odd central quotients

A Sylow two-normalizer has exactly the involutions of its normal Sylow
subgroup. A surjective homomorphism with central odd kernel induces a
bijection on involutions, also within every subgroup containing the kernel.
Existence of lifts comes from coprime Sylow lifting; uniqueness follows
from conjugacy of involutions in an odd-kernel fiber and centrality.

These elementary counting tools are used with the concrete Bender root
groups in GLS, Volume 4, Chapter 4, Lemma 3.2(b), and the central quotients
in Chapter 2, Corollary 7.14.
-/

open BenderSuzuki.PFAppendixIII
open Subgroup
namespace Theory.GroupTheory

/-- Group equivalences preserve the number of involutions. -/
public theorem involution_card_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card {x : G // IsInvolution x} = Nat.card {x : H // IsInvolution x} := by
  apply Nat.card_congr
  exact Equiv.subtypeEquiv e.toEquiv (fun x => by
    change (x ≠ 1 ∧ x ^ 2 = 1) ↔ (e x ≠ 1 ∧ (e x) ^ 2 = 1)
    simp only [← map_pow, ← e.map_one, e.injective.eq_iff]
    exact and_congr (not_congr e.injective.eq_iff).symm Iff.rfl)

/-- Exclude the identity from the square-one elements. -/
public theorem involution_card_eq_square_card_sub_one {G : Type*} [Group G] [Finite G] :
    Nat.card {x : G // IsInvolution x} = Nat.card {x : G // x ^ 2 = 1} - 1 := by
  change Nat.card ↥{x : G | IsInvolution x} = Nat.card ↥{x : G | x ^ 2 = 1} - 1
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  have he : {x : G | IsInvolution x} = {x : G | x ^ 2 = 1} \ {1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff, IsInvolution]
    exact and_comm
  rw [he, Set.ncard_sdiff_singleton_of_mem (by simp)]

/-- In an exponent-two group every nonidentity element is an involution. -/
public theorem involution_card_eq_of_exponent_two {G : Type*} [Group G] [Finite G]
    (hG : ∀ x : G, x ^ 2 = 1) : Nat.card {x : G // IsInvolution x} = Nat.card G - 1 := by
  rw [involution_card_eq_square_card_sub_one]
  congr 1
  exact Nat.card_congr {
    toFun := fun x => x.val
    invFun := fun x => ⟨x, hG x⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Count in a subgroup containing every involution. -/
public theorem involution_card_eq_of_containment {G : Type*} [Group G] (S : Subgroup G)
    (hS : ∀ x : G, IsInvolution x → x ∈ S) :
    Nat.card {x : G // IsInvolution x} = Nat.card {x : S // IsInvolution x} := by
  apply Nat.card_congr
  exact {
    toFun := fun x => ⟨⟨x, hS x x.property⟩,
      (fun h => x.property.1 (congrArg Subtype.val h)), Subtype.ext x.property.2⟩
    invFun := fun x => ⟨x.val.val,
      (fun h => x.property.1 (Subtype.ext h)), congrArg Subtype.val x.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Every involution lies in a normal Sylow two-subgroup. -/
public theorem involution_mem_normal_sylow {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) [(S : Subgroup G).Normal] {x : G} (hx : IsInvolution x) : x ∈ S := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (by
    rw [Nat.card_zpowers, orderOf_eq_prime hx.2 hx.1]
    exact (pow_one 2).symm)
  have he := S.is_maximal' (hp.to_sup_of_normal_right S.isPGroup') le_sup_right
  exact (show zpowers x ≤ (S : Subgroup G) from sup_eq_right.mp he) (mem_zpowers x)

/-- A Sylow two-normalizer has the involution count of any ambient Sylow two-subgroup. -/
public theorem involution_card_normalizer {G : Type*} [Group G] [Finite G]
    (S T : Sylow 2 G) :
    Nat.card {x : normalizer (S : Set G) // IsInvolution x} =
      Nat.card {x : T // IsInvolution x} := by
  let P := S.subtype (N := normalizer (S : Set G)) le_normalizer
  have : (P : Subgroup (normalizer (S : Set G))).Normal := normal_in_normalizer
  rw [involution_card_eq_of_containment (P : Subgroup _) (fun _ hx =>
    involution_mem_normal_sylow P hx)]
  exact involution_card_congr ((subgroupOfEquivOfLe le_normalizer).trans (S.equiv T))

/-- An odd kernel cannot kill an involution. -/
public theorem involution_map_of_odd_kernel {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hodd : Odd (Nat.card f.ker)) {x : G} (hx : IsInvolution x) :
    IsInvolution (f x) := by
  let := IsElementaryAbelian.zpowers_of_pow_eq_one hx.2
  have hi := injective_comp_subtype_of_coprime_ker f hodd.coprime_two_left
    (zpowers x) (IsElementaryAbelian.isPGroup 2 _)
  refine ⟨?_, by rw [← map_pow, hx.2, map_one]⟩
  intro h
  have he : (⟨x, mem_zpowers x⟩ : zpowers x) = 1 := hi (by simpa using h)
  exact hx.1 (congrArg Subtype.val he)

/-- Every involution lifts through a surjective homomorphism with odd kernel. -/
public theorem exists_involution_lift_of_odd_kernel {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    {y : H} (hy : IsInvolution y) : ∃ x : G, IsInvolution x ∧ f x = y := by
  let := IsElementaryAbelian.zpowers_of_pow_eq_one hy.2
  obtain ⟨A, hA, hmap, _⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    f hf hodd.coprime_two_left (zpowers y)
  have hyA : y ∈ A.map f := hmap.symm ▸ mem_zpowers y
  obtain ⟨x, hx, hxy⟩ := hyA
  let := hA
  exact ⟨x, ⟨fun he => hy.1 (by rw [← hxy, he, map_one]),
    elemPow_eq_one_of_isElementaryAbelian x hx⟩, hxy⟩

/-- Centrality makes each odd-kernel involution fiber a singleton. -/
public theorem involution_eq_of_central_odd_kernel {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hodd : Odd (Nat.card f.ker)) (hcentral : f.ker ≤ center G)
    {x y : G} (hx : IsInvolution x) (hy : IsInvolution y) (he : f x = f y) : x = y := by
  obtain ⟨g, hg⟩ := involutions_same_image_conj_ker f hodd.coprime_two_left
    (orderOf_eq_prime hx.2 hx.1) (orderOf_eq_prime hy.2 hy.1) he
  have hc := mem_center_iff.mp (hcentral g.property) x
  rw [← hc, mul_inv_cancel_right] at hg
  exact hg

/-- Involution cardinality is unchanged by a central odd quotient, within each subgroup containing the kernel. -/
public theorem involution_card_map_of_central_odd_kernel {G H : Type*}
    [Group G] [Finite G] [Group H] (f : G →* H) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) (hcentral : f.ker ≤ center G)
    (B : Subgroup G) (hB : f.ker ≤ B) :
    Nat.card {x : B // IsInvolution x} = Nat.card {x : B.map f // IsInvolution x} := by
  let F : {x : B // IsInvolution x} → {x : B.map f // IsInvolution x} := fun x =>
    ⟨⟨f x.val.val, mem_map_of_mem f x.val.property⟩, by
      have hx : IsInvolution x.val.val :=
        ⟨fun he => x.property.1 (Subtype.ext he), congrArg Subtype.val x.property.2⟩
      have hfx := involution_map_of_odd_kernel f hodd hx
      exact ⟨fun he => hfx.1 (congrArg Subtype.val he), Subtype.ext hfx.2⟩⟩
  apply Nat.card_congr (Equiv.ofBijective F ?_)
  constructor
  · intro x y he
    apply Subtype.ext
    apply Subtype.ext
    apply involution_eq_of_central_odd_kernel f hodd hcentral
      ⟨fun he => x.property.1 (Subtype.ext he), congrArg Subtype.val x.property.2⟩
      ⟨fun he => y.property.1 (Subtype.ext he), congrArg Subtype.val y.property.2⟩
    exact congrArg (fun z => z.val.val) he
  · intro y
    have hy : IsInvolution y.val.val :=
      ⟨fun he => y.property.1 (Subtype.ext he), congrArg Subtype.val y.property.2⟩
    obtain ⟨x, hx, hxy⟩ := exists_involution_lift_of_odd_kernel f hf hodd hy
    have hxB : x ∈ B := by
      have hm : x ∈ (B.map f).comap f := by
        change f x ∈ B.map f
        rw [hxy]
        exact y.val.property
      rwa [comap_map_eq_self hB] at hm
    exact ⟨⟨⟨x, hxB⟩, ⟨fun he => hx.1 (congrArg Subtype.val he), Subtype.ext hx.2⟩⟩,
      Subtype.ext (Subtype.ext hxy)⟩
end Theory.GroupTheory
