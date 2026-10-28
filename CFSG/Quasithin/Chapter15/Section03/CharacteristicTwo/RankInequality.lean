module

public import Stellmacher.MaxElementaryOffenderEquality
public import Theory.Representation.BinaryOffender.Defs

/-!
# The paired-module rank inequality in Section 15.3

For the two normal elementary subgroups `U_L` and `U_L^t` inside `XS`,
uniqueness of their direct-product factorization makes fixed codimensions
add. A maximum elementary subgroup `A` is compared with
`W C_A(W)`, where `W = U_L U_L^t`. Kernel/image counting bounds its
combined action by its quotient image and the two kernel action images.
This proves the inequality (!) on printed p.1133 using actual subgroups
and action kernels, without any assumed dimensions or rank tuples.

Here `rank` is the binary logarithm of a subgroup's order; on the elementary
subgroups in the statement it is their vector-space dimension. The ambient
`G` in the counting lemmas is the local group `XS`, so normality of the
factors is relative to that group. The Section 15.3 owner must construct
these factors and actions from 15.3.32 and identify the quotient kernel.
The later case calculations and characteristic-two exclusion are separate.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of Theorem 15.3.25, printed pp.1133–1134 (PDF pp.1150–1151).
-/

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open Subgroup Stellmacher Representation.BinaryOffender
variable {G H K Q : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [Group K] [Finite K] [Group Q] [Finite Q]

private theorem card_eq_pow_rank (A : Subgroup G) [IsElementaryAbelian 2 A] :
    Nat.card A = 2 ^ rank A := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  simp only [rank, hn, Nat.log_pow Nat.one_lt_two]

private theorem rank_mono {A B : Subgroup G} (h : A ≤ B) : rank A ≤ rank B :=
  Nat.log_mono_right (Nat.card_le_card_of_injective _ (inclusion_injective h))

private theorem rank_kernel_add_rank_image
    (A : Subgroup G) [IsElementaryAbelian 2 A] (f : G →* H) :
    rank (A ⊓ f.ker) + rank (A.map f) = rank A := by
  let : IsElementaryAbelian 2 (A ⊓ f.ker : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have h : Nat.card (A ⊓ f.ker : Subgroup G) * Nat.card (A.map f) = Nat.card A := by
    have ht := relIndex_mul_relIndex (⊥ : Subgroup G) (f.ker ⊓ A) A bot_le inf_le_right
    rw [relIndex_bot_left, inf_relIndex_right, relIndex_ker] at ht
    simpa only [relIndex_bot_left, inf_comm] using ht
  rw [card_eq_pow_rank, card_eq_pow_rank, card_eq_pow_rank, ← pow_add] at h
  exact Nat.pow_right_injective Nat.one_lt_two h

private theorem rank_image_le_quotient_and_kernel
    (A : Subgroup G) [IsElementaryAbelian 2 A] (q : G →* Q) (f : G →* H) :
    rank (A.map f) ≤ rank (A.map q) + rank ((A ⊓ q.ker).map f) := by
  let : IsElementaryAbelian 2 (A ⊓ q.ker : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  have h₁ := rank_kernel_add_rank_image A f
  have h₂ := rank_kernel_add_rank_image A q
  have h₃ := rank_kernel_add_rank_image (A ⊓ q.ker) f
  have h₄ : rank ((A ⊓ q.ker) ⊓ f.ker) ≤ rank (A ⊓ f.ker) :=
    rank_mono (inf_le_inf_right _ inf_le_left)
  omega

omit [Finite G] in
private theorem rank_product_image_le
    (A : Subgroup G) [IsElementaryAbelian 2 A] (f : G →* H) (g : G →* K) :
    rank (A.map (f.prod g)) ≤ rank (A.map f) + rank (A.map g) := by
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  let : IsElementaryAbelian 2 (A.map g) := IsElementaryAbelian.map g
  let : IsElementaryAbelian 2 (A.map (f.prod g)) := IsElementaryAbelian.map (f.prod g)
  let injection : A.map (f.prod g) → (A.map f) × (A.map g) := fun x =>
    ⟨⟨x.val.1, by obtain ⟨a, ha, hx⟩ := x.property; exact ⟨a, ha, congrArg Prod.fst hx⟩⟩,
      ⟨x.val.2, by obtain ⟨a, ha, hx⟩ := x.property; exact ⟨a, ha, congrArg Prod.snd hx⟩⟩⟩
  have hi : Function.Injective injection := by
    intro a b h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun x => (x.1 : H)) h)
      (congrArg (fun x => (x.2 : K)) h)
  have hc := Nat.card_le_card_of_injective injection hi
  rw [Nat.card_prod, card_eq_pow_rank, card_eq_pow_rank,
    card_eq_pow_rank, ← pow_add] at hc
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hc

/-- The cardinal argument on p.1133, before calculating the two module
codimensions. The three terms are the actual quotient image and the two
action images of its kernel in A. -/
private theorem paired_action_rank_bound
    (S W A : Subgroup G) [W.Normal] [IsElementaryAbelian 2 W]
    (hWS : W ≤ S) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (q : G →* Q) (f : G →* H) (g : G →* K)
    (hker : (f.prod g).ker = centralizer (W : Set G)) :
    rank W - rank (W ⊓ centralizer (A : Set G)) ≤
      rank (A.map q) + rank ((A ⊓ q.ker).map f) + rank ((A ⊓ q.ker).map g) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A ⊓ q.ker : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (A.map (f.prod g)) := IsElementaryAbelian.map (f.prod g)
  let : IsElementaryAbelian 2 (W ⊓ centralizer (A : Set G) : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  have h := maxElementary_card_le_fixed_mul_image S W A hWS hA (f.prod g) hker
  rw [card_eq_pow_rank, card_eq_pow_rank, card_eq_pow_rank, ← pow_add] at h
  have hbound := (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp h
  have hquot := rank_image_le_quotient_and_kernel A q (f.prod g)
  have hprod := rank_product_image_le (A ⊓ q.ker) f g
  omega

omit [Finite G] in
private theorem card_of_factorization (W U V : Subgroup G)
    (hU : U ≤ W) (hV : V ≤ W) (hd : Disjoint U V)
    (hgen : ∀ w ∈ W, ∃ u ∈ U, ∃ v ∈ V, u * v = w) :
    Nat.card W = Nat.card U * Nat.card V := by
  let f : U × V → W := fun x => ⟨x.1 * x.2, W.mul_mem (hU x.1.property) (hV x.2.property)⟩
  have hi : Function.Injective f := fun _ _ h =>
    mul_injective_of_disjoint hd (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro w
    obtain ⟨u, hu, v, hv, he⟩ := hgen w w.property
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), Subtype.ext he⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)).symm.trans (Nat.card_prod U V)

omit [Finite G] in
private theorem fixed_factors (U V A : Subgroup G) [U.Normal] [V.Normal]
    (hd : Disjoint U V) (u : U) (v : V)
    (hfix : (u : G) * v ∈ centralizer (A : Set G)) :
    (u : G) ∈ centralizer (A : Set G) ∧ (v : G) ∈ centralizer (A : Set G) := by
  have h (a : G) (ha : a ∈ A) :
      ((MulAut.conjNormal a u : U), (MulAut.conjNormal a v : V)) = (u, v) := by
    apply mul_injective_of_disjoint hd
    change (a * (u : G) * a⁻¹) * (a * (v : G) * a⁻¹) = (u : G) * v
    calc
      _ = a * ((u : G) * v) * a⁻¹ := by simp [mul_assoc]
      _ = _ := mul_inv_eq_iff_eq_mul.mpr (hfix a ha)
  constructor
  · intro a ha
    have hh := congrArg (fun x : U × V => (x.1 : G)) (h a ha)
    exact mul_inv_eq_iff_eq_mul.mp hh
  · intro a ha
    have hh := congrArg (fun x : U × V => (x.2 : G)) (h a ha)
    exact mul_inv_eq_iff_eq_mul.mp hh

/-- Fixed codimensions add for the two genuine invariant direct factors.
No prescribed dimensions or offender type enters this calculation. -/
public theorem paired_fixed_codimension (U V A : Subgroup G) [U.Normal] [V.Normal]
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hc : V ≤ centralizer (U : Set G)) (hd : Disjoint U V) :
    rank (U ⊔ V) - rank ((U ⊔ V) ⊓ centralizer (A : Set G)) =
      (rank U - rank (U ⊓ centralizer (A : Set G))) +
      (rank V - rank (V ⊓ centralizer (A : Set G))) := by
  let : IsElementaryAbelian 2 (U ⊔ V : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hc
  let : IsElementaryAbelian 2 (U ⊓ centralizer (A : Set G) : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (V ⊓ centralizer (A : Set G) : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 ((U ⊔ V) ⊓ centralizer (A : Set G) : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  have hcard := card_of_factorization (U ⊔ V) U V le_sup_left le_sup_right hd
    (fun _ hw => mem_sup_of_normal_right.mp hw)
  have hfixed := card_of_factorization
    ((U ⊔ V) ⊓ centralizer (A : Set G))
    (U ⊓ centralizer (A : Set G)) (V ⊓ centralizer (A : Set G))
    (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)
    (hd.mono inf_le_left inf_le_left) (by
      intro w hw
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_sup_of_normal_right.mp hw.1
      obtain ⟨huf, hvf⟩ := fixed_factors U V A hd ⟨u, hu⟩ ⟨v, hv⟩ hw.2
      exact ⟨u, ⟨hu, huf⟩, v, ⟨hv, hvf⟩, rfl⟩)
  rw [card_eq_pow_rank, card_eq_pow_rank, card_eq_pow_rank, ← pow_add] at hcard hfixed
  have hdim := Nat.pow_right_injective Nat.one_lt_two hcard
  have hfixdim := Nat.pow_right_injective Nat.one_lt_two hfixed
  have hU : rank (U ⊓ centralizer (A : Set G)) ≤ rank U := rank_mono inf_le_left
  have hV : rank (V ⊓ centralizer (A : Set G)) ≤ rank V := rank_mono inf_le_left
  omega

omit [Finite G] [Finite H] [Finite K] in
private theorem paired_action_kernel
    (U V : Subgroup G) [V.Normal] (f : G →* H) (g : G →* K)
    (hf : f.ker = centralizer (U : Set G))
    (hg : g.ker = centralizer (V : Set G)) :
    (f.prod g).ker = centralizer ((U ⊔ V : Subgroup G) : Set G) := by
  rw [MonoidHom.ker_prod, hf, hg]
  ext x
  constructor
  · intro hx
    apply (mem_centralizer_iff).mpr
    intro w hw
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_sup_of_normal_right.mp hw
    rw [mul_assoc, hx.2 v hv, ← mul_assoc, hx.1 u hu, mul_assoc]
  · intro hx
    exact ⟨fun u hu => hx u (mem_sup_left hu), fun v hv => hx v (mem_sup_right hv)⟩

/-- The source inequality (!) on p.1133. The factors are actual normal
subgroups, and f and g have their actual conjugation kernels. This is
applicable inside XS, where U and V are UL and its conjugate. -/
public theorem paired_offender_rank_inequality
    (S U V A : Subgroup G) [U.Normal] [V.Normal]
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hUS : U ≤ S) (hVS : V ≤ S) (hc : V ≤ centralizer (U : Set G))
    (hd : Disjoint U V) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (q : G →* Q) (f : G →* H) (g : G →* K)
    (hf : f.ker = centralizer (U : Set G))
    (hg : g.ker = centralizer (V : Set G)) :
    (rank U - rank (U ⊓ centralizer (A : Set G))) +
        (rank V - rank (V ⊓ centralizer (A : Set G))) ≤
      rank (A.map q) + rank (A.map f ⊓ q.ker.map f) + rank ((A ⊓ q.ker).map g) := by
  let : IsElementaryAbelian 2 (U ⊔ V : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hc
  have hker := paired_action_kernel U V f g hf hg
  rw [← paired_fixed_codimension U V A hc hd]
  have h := paired_action_rank_bound S (U ⊔ V) A (sup_le hUS hVS) hA q f g hker
  have hmap : (A ⊓ q.ker).map f ≤ A.map f ⊓ q.ker.map f := by
    exact le_inf (map_mono inf_le_left) (map_mono inf_le_right)
  have hr := rank_mono hmap
  omega

/-- Equality in the paired bound makes `W C_A(W)` a maximum elementary
subgroup. This is the replacement needed after the surviving offender
case on p.1134; its numerical bound still has to be calculated in the
actual two modules. -/
public theorem paired_replacement_mem_max
    (S U V A : Subgroup G) [U.Normal] [V.Normal]
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hUS : U ≤ S) (hVS : V ≤ S) (hc : V ≤ centralizer (U : Set G))
    (hd : Disjoint U V) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (q : G →* Q) (f : G →* H) (g : G →* K)
    (hf : f.ker = centralizer (U : Set G))
    (hg : g.ker = centralizer (V : Set G))
    (hbound : rank (A.map q) + rank (A.map f ⊓ q.ker.map f) +
        rank ((A ⊓ q.ker).map g) ≤
      (rank U - rank (U ⊓ centralizer (A : Set G))) +
        (rank V - rank (V ⊓ centralizer (A : Set G)))) :
    (U ⊔ V) ⊔ (A ⊓ centralizer ((U ⊔ V : Subgroup G) : Set G)) ∈
      elementaryAbelianMaxSubgroups S := by
  let W := U ⊔ V
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.sup_of_le_centralizer hc
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A ⊓ q.ker : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (A.map (f.prod g)) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (W ⊓ centralizer (A : Set G) : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  have hker := paired_action_kernel U V f g hf hg
  have hsharp := maxElementary_card_bound_and_eq S W A (sup_le hUS hVS) hA.1 0
    (by simpa using (maxOrder_eq_card_of_mem S A hA).symm) (f.prod g) hker
  apply hsharp.2
  have hcard := hsharp.1
  simp only [pow_zero, mul_one] at hcard ⊢
  rw [card_eq_pow_rank, card_eq_pow_rank, card_eq_pow_rank, ← pow_add] at hcard ⊢
  have hlower := (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hcard
  have hquot := rank_image_le_quotient_and_kernel A q (f.prod g)
  have hprod := rank_product_image_le (A ⊓ q.ker) f g
  have hmap : (A ⊓ q.ker).map f ≤ A.map f ⊓ q.ker.map f :=
    le_inf (map_mono inf_le_left) (map_mono inf_le_right)
  have hr := rank_mono hmap
  rw [← paired_fixed_codimension U V A hc hd] at hbound
  have hfix : rank (W ⊓ centralizer (A : Set G)) ≤ rank W := rank_mono inf_le_left
  congr 1
  change rank (A.map q) + rank (A.map f ⊓ q.ker.map f) +
    rank ((A ⊓ q.ker).map g) ≤ rank W - rank (W ⊓ centralizer (A : Set G)) at hbound
  omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
