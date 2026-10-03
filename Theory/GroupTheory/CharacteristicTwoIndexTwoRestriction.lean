module

public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.IndexTwoCoprimeAutomorphism

/-!
# Restriction to a subgroup of index two in the two-core

In a finite group with self-centralizing two-core, the centralizer of a
subgroup of index two in that core is a two-group. Consequently, when the
subgroup is normal, its Frattini action has two-group kernel.

An automorphism fixing an index-two subgroup pointwise has displacement in
that subgroup. Iterating shows that its order divides the subgroup order.
Apply this to conjugation on the two-core, then use self-centralization and
Burnside's Frattini kernel theorem. This is an elementary restriction argument.
-/

open Subgroup
namespace Subgroup

/-- Pointwise fixation of an index-two subgroup bounds the automorphism order
by the subgroup order. -/
public theorem pow_card_eq_one_of_fixed_index_two
    {G : Type*} [Group G] [Finite G] (R : Subgroup G) (hi : R.index = 2)
    (e : MulAut G) (hfixed : ∀ x ∈ R, e x = x) : e ^ Nat.card R = 1 := by
  have hmem (x : G) : e x ∈ R ↔ x ∈ R := by
    constructor
    · intro hx
      have heq := hfixed (e x) hx
      exact e.injective heq ▸ hx
    · intro hx
      exact (hfixed x hx).symm ▸ hx
  apply MulEquiv.ext
  intro x
  let d := x⁻¹ * e x
  have hd : d ∈ R := by
    rw [R.mul_mem_iff_of_index_two hi]
    simp only [R.inv_mem_iff, hmem]
  have hdfixed : e d = d := hfixed d hd
  have hstep : e x = x * d := by simp [d]
  have hiter (n : ℕ) : (e ^ n) x = x * d ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hdfixed, hstep]
      simp [pow_succ', mul_assoc]
  have hdcard : d ^ Nat.card R = 1 := congrArg Subtype.val (pow_card_eq_one' (x := (⟨d, hd⟩ : R)))
  simpa [hdcard] using hiter (Nat.card R)

/-- Centralizing an index-two subgroup of a self-centralizing two-core forces
an element to have two-power order. -/
public theorem centralizer_isPGroup_of_index_two_in_core
    {G : Type*} [Group G] [Finite G]
    (hcentral : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (R : Subgroup G)
    (hi : (R.subgroupOf (pCore 2 G)).index = 2) :
    IsPGroup 2 (centralizer (R : Set G)) := by
  let Q := pCore 2 G
  let T := R.subgroupOf Q
  have hT : IsPGroup 2 T := pCore_isPGroup.to_subgroup T
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  intro c
  let e : MulAut Q := MulAut.conjNormal (c : G)
  have he : e ^ Nat.card T = 1 := pow_card_eq_one_of_fixed_index_two T hi e (by
    intro x hx
    apply Subtype.ext
    change (c : G) * (x : G) * (c : G)⁻¹ = (x : G)
    have hc := mem_centralizer_iff.mp c.property (x : G) hx
    rw [← hc, mul_inv_cancel_right])
  have hcQ : (c : G) ^ 2 ^ n ∈ Q := by
    apply hcentral
    rw [mem_centralizer_iff]
    intro q hq
    have hh := congrArg (fun a : MulAut Q => (a ⟨q, hq⟩ : G)) he
    rw [hn, ← map_pow] at hh
    change (c : G) ^ 2 ^ n * q * ((c : G) ^ 2 ^ n)⁻¹ = q at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  obtain ⟨m, hm⟩ := (pCore_isPGroup (p := 2) (G := G)) ⟨_, hcQ⟩
  refine ⟨n + m, ?_⟩
  apply Subtype.ext
  change (c : G) ^ 2 ^ (n + m) = 1
  rw [pow_add, pow_mul]
  exact congrArg Subtype.val hm

/-- The Frattini action on a normal subgroup of index two in the two-core
has two-group kernel. -/
public theorem frattini_kernel_isPGroup_of_index_two_in_core
    {G : Type*} [Group G] [Finite G]
    (hcentral : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (R : Subgroup G) [R.Normal] (hRQ : R ≤ pCore 2 G)
    (hi : (R.subgroupOf (pCore 2 G)).index = 2) :
    IsPGroup 2 (((quotientAut (frattini R)).comp
      (MulAut.conjNormal : G →* MulAut R)).ker) := by
  have hR : IsPGroup 2 R := pCore_isPGroup.to_le hRQ
  let f : G →* MulAut R := MulAut.conjNormal
  have hker : f.ker ≤ centralizer (R : Set G) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro r hr
    have hh := congrArg (fun a : MulAut R => (a ⟨r, hr⟩ : G)) hg
    change g * r * g⁻¹ = r at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  exact (isPGroup_quotientAut_frattini_kernel hR).comap_of_ker_isPGroup f
    ((centralizer_isPGroup_of_index_two_in_core hcentral R hi).to_le hker)
end Subgroup
