module

public import Theory.GroupTheory.PiCore
public import Mathlib.GroupTheory.PGroup

/-!
# Automorphisms preserving a homomorphism

For a homomorphism d from a finite group, restrict the automorphisms satisfying
`d ∘ a = d` to its kernel. Automorphisms in the restriction kernel embed in
functions to ker(d) by `a ↦ (x ↦ x⁻¹a(x))`. Thus a p-group kernel makes the
restriction kernel a p-group. This proves both p-group and π-group extension
criteria without requiring ker(d) to be characteristic.

Source: the standard subgroup-and-quotient automorphism argument; applied to
determinants in Aschbacher–Smith A.1.26, printed pp.25–26.
-/

open Subgroup

namespace MonoidHom
variable {P D : Type*} [Group P] [Group D] (d : P →* D)

/-- Automorphisms preserving every value of the homomorphism. -/
@[expose] public def fixingAut : Subgroup (MulAut P) where
  carrier := {a | ∀ x, d (a x) = d x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro a b ha hb x; exact (ha (b x)).trans (hb x)
  inv_mem' := by
    intro a ha x
    exact (ha (a⁻¹ x)).symm.trans (congrArg d (a.apply_symm_apply x))

/-- Restriction of value-preserving automorphisms to the kernel. -/
public def fixingAutRestriction : d.fixingAut →* MulAut d.ker where
  toFun a := {
    toFun x := ⟨a.val x, (a.property x).trans x.property⟩
    invFun x := ⟨a.val.symm x, ((d.fixingAut).inv_mem a.property x).trans x.property⟩
    left_inv x := Subtype.ext (a.val.symm_apply_apply x)
    right_inv x := Subtype.ext (a.val.apply_symm_apply x)
    map_mul' x y := Subtype.ext (a.val.map_mul x y) }
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

private theorem fixes_kernel (a : d.fixingAutRestriction.ker) (x : d.ker) :
    a.val.val x = x := by
  exact congrArg Subtype.val (DFunLike.congr_fun a.property x)

private def fixingAutDisplacement : d.fixingAutRestriction.ker →* (P → d.ker) where
  toFun a x := ⟨x⁻¹ * a.val.val x, by
    change d (x⁻¹ * a.val.val x) = 1
    rw [map_mul, map_inv, a.val.property x, inv_mul_cancel]⟩
  map_one' := by funext x; apply Subtype.ext; simp
  map_mul' a b := by
    funext x
    apply Subtype.ext
    change x⁻¹ * a.val.val (b.val.val x) =
      (x⁻¹ * a.val.val x) * (x⁻¹ * b.val.val x)
    have hd : x⁻¹ * b.val.val x ∈ d.ker := by
      change d (x⁻¹ * b.val.val x) = 1
      rw [map_mul, map_inv, b.val.property x, inv_mul_cancel]
    have ha := fixes_kernel d a ⟨x⁻¹ * b.val.val x, hd⟩
    change a.val.val (x⁻¹ * b.val.val x) = x⁻¹ * b.val.val x at ha
    rw [map_mul, map_inv] at ha
    calc
      _ = x⁻¹ * (a.val.val x * (a.val.val x)⁻¹ * a.val.val (b.val.val x)) := by simp
      _ = _ := by rw [mul_assoc (a.val.val x), ha, mul_assoc]

private theorem fixingAutDisplacement_injective : Function.Injective d.fixingAutDisplacement := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  ext x
  exact mul_left_cancel (congrArg Subtype.val (congrFun h x))

/-- The restriction kernel embeds by displacement into functions to the p-kernel. -/
public theorem isPGroup_fixingAutRestriction_ker [Finite P] {p : ℕ}
    (hP : IsPGroup p d.ker) : IsPGroup p d.fixingAutRestriction.ker := by
  have hf : IsPGroup p (P → d.ker) := by
    obtain ⟨k, hk⟩ := isPGroup_iff_exists_pow_pow_eq_one.mp hP
    intro f
    exact ⟨k, funext (fun x => hk (f x))⟩
  exact hf.of_injective d.fixingAutDisplacement d.fixingAutDisplacement_injective

/-- A p-kernel with p-group automorphisms has a p-group of value-preserving automorphisms. -/
public theorem isPGroup_fixingAut [Finite P] {p : ℕ}
    (hP : IsPGroup p d.ker) (hA : IsPGroup p (MulAut d.ker)) :
    IsPGroup p d.fixingAut := by
  have ht := (hA.to_subgroup ⊤).comap_of_ker_isPGroup d.fixingAutRestriction
    (d.isPGroup_fixingAutRestriction_ker hP)
  rw [Subgroup.comap_top] at ht
  exact ht.of_surjective (⊤ : Subgroup d.fixingAut).subtype
    (fun a => ⟨⟨a, mem_top a⟩, rfl⟩)

/-- Value-preserving automorphisms form a π-group when their restriction does. -/
public theorem isPiGroup_fixingAut [Finite P] {p : ℕ} [Fact p.Prime]
    {π : Set Nat.Primes} (hp : ⟨p, Fact.out⟩ ∈ π)
    (hP : IsPGroup p d.ker) (hA : IsPiGroup π (MulAut d.ker)) :
    IsPiGroup π d.fixingAut := by
  let r := d.fixingAutRestriction
  have hK : IsPiGroup π r.ker := by
    rw [IsPiGroup_iff]
    obtain ⟨n, hn⟩ := (d.isPGroup_fixingAutRestriction_ker hP).exists_card_eq
    intro q hq
    rw [hn] at hq
    have he : q.val = p := (Nat.prime_dvd_prime_iff_eq q.property (Fact.out : p.Prime)).mp
      (q.property.dvd_of_dvd_pow hq)
    have : q = ⟨p, Fact.out⟩ := Subtype.ext he
    exact this ▸ hp
  exact IsPiGroup.of_normal_subgroup_and_quotient r.ker (hK.isPiSubgroup r.ker)
    (hA.of_injective (QuotientGroup.kerLift r) (QuotientGroup.kerLift_injective r))
end MonoidHom
