module

public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Index

/-!
# Involutions in commuting products with odd intersection

If A and B commute and A ∩ B has odd order, every involution in AB is a
product of commuting elements of square one, one from each factor. Starting
with x = ab, the common square a² = b⁻² lies in the odd intersection. Its
unique square root corrects both factors without changing their product.
This is the involution calculation behind GLS IV, Chapter 2, Lemma 16.4(b).
-/

public section
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

/-- Square-one elements split over commuting factors with odd intersection. -/
theorem exists_square_one_factors_of_odd_intersection
    (A B : Subgroup G) (hcomm : B ≤ centralizer (A : Set G))
    (hodd : Odd (Nat.card (A ⊓ B : Subgroup G))) {x : G}
    (hx : x ∈ A ⊔ B) (hx2 : x ^ 2 = 1) :
    ∃ a ∈ A, ∃ b ∈ B, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a * b = x := by
  have hn : B ≤ normalizer (A : Set G) := hcomm.trans (Subgroup.centralizer_le_normalizer _)
  have hm : x ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B hn]
    exact hx
  obtain ⟨a,ha,b,hb,rfl⟩ := hm
  have hab : Commute a b := hcomm hb a ha
  have hs : a ^ 2 * b ^ 2 = 1 := (hab.mul_pow 2).symm.trans hx2
  have habsq : a ^ 2 = (b ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hs
  have ha2 : a ^ 2 ∈ A ⊓ B := ⟨A.pow_mem ha 2, habsq ▸ B.inv_mem (B.pow_mem hb 2)⟩
  obtain ⟨d,hd⟩ := (powCoprime (G := (A ⊓ B : Subgroup G))
    (n := 2) hodd.coprime_two_right).surjective ⟨a ^ 2,ha2⟩
  have hd2 : (d : G) ^ 2 = a ^ 2 := congrArg Subtype.val hd
  have had : Commute a (d : G) := hcomm d.property.2 a ha
  have hdb : Commute (d : G) b := hcomm hb d d.property.1
  refine ⟨a * (d : G)⁻¹, A.mul_mem ha (A.inv_mem d.property.1),
    (d : G) * b, B.mul_mem d.property.2 hb, ?_, ?_, ?_⟩
  · rw [had.inv_right.mul_pow, inv_pow, hd2, mul_inv_cancel]
  · rw [hdb.mul_pow, hd2]
    exact hs
  · group

/-- If the second factor has a unique involution u, the first omega of
T∩AB is Ω₁(T∩A)⟨u⟩ whenever u belongs to T. No Sylow hypothesis is needed. -/
theorem omega_inf_commuting_join_of_unique_involution
    (A B T : Subgroup G) (hcomm : B ≤ centralizer (A : Set G))
    (hodd : Odd (Nat.card (A ⊓ B : Subgroup G))) {u : G}
    (huB : u ∈ B) (huT : u ∈ T) (hu2 : u ^ 2 = 1)
    (huniq : ∀ b ∈ B, b ^ 2 = 1 → b = 1 ∨ b = u) :
    omegaOneAmbient (T ⊓ (A ⊔ B)) = omegaOneAmbient (T ⊓ A) ⊔ zpowers u := by
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hx2
    obtain ⟨a,ha,b,hb,ha2,hb2,he⟩ :=
      exists_square_one_factors_of_odd_intersection A B hcomm hodd hx.2 hx2
    rcases huniq b hb hb2 with hb1 | hbu
    · rw [hb1,mul_one] at he
      rw [← he]
      exact (show omegaOneAmbient (T ⊓ A) ≤ omegaOneAmbient (T ⊓ A) ⊔ zpowers u from le_sup_left)
        ((omegaOneAmbient_le_iff _ _).mp le_rfl a ⟨he.symm ▸ hx.1,ha⟩ ha2)
    · rw [hbu] at he
      have haT : a ∈ T := by
        have hh := T.mul_mem hx.1 (T.inv_mem huT)
        rw [← he,mul_inv_cancel_right] at hh
        exact hh
      rw [← he]
      exact mul_mem_sup ((omegaOneAmbient_le_iff _ _).mp le_rfl a ⟨haT,ha⟩ ha2)
        (mem_zpowers u)
  · apply sup_le
    · exact omegaOneAmbient_mono (inf_le_inf_left _ le_sup_left)
    · apply zpowers_le.mpr
      exact (omegaOneAmbient_le_iff _ _).mp le_rfl u
        ⟨huT,(show B ≤ A ⊔ B from le_sup_right) huB⟩ hu2

end Subgroup
