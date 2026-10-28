module

public import Theory.GroupTheory.IndexTwoIntersection
public import Theory.GroupTheory.C4SquareQuaternionIndexTwo

/-!
# The characteristic abelian base of an inverting extension

An index-two C₄ × C₄ subgroup inverted by an outside element is characteristic.
Every outside element inverts the base. An abelian subgroup crossing the base
therefore meets it in its four elements of square one, and has order at most
eight. This makes the base the unique abelian subgroup of order sixteen.

This elementary argument applies to the initial core in Stellmacher (8.6)(a).
-/

namespace Subgroup

private abbrev C4 := Multiplicative (ZMod 4)

/-- All elements outside an abelian index-two base induce the same inversion. -/
public theorem inverts_of_not_mem_index_two
    {G : Type*} [Group G] (A : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hi : A.index = 2) (t : G) (ht : t ∉ A)
    (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹)
    (x : G) (hx : x ∉ A) : ∀ a ∈ A, x * a * x⁻¹ = a⁻¹ := by
  intro a ha
  have hxt : x * t⁻¹ ∈ A := (A.mul_mem_iff_of_index_two hi).mpr (by
    simpa only [A.inv_mem_iff] using (show x ∈ A ↔ t ∈ A from iff_of_false hx ht))
  calc
    x * a * x⁻¹ = (x * t⁻¹) * (t * a * t⁻¹) * (x * t⁻¹)⁻¹ := by group
    _ = (x * t⁻¹) * a⁻¹ * (x * t⁻¹)⁻¹ := by rw [hinv a ha]
    _ = a⁻¹ := by rw [hcomm _ hxt _ (A.inv_mem ha), mul_assoc, mul_inv_cancel, mul_one]

/-- Any abelian subgroup crossing an inverted C₄ × C₄ base has order at most eight. -/
public theorem card_le_eight_of_abelian_not_le_inverted_c4_square
    {G : Type*} [Group G] [Finite G] (A B : Subgroup G)
    (hA : Nonempty (A ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) (hi : A.index = 2)
    (t : G) (ht : t ∉ A) (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹)
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hnle : ¬ B ≤ A) :
    Nat.card B ≤ 8 := by
  obtain ⟨e⟩ := hA
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have hh : (⟨a, ha⟩ : A) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := e.injective (by
      simp only [map_mul]
      exact mul_comm _ _)
    exact congrArg Subtype.val hh
  obtain ⟨x, hxB, hxA⟩ := SetLike.not_le_iff_exists.mp hnle
  have hsquare (a : A.subgroupOf B) : (a : B).val ^ 2 = 1 := by
    have h1 := inverts_of_not_mem_index_two A hcomm hi t ht hinv x hxA
      (a : B).val a.property
    have h2 := hB x hxB (a : B).val (a : B).property
    rw [h2, mul_assoc, mul_inv_cancel, mul_one] at h1
    rw [pow_two]
    exact (congrArg (fun z => z * (a : B).val) h1).trans (inv_mul_cancel _)
  let f : A.subgroupOf B → {z : C4 × C4 // z ^ 2 = 1} := fun a =>
    ⟨e ⟨(a : B).val, a.property⟩, by
      rw [← map_pow]
      have h : (⟨(a : B).val, a.property⟩ : A) ^ 2 = 1 := Subtype.ext (hsquare a)
      rw [h, map_one]⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h := e.injective (congrArg Subtype.val hab)
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : A => (z : G)) h
  have hb := Nat.card_le_card_of_injective f hf
  have hc : Nat.card {z : C4 × C4 // z ^ 2 = 1} = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hc] at hb
  have hcount := (A.subgroupOf B).card_mul_index
  rw [subgroupOf_index_eq_two A B hi hnle] at hcount
  omega

/-- The abelian base in an inverting extension of C₄ × C₄ is characteristic. -/
public theorem characteristic_of_inverted_c4_square
    {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    (hA : Nonempty (A ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) (hi : A.index = 2)
    (t : G) (ht : t ∉ A) (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) :
    A.Characteristic := by
  obtain ⟨e⟩ := hA
  have hcard : Nat.card A = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num [C4]
  apply characteristic_iff_map_eq.mpr
  intro φ
  have hmapcard : Nat.card (A.map φ.toMonoidHom) = 16 := by
    rw [card_map_of_injective φ.injective, hcard]
  have hle : A.map φ.toMonoidHom ≤ A := by
    by_contra hn
    have hb : ∀ a ∈ A.map φ.toMonoidHom, ∀ b ∈ A.map φ.toMonoidHom,
        a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      have hh : (⟨a, ha⟩ : A) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := e.injective (by
        simp only [map_mul]
        exact mul_comm _ _)
      exact congrArg Subtype.val hh
    have hbound := card_le_eight_of_abelian_not_le_inverted_c4_square
      A (A.map φ.toMonoidHom) ⟨e⟩ hi t ht hinv hb hn
    omega
  exact eq_of_le_of_card_ge hle (by rw [hcard, hmapcard])

end Subgroup
