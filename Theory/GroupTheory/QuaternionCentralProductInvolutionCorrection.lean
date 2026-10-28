module

public import Theory.GroupTheory.QuaternionCentralProductFactors
public import Theory.GroupTheory.QuaternionCentralProductCenter

/-!
# Correcting a quaternion centralizer element to an involution

Let two commuting quaternion factors generate a self-centralizing subgroup.
An outside element centralizing the first factor, with square in the shared
center, can be multiplied by an element of that factor to give an outside
involution. Its restriction to the first factor is inner and its restriction
to the other factor is outer. Indeed, two inner restrictions would differ
from an inner automorphism of the product by an element of its centralizer.

This is the involution construction in Janko–Thompson, Math. Z. 113 (1970),
§4, case (c), printed p.392. Existence of the original centralizer element
and the order of the resulting fixed subgroup are separate calculations.
-/

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem square_root_in_quaternion_of_central (B : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (z : G) (hz : z ∈ (center B).map B.subtype) :
    ∃ b ∈ B, b ^ 2 = z := by
  obtain ⟨e⟩ := hB
  obtain ⟨zB, hzB, rfl⟩ := hz
  have hmodel : ∀ q : QuaternionGroup 2,
      (∀ x, x * q = q * x) → ∃ b, b ^ 2 = q := by decide
  obtain ⟨b, hb⟩ := hmodel (e zB) (by
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hzB y))
  refine ⟨e.symm b, (e.symm b).property, ?_⟩
  have h : (e.symm b) ^ 2 = zB := e.injective (by simpa using hb)
  exact congrArg Subtype.val h

/-- An outside element centralizing one quaternion factor and squaring into
the shared center gives an outside involution with exactly one inner factor
restriction. -/
public theorem exists_involution_inner_outer_of_quaternion_centralizing_square
    (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hself : centralizer ((B ⊔ C : Subgroup G) : Set G) ≤ B ⊔ C)
    (k : G) (hout : k ∉ B ⊔ C)
    (hkn : k ∈ normalizer ((B ⊔ C : Subgroup G) : Set G))
    (hkc : k ∈ centralizer (B : Set G)) (hksq : k ^ 2 ∈ B ⊓ C) :
    ∃ l : G, orderOf l = 2 ∧ l ∉ B ⊔ C ∧
      l ∈ normalizer (B : Set G) ∧ l ∈ normalizer (C : Set G) ∧
      (∃ b ∈ B, ∀ x ∈ B, l * x * l⁻¹ = b * x * b⁻¹) ∧
      ¬ (∃ c ∈ C, ∀ x ∈ C, l * x * l⁻¹ = c * x * c⁻¹) := by
  have hksqZ : k ^ 2 ∈ (center B).map B.subtype :=
    (intersection_eq_factor_center B C hB hinter hcomm) ▸ hksq
  obtain ⟨b, hb, hbsq⟩ := square_root_in_quaternion_of_central B hB (k ^ 2) hksqZ
  have hkfour : (k ^ 2) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨k ^ 2, hksq⟩ : (B ⊓ C : Subgroup G)))
    rw [hinter] at hh
    exact congrArg Subtype.val hh
  let l := b * k
  have hlout : l ∉ B ⊔ C := by
    intro h
    exact hout ((B ⊔ C).mul_mem_cancel_left (mem_sup_left hb) |>.mp h)
  have hlorder : orderOf l = 2 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨?_, fun h => hlout (h ▸ (B ⊔ C).one_mem)⟩
    change (b * k) ^ 2 = 1
    rw [(show Commute b k from hkc b hb).mul_pow, hbsq, ← pow_two, hkfour]
  have hinner : ∀ x ∈ B, l * x * l⁻¹ = b * x * b⁻¹ := by
    intro x hx
    dsimp [l]
    calc
      b * k * x * (b * k)⁻¹ = b * (k * x) * k⁻¹ * b⁻¹ := by group
      _ = b * (x * k) * k⁻¹ * b⁻¹ := by rw [← hkc x hx]
      _ = b * x * b⁻¹ := by group
  have hlnB : l ∈ normalizer (B : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hinner x hx]
      exact B.mul_mem (B.mul_mem hb hx) (B.inv_mem hb)
    · intro hx
      have hll : l * l = 1 := by simpa only [pow_two, hlorder] using pow_orderOf_eq_one l
      have hh := hinner (l * x * l⁻¹) hx
      have he : l * (l * x * l⁻¹) * l⁻¹ = x := by
        calc
          l * (l * x * l⁻¹) * l⁻¹ = (l * l) * x * (l * l)⁻¹ := by group
          _ = x := by rw [hll]; simp
      rw [he] at hh
      rw [hh]
      exact B.mul_mem (B.mul_mem hb hx) (B.inv_mem hb)
  have hln : l ∈ normalizer ((B ⊔ C : Subgroup G) : Set G) :=
    (normalizer _).mul_mem ((B ⊔ C).le_normalizer (mem_sup_left hb)) hkn
  have hlnC : l ∈ normalizer (C : Set G) := by
    let e := MulAut.conj l
    have hBC : B ≠ C := by
      intro h
      obtain ⟨model⟩ := hB
      have hcB : Nat.card B = 8 := by
        rw [Nat.card_congr model.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      rw [← h, inf_idem, hcB] at hinter
      omega
    have hjoin := mem_normalizer_iff_map_conj_eq.mp hln
    have hBB := mem_normalizer_iff_map_conj_eq.mp hlnB
    obtain ⟨model⟩ := hC
    have hfactor := quaternion_subgroup_eq_factor B C (C.map e.toMonoidHom)
      hB ⟨model⟩ hinter hcomm
      ⟨(C.equivMapOfInjective e.toMonoidHom e.injective).symm.trans model⟩
      ((map_mono (show C ≤ B ⊔ C from le_sup_right)).trans_eq hjoin)
    apply mem_normalizer_iff_map_conj_eq.mpr
    rcases hfactor with h | h
    · exact (hBC (map_injective e.injective (hBB.trans h.symm))).elim
    · exact h
  refine ⟨l, hlorder, hlout, hlnB, hlnC, ⟨b, hb, hinner⟩, ?_⟩
  rintro ⟨c, hc, hcin⟩
  have hkC : ∀ x ∈ C, k * x * k⁻¹ = c * x * c⁻¹ := by
    intro x hx
    have hbk : b * (k * x * k⁻¹) * b⁻¹ = l * x * l⁻¹ := by dsimp [l]; group
    have hh : k * x * k⁻¹ = b⁻¹ * (l * x * l⁻¹) * b := by rw [← hbk]; group
    rw [hh, hcin x hx]
    have hcx : c * x * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hc hx) (C.inv_mem hc)
    rw [mul_assoc, ← hcomm b hb _ hcx, ← mul_assoc, inv_mul_cancel, one_mul]
  have hfixB : c⁻¹ * k ∈ centralizer (B : Set G) :=
    (centralizer (B : Set G)).mul_mem
      ((centralizer (B : Set G)).inv_mem (fun x hx => hcomm x hx c hc)) hkc
  have hfixC : c⁻¹ * k ∈ centralizer (C : Set G) := by
    intro x hx
    have hh : (c⁻¹ * k) * x * (c⁻¹ * k)⁻¹ = x := by
      calc
        (c⁻¹ * k) * x * (c⁻¹ * k)⁻¹ = c⁻¹ * (k * x * k⁻¹) * c := by group
        _ = c⁻¹ * (c * x * c⁻¹) * c := by rw [hkC x hx]
        _ = x := by group
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hfix : c⁻¹ * k ∈ centralizer ((B ⊔ C : Subgroup G) : Set G) := by
    have hle : B ⊔ C ≤ centralizer ({c⁻¹ * k} : Set G) :=
      sup_le (fun x hx => mem_centralizer_singleton_iff.mpr (hfixB x hx))
        (fun x hx => mem_centralizer_singleton_iff.mpr (hfixC x hx))
    exact fun x hx => mem_centralizer_singleton_iff.mp (hle hx)
  have hh := (B ⊔ C).mul_mem (mem_sup_right hc) (hself hfix)
  exact hout (by simpa using hh)

end Subgroup
