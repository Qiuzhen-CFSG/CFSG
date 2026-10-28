module

public import Theory.SpecificGroups.MinusExtraspecial.InvolutionCentralizerGeometry

/-!
# Pointwise fixation of an involution centralizer in the minus group

An automorphism of the minus-extraspecial group of order 32 fixing the
centralizer of a noncentral involution pointwise is either the identity or
conjugation by that involution. A finite check supplies a representative of
the other coset and its two possible images, constrained by squares and
conjugation on the centralizer. The remainder is a two-coset argument.

The ambient consequence uses self-centralization of the whole core to put
the centralizer of this index-two subgroup back inside the core. This is
the width-two form of the singular-axis obstruction in Aschbacher,
*Sporadic Groups* (1994), proof of 8.15(2), printed p.29.
-/

namespace MinusExtraspecial
private theorem fixer_calculation : ∀ u : Model,
    u ^ 2 = 1 → u ≠ 1 → u ≠ quaternion z →
    ∃ t : Model,
      (∀ x : Model, x * u = u * x ∨ (t⁻¹ * x) * u = u * (t⁻¹ * x)) ∧
      (∀ x : Model, x * u = u * x →
        (t * x * t⁻¹) * u = u * (t * x * t⁻¹)) ∧
      (∀ v : Model, v ^ 2 = t ^ 2 →
        (∀ x : Model, x * u = u * x → v * x * v⁻¹ = t * x * t⁻¹) →
        v = t ∨ v = u * t * u⁻¹) := by
  decide +kernel

private theorem model_fixer {u : Model}
    (hu : u ^ 2 = 1) (hu1 : u ≠ 1) (huz : u ≠ quaternion z)
    (a : MulAut Model) (ha : ∀ x : Model, x * u = u * x → a x = x) :
    a = 1 ∨ a = MulAut.conj u := by
  obtain ⟨t, hcover, hnormal, hrigid⟩ := fixer_calculation u hu hu1 huz
  have hsquare : a t ^ 2 = t ^ 2 := by
    rw [← map_pow]
    exact ha _ ((Subgroup.mem_center_iff.mp (square_mem_center t) u).symm)
  have hconj (x : Model) (hx : x * u = u * x) :
      a t * x * (a t)⁻¹ = t * x * t⁻¹ := by
    have h := ha _ (hnormal x hx)
    simpa only [map_mul, map_inv, ha x hx] using h
  have hext (b : MulAut Model) (hbt : a t = b t)
      (hb : ∀ x : Model, x * u = u * x → b x = x) : a = b := by
    apply MulEquiv.ext
    intro x
    rcases hcover x with hx | hx
    · exact (ha x hx).trans (hb x hx).symm
    · calc
        a x = a t * a (t⁻¹ * x) := by rw [← map_mul]; simp
        _ = b t * b (t⁻¹ * x) := by rw [hbt, ha _ hx, hb _ hx]
        _ = b x := by rw [← map_mul]; simp
  rcases hrigid (a t) hsquare hconj with ht | ht
  · exact Or.inl (hext 1 ht (fun _ _ => rfl))
  · apply Or.inr
    exact hext (MulAut.conj u) ht (fun x hx => by
      change u * x * u⁻¹ = x
      rw [← hx, mul_inv_cancel_right])

variable {K : Type*} [Group K]
/-- A pointwise fixer of the involution centralizer is one of its two inner fixers. -/
public theorem eq_one_or_conj_of_fixes_involution_centralizer (e : K ≃* Model) {u : K}
    (hu : u ^ 2 = 1) (huZ : u ∉ Subgroup.center K)
    (a : MulAut K) (ha : ∀ x : K, x * u = u * x → a x = x) :
    a = 1 ∨ a = MulAut.conj u := by
  have heu : e u ^ 2 = 1 := by simpa only [map_pow, map_one] using congrArg e hu
  have heZ : e u ∉ Subgroup.center Model := by
    intro h
    apply huZ
    rw [Subgroup.mem_center_iff]
    intro x
    apply e.injective
    simpa only [map_mul] using Subgroup.mem_center_iff.mp h (e x)
  have he1 : e u ≠ 1 := fun h => heZ (h ▸ (Subgroup.center Model).one_mem)
  have hec : e u ≠ quaternion z := fun h =>
    heZ ((mem_center_iff _).mpr (Or.inr h))
  have hfix (x : Model) (hx : x * e u = e u * x) : MulAut.congr e a x = x := by
    change e (a (e.symm x)) = x
    rw [ha]
    · exact e.apply_symm_apply x
    · apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using hx
  rcases model_fixer heu he1 hec (MulAut.congr e a) hfix with h | h
  · exact Or.inl ((MulAut.congr e).injective (h.trans (map_one _).symm))
  · apply Or.inr
    apply (MulAut.congr e).injective
    rw [h]
    apply MulEquiv.ext
    intro x
    change e u * x * (e u)⁻¹ = e (u * e.symm x * u⁻¹)
    simp only [map_mul, map_inv, e.apply_symm_apply]

open Subgroup

variable {G : Type*} [Group G]

/-- A normalizing element fixing the involution centralizer lies in the core,
provided the full core is self-centralizing. -/
public theorem normalizer_inf_centralizer_involutionCentralizer_le
    (Q : Subgroup G) (e : Q ≃* Model) (u : Q)
    (hu : u ^ 2 = 1) (huZ : u ∉ center Q)
    (hQ : centralizer (Q : Set G) ≤ Q) :
    normalizer (Q : Set G) ⊓ centralizer
      ((Q ⊓ centralizer ({(u : G)} : Set G) : Subgroup G) : Set G) ≤ Q := by
  rintro c ⟨hcN, hc⟩
  let n : normalizer (Q : Set G) := ⟨c, hcN⟩
  have hfix (x : Q) (hx : x * u = u * x) : Q.normalizerMonoidHom n x = x := by
    apply Subtype.ext
    change c * x * c⁻¹ = x
    rw [← hc x ⟨x.property,
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hx)⟩,
      mul_inv_cancel_right]
  obtain ⟨q, hq⟩ : ∃ q : Q, Q.normalizerMonoidHom n = MulAut.conj q := by
    rcases eq_one_or_conj_of_fixes_involution_centralizer e hu huZ
      (Q.normalizerMonoidHom n) hfix with h | h
    · exact ⟨1, by simpa using h⟩
    · exact ⟨u, h⟩
  let qn : normalizer (Q : Set G) := ⟨q, le_normalizer q.property⟩
  have hqn : Q.normalizerMonoidHom qn = MulAut.conj q := by
    apply MulEquiv.ext
    intro x
    rfl
  have hk : n * qn⁻¹ ∈ Q.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hq, hqn, mul_inv_cancel]
  rw [normalizerMonoidHom_ker] at hk
  have hcq : c * (q : G)⁻¹ ∈ Q := hQ hk
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using Q.mul_mem hcq q.property


/-- The centralizer of the involution centralizer is its central four-group. -/
public theorem centralizer_centralizer_involution_le
    (e : K ≃* Model) (u : K) (hu : u ^ 2 = 1) (huZ : u ∉ center K) :
    centralizer (centralizer ({u} : Set K) : Set K) ≤ center K ⊔ zpowers u := by
  intro x hx
  have hfix (y : K) (hy : y * u = u * y) : MulAut.conj x y = y := by
    change x * y * x⁻¹ = y
    rw [← hx y (mem_centralizer_singleton_iff.mpr hy), mul_inv_cancel_right]
  have central_of_conj {v : K} (hv : MulAut.conj v = 1) : v ∈ center K := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    have h := DFunLike.congr_fun hv y
    change v * y * v⁻¹ = y at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  rcases eq_one_or_conj_of_fixes_involution_centralizer e hu huZ
      (MulAut.conj x) hfix with h | h
  · exact mem_sup_left (central_of_conj h)
  · have hv : MulAut.conj (u⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have hm := (center K ⊔ zpowers u).mul_mem
      (mem_sup_right (mem_zpowers u)) (mem_sup_left (central_of_conj hv))
    simpa only [mul_inv_cancel_left] using hm

end MinusExtraspecial
