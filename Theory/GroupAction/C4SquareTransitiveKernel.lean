module

public import Theory.GroupAction.C4SquareActionDichotomySetup
public import Theory.GroupAction.C4SquareFixedKernel

/-!
# A transitive order-eight kernel on a C₄-square

Let `H` be an order-eight group of automorphisms fixing every square-one element
and containing inversion. If its normalizer acts transitively on the three
nonidentity involutions, an element of `H` fixing a primitive point cannot invert
another primitive point.

Transitivity supplies a normalizing automorphism cycling the three involutions.
Its conjugation on the involution-fixing kernel agrees with the explicit
coordinate rotation: their quotient fixes every involution and hence commutes
with that kernel. A small binary certificate shows that any counterexample,
its two rotation conjugates, and inversion have sixteen distinct products.
All these products belong to `H`, contradicting its order. The certificate
uses the sixteen congruence matrices, never permutations of the base group.

Source: MacWilliams, Trans. AMS 150 (1970), §2 and §4;
Janko–Thompson, Math. Z. 113 (1970), 1.4(c), printed p.386.
-/

set_option synthInstance.maxSize 8192

namespace C4SquareExtension
namespace TransitiveKernel
open ActionDichotomy
private abbrev p : Model := e₁ ^ 2
private abbrev q : Model := e₂ ^ 2
private abbrev r : Model := p * q

private def rotate : MulAut Model where
  toFun x := (x.2⁻¹, x.1 * x.2⁻¹)
  invFun x := (x.2 * x.1⁻¹, x.1⁻¹)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

private theorem three : ∀ x : Model, x ^ 2 = 1 → x ≠ 1 →
    x = p ∨ x = q ∨ x = r := by decide

private theorem square_image (a : MulAut Model) (x : Model) (hx : x ^ 2 = 1) :
    (a x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]

private theorem nonone_image (a : MulAut Model) (x : Model) (hx : x ≠ 1) :
    a x ≠ 1 := by
  intro h
  exact hx (a.injective (h.trans (map_one a).symm))

private theorem exists_cycle (H : Subgroup (MulAut Model))
    (htrans : ∀ u v : Model, u ^ 2 = 1 → v ^ 2 = 1 → u ≠ 1 → v ≠ 1 →
      ∃ a : MulAut Model, H.map (MulAut.conj a).toMonoidHom = H ∧ a u = v) :
    ∃ c ∈ Subgroup.normalizer (H : Set (MulAut Model)), c p = q ∧ c q = r := by
  obtain ⟨a, ha, hap⟩ := htrans p q (by decide) (by decide) (by decide) (by decide)
  obtain ⟨b, hb, hbp⟩ := htrans p r (by decide) (by decide) (by decide) (by decide)
  have haN := Subgroup.mem_normalizer_iff_map_conj_eq.mpr ha
  have hbN := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hb
  have haq := three (a q) (square_image a q (by decide))
    (nonone_image a q (by decide))
  have hbq := three (b q) (square_image b q (by decide))
    (nonone_image b q (by decide))
  rcases haq with haq | haq | haq
  · rcases hbq with hbq | hbq | hbq
    · refine ⟨b * b, (Subgroup.normalizer _).mul_mem hbN hbN, ?_, ?_⟩
      · change b (b p) = q
        rw [hbp, map_mul, hbp, hbq]
        decide
      · change b (b q) = r
        rw [hbq, hbp]
    · exact ⟨b * a, (Subgroup.normalizer _).mul_mem hbN haN,
        by change b (a p) = q; rw [hap, hbq],
        by change b (a q) = r; rw [haq, hbp]⟩
    · exact False.elim ((by decide : q ≠ p) (b.injective (hbq.trans hbp.symm)))
  · exact False.elim ((by decide : q ≠ p) (a.injective (haq.trans hap.symm)))
  · exact ⟨a, haN, hap, haq⟩

private theorem agrees_on_squares (c : MulAut Model) (hp : c p = q) (hq : c q = r) :
    ∀ x : Model, x ^ 2 = 1 → c x = rotate x := by
  intro x hx
  by_cases h : x = 1
  · subst x; simp
  rcases three x hx h with rfl | rfl | rfl
  · exact hp
  · exact hq
  · rw [map_mul, hp, hq]
    decide

private theorem rotate_conj_mem (H : Subgroup (MulAut Model))
    (hfix : ∀ f ∈ H, ∀ x : Model, x ^ 2 = 1 → f x = x)
    (c : MulAut Model) (hc : c ∈ Subgroup.normalizer (H : Set (MulAut Model)))
    (hp : c p = q) (hq : c q = r) (f : MulAut Model) (hf : f ∈ H) :
    MulAut.conj rotate f ∈ H := by
  have hk : ∀ x : Model, x ^ 2 = 1 → (rotate⁻¹ * c) x = x := by
    intro x hx
    change rotate.symm (c x) = x
    rw [agrees_on_squares c hp hq x hx, rotate.symm_apply_apply]
  have hcomm := commute_of_fix_square_one (rotate⁻¹ * c) f hk (hfix f hf)
  have heq : MulAut.conj rotate f = MulAut.conj c f := by
    simp only [MulAut.conj_apply]
    have he := hcomm.eq
    have he' := congrArg (fun t : MulAut Model => rotate * t * c⁻¹) he
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel,
      mul_one] using he'.symm
  rw [heq]
  exact (Subgroup.mem_normalizer_iff.mp hc f).mp hf

private def orbitWord (m : Code) (i : Code) : MulAut Model :=
  (MulEquiv.inv Model : MulAut Model) ^ i.1.val *
    congruenceAut m ^ i.2.1.val *
    (MulAut.conj rotate (congruenceAut m)) ^ i.2.2.1.val *
    (MulAut.conj rotate (MulAut.conj rotate (congruenceAut m))) ^ i.2.2.2.val

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem bad_injective : ∀ m : Code,
    (∃ x : Model, congruenceAut m x = x ∧ x ^ 2 ≠ 1) →
    (∃ y : Model, congruenceAut m y = y⁻¹ ∧ y ^ 2 ≠ 1) →
    ∀ i j : Code, orbitWord m i e₁ = orbitWord m j e₁ →
      orbitWord m i e₂ = orbitWord m j e₂ → i = j := by decide

end TransitiveKernel

open ActionDichotomy TransitiveKernel in
/-- In an order-eight involution-fixing automorphism group whose normalizer is
transitive on the three involutions and which contains inversion, an automorphism
fixing an element of order four can invert only elements of square one. -/
public theorem inverted_square_eq_one_of_transitive_kernel
    (H : Subgroup (MulAut Model)) (hH : Nat.card H = 8)
    (hfix : ∀ f ∈ H, ∀ x : Model, x ^ 2 = 1 → f x = x)
    (hinversion : (MulEquiv.inv Model : MulAut Model) ∈ H)
    (htrans : ∀ u v : Model, u ^ 2 = 1 → v ^ 2 = 1 → u ≠ 1 → v ≠ 1 →
      ∃ a : MulAut Model, H.map (MulAut.conj a).toMonoidHom = H ∧ a u = v) :
    ∀ f ∈ H, (∃ x : Model, f x = x ∧ x ^ 2 ≠ 1) →
      ∀ y : Model, f y = y⁻¹ → y ^ 2 = 1 := by
  classical
  obtain ⟨c, hc, hp, hq⟩ := exists_cycle H htrans
  have hrot := rotate_conj_mem H hfix c hc hp hq
  intro f hf hfixed y hy
  by_contra hy2
  obtain ⟨m, rfl⟩ := exists_congruenceAut f (hfix f hf)
  have hmem (i : Code) : orbitWord m i ∈ H := by
    exact H.mul_mem (H.mul_mem (H.mul_mem
      (H.pow_mem hinversion _) (H.pow_mem hf _))
      (H.pow_mem (hrot _ hf) _)) (H.pow_mem (hrot _ (hrot _ hf)) _)
  let F : Code → H := fun i => ⟨orbitWord m i, hmem i⟩
  have hF : Function.Injective F := by
    intro i j hij
    have heq := congrArg Subtype.val hij
    exact bad_injective m hfixed ⟨y, hy, hy2⟩ i j
      (congrArg (fun a : MulAut Model => a e₁) heq)
      (congrArg (fun a : MulAut Model => a e₂) heq)
  let : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have hle := Nat.card_le_card_of_injective F hF
  have hcode : Nat.card Code = 16 := by rw [Nat.card_eq_fintype_card]; decide
  rw [hcode, hH] at hle
  omega

end C4SquareExtension
