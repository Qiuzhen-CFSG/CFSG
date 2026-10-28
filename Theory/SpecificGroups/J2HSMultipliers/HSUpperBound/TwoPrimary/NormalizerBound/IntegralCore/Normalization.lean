module

public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.NormalizerBound.IntegralCore.ActionData
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Tactic.Module

/-!
# Integral cyclic-error normalization for the literal HS core

Given the published small action certificate on Q = O₂(N), where N is the
literal HS base normalizer, every right crossed homomorphism trivial on Q
can be corrected so that all its errors lie in one cyclic subgroup of order
at most two.

For the third actor C, the inverse of C-I is C²-C. Composing its cocycle
value with this polynomial action gives a character killing that actor's
error. The four quotient relations then yield six equations on the other
actors' basis values. Six checked row combinations force those values to
be (1,1,z) and (z,z,z), with z²=1. Generation of Q by the marked basis and
of N by the actors and Q extends the containment to all arguments.

The calculation takes place in the subgroup of fourth roots of unity of
an arbitrary commutative target. Neither finiteness nor an exponent bound
on that target is assumed. Construction of IntegralActionData remains an
independent obligation; this module proves the conditional normalization.

Source: the integral module step behind Aschbacher–Smith I.1.3(1), printed
p.407, and the HS normalizer in I.2.2(5), p.412; GLS3 Table 5.3m. This
calculation does not use the latter paragraph's center-order-two assumption.
-/

open Subgroup
open scoped IsMulCommutative
namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
open Sporadic.LeechRelated.HS BlockNormalizer
namespace IntegralNormalization
local notation "Q" => pCore 2 baseNormalizer

theorem basis_decomposition (q : Q) : ∃ (v : Fin 3 → ℕ),
    q = integralBasis 0 ^ v 0 * integralBasis 1 ^ v 1 * integralBasis 2 ^ v 2 := by
  obtain ⟨x, rfl⟩ := CoreGeometry.coreCoordinates_bijective.surjective q
  refine ⟨fun i => (x.toAdd i).val, ?_⟩
  simp only [integralBasis, ← map_pow, ← map_mul]
  congr 1
  apply Multiplicative.toAdd.injective
  ext i
  change x.toAdd i = (x.toAdd 0).val • (Pi.single 0 (1 : ZMod 4) : Fin 3 → ZMod 4) i +
    (x.toAdd 1).val • (Pi.single 1 (1 : ZMod 4) : Fin 3 → ZMod 4) i +
    (x.toAdd 2).val • (Pi.single 2 (1 : ZMod 4) : Fin 3 → ZMod 4) i
  fin_cases i <;> simp [nsmul_eq_mul]

theorem hom_ext {K : Type*} [Monoid K] {f g : Q →* K}
    (h : ∀ i, f (integralBasis i) = g (integralBasis i)) : f = g := by
  ext q
  obtain ⟨v, rfl⟩ := basis_decomposition q
  simp only [map_mul, map_pow, h]

theorem hom_mem {K : Type*} [Group K] (f : Q →* K) (S : Subgroup K)
    (h : ∀ i, f (integralBasis i) ∈ S) (q : Q) : f q ∈ S := by
  obtain ⟨v, rfl⟩ := basis_decomposition q
  simp only [map_mul, map_pow]
  exact S.mul_mem (S.mul_mem (S.pow_mem (h 0) _) (S.pow_mem (h 1) _)) (S.pow_mem (h 2) _)

theorem core_conj (u q : Q) : MulAut.conjNormal (u : baseNormalizer) q = q := by
  apply Subtype.ext
  exact congrArg Subtype.val (show u * q * u⁻¹ = q by rw [mul_comm u q, mul_inv_cancel_right])

variable {K : Type*} [CommGroup K]

def correct (β : CoreCrossedHom K) (t : Q →* K) : CoreCrossedHom K where
  toFun n := β.toFun n * t / (t.comp (MulAut.conjNormal n).toMonoidHom)
  mul_rule n m q := by
    change β.toFun (n * m) q * t q / t (MulAut.conjNormal (n * m) q) =
      (β.toFun n (MulAut.conjNormal m q) * t (MulAut.conjNormal m q) /
        t (MulAut.conjNormal n (MulAut.conjNormal m q))) *
      (β.toFun m q * t q / t (MulAut.conjNormal m q))
    rw [β.mul_rule, map_mul]
    change _ / t (MulAut.conjNormal n (MulAut.conjNormal m q)) = _
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel
  core_rule u := by
    ext q
    change β.toFun u q * t q / t (MulAut.conjNormal (u : baseNormalizer) q) = 1
    rw [β.core_rule, core_conj]
    simp

theorem correct_apply (β : CoreCrossedHom K) (t : Q →* K)
    (n : baseNormalizer) (q : Q) :
    (correct β t).toFun n q = β.toFun n q * t q / t (MulAut.conjNormal n q) := rfl

theorem value_core (β : CoreCrossedHom K) {u : baseNormalizer} (hu : u ∈ Q) (q : Q) :
    β.toFun u q = 1 := by
  have := DFunLike.congr_fun (β.core_rule ⟨u, hu⟩) q
  exact this

theorem value_one (β : CoreCrossedHom K) (q : Q) : β.toFun 1 q = 1 :=
  value_core β (one_mem _) q

theorem value_eq (β : CoreCrossedHom K) {u v : baseNormalizer} (huv : u / v ∈ Q)
    (q : Q) : β.toFun u q = β.toFun v q := by
  have he := β.mul_rule (u / v) v q
  rw [div_mul_cancel, value_core β huv, one_mul] at he
  exact he

theorem values_mem (h : IntegralActionData) (β : CoreCrossedHom K) (S : Subgroup K)
    (hb : ∀ i j, β.toFun (h.actor i) (integralBasis j) ∈ S)
    (n : baseNormalizer) (q : Q) : β.toFun n q ∈ S := by
  have hn : n ∈ closure (Set.range h.actor ∪ (Q : Set baseNormalizer)) := by
    rw [h.generation]; exact mem_top n
  have hall : ∀ q, β.toFun n q ∈ S := by
    induction hn using closure_induction with
    | mem n hn =>
      rcases hn with ⟨i, rfl⟩ | hn
      · exact hom_mem _ S (hb i)
      · intro q; rw [value_core β hn]; exact S.one_mem
    | one => intro q; rw [value_one]; exact S.one_mem
    | mul n m _ _ hn hm =>
      intro q; rw [β.mul_rule]; exact S.mul_mem (hn _) (hm _)
    | inv n _ hn =>
      intro q
      have he := β.mul_rule n n⁻¹ q
      rw [mul_inv_cancel, value_one] at he
      have hi : β.toFun n⁻¹ q = (β.toFun n (MulAut.conjNormal n⁻¹ q))⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        exact (mul_comm _ _).trans he.symm
      rw [hi]; exact S.inv_mem (hn _)
  exact hall q

end IntegralNormalization
end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
open Subgroup
open scoped IsMulCommutative
open Sporadic.LeechRelated.HS BlockNormalizer
namespace IntegralNormalization
local notation "Q" => pCore 2 baseNormalizer
variable {K : Type*} [CommGroup K]

/-- The inverse of C-I on the marked core is C²-C. -/
def correctionCharacter (h : IntegralActionData) (β : CoreCrossedHom K) : Q →* K :=
  ((β.toFun (h.actor 2)).comp (MulAut.conjNormal (h.actor 2)).toMonoidHom).comp
      (MulAut.conjNormal (h.actor 2)).toMonoidHom /
    (β.toFun (h.actor 2)).comp (MulAut.conjNormal (h.actor 2)).toMonoidHom

variable [Module (ZMod 4) (Additive K)]

theorem killed_third (h : IntegralActionData) (β : CoreCrossedHom K) :
    (correct β (correctionCharacter h β)).toFun (h.actor 2) = 1 := by
  apply hom_ext
  intro j
  change (correct β (correctionCharacter h β)).toFun (h.actor 2) (integralBasis j) = 1
  rw [correct_apply]
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by
    fin_cases j <;> decide
  rcases hj with rfl | rfl | rfl <;>
    simp only [correctionCharacter, MonoidHom.div_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, h.on_basis, integralMatrixImage, map_mul, map_pow]
  all_goals
    norm_num [integralMatrices, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow, ofMul_one]
    simp only [← Nat.cast_smul_eq_nsmul (R := ZMod 4)]
    match_scalars <;> norm_num <;> decide

end IntegralNormalization
end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound

namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound.IntegralNormalization
/-- The six small relation rows force a single involution parameter.
Each equality below checks the supplied row-combination witness in Z/4. -/
theorem six_relations {V : Type*} [AddCommGroup V] [Module (ZMod 4) V]
    (x0 x1 x2 y0 y1 y2 : V)
    (e0 : x0 + (2 : ZMod 4) • x1 + (2 : ZMod 4) • x2 = 0)
    (e1 : (3 : ZMod 4) • y0 + y1 = 0)
    (e2 : x1 + (2 : ZMod 4) • y0 + (3 : ZMod 4) • y1 + (3 : ZMod 4) • y2 = 0)
    (e3 : x2 + y0 + (2 : ZMod 4) • y1 + (2 : ZMod 4) • y2 = 0)
    (e4 : (2 : ZMod 4) • x0 + (3 : ZMod 4) • x1 + (2 : ZMod 4) • x2 + (2 : ZMod 4) • y0 + (2 : ZMod 4) • y1 + (2 : ZMod 4) • y2 = 0)
    (e5 : (2 : ZMod 4) • x0 + (3 : ZMod 4) • x2 + (2 : ZMod 4) • y0 + y1 + (2 : ZMod 4) • y2 = 0)
    : (2 : ZMod 4) • y2 = 0 ∧ x0 = 0 ∧ x1 = 0 ∧
      x2 = y2 ∧ y0 = y2 ∧ y1 = y2 := by
  have h0 : (2 : ZMod 4) • y2 = 0 := by
    calc
      _ = (2 : ZMod 4) • (x0 + (2 : ZMod 4) • x1 + (2 : ZMod 4) • x2) +
        (3 : ZMod 4) • ((3 : ZMod 4) • y0 + y1) +
        (2 : ZMod 4) • (x1 + (2 : ZMod 4) • y0 + (3 : ZMod 4) • y1 + (3 : ZMod 4) • y2) +
        (1 : ZMod 4) • (x2 + y0 + (2 : ZMod 4) • y1 + (2 : ZMod 4) • y2) +
        (2 : ZMod 4) • ((2 : ZMod 4) • x0 + (3 : ZMod 4) • x1 + (2 : ZMod 4) • x2 + (2 : ZMod 4) • y0 + (2 : ZMod 4) • y1 + (2 : ZMod 4) • y2) +
        (1 : ZMod 4) • ((2 : ZMod 4) • x0 + (3 : ZMod 4) • x2 + (2 : ZMod 4) • y0 + y1 + (2 : ZMod 4) • y2) := by
        match_scalars <;> norm_num <;> decide
      _ = 0 := by rw [e0, e1, e2, e3, e4, e5]; simp
  have h1 : x0 = 0 := by
    calc
      _ = (3 : ZMod 4) • (x0 + (2 : ZMod 4) • x1 + (2 : ZMod 4) • x2) +
        (3 : ZMod 4) • ((3 : ZMod 4) • y0 + y1) +
        (1 : ZMod 4) • (x2 + y0 + (2 : ZMod 4) • y1 + (2 : ZMod 4) • y2) +
        (2 : ZMod 4) • ((2 : ZMod 4) • x0 + (3 : ZMod 4) • x1 + (2 : ZMod 4) • x2 + (2 : ZMod 4) • y0 + (2 : ZMod 4) • y1 + (2 : ZMod 4) • y2) +
        (3 : ZMod 4) • ((2 : ZMod 4) • x0 + (3 : ZMod 4) • x2 + (2 : ZMod 4) • y0 + y1 + (2 : ZMod 4) • y2) := by
        match_scalars <;> norm_num <;> decide
      _ = 0 := by rw [e0, e1, e3, e4, e5]; simp
  have h2 : x1 = 0 := by
    calc
      _ = (2 : ZMod 4) • (x0 + (2 : ZMod 4) • x1 + (2 : ZMod 4) • x2) +
        (2 : ZMod 4) • ((3 : ZMod 4) • y0 + y1) +
        (2 : ZMod 4) • (x1 + (2 : ZMod 4) • y0 + (3 : ZMod 4) • y1 + (3 : ZMod 4) • y2) +
        (1 : ZMod 4) • ((2 : ZMod 4) • x0 + (3 : ZMod 4) • x1 + (2 : ZMod 4) • x2 + (2 : ZMod 4) • y0 + (2 : ZMod 4) • y1 + (2 : ZMod 4) • y2) +
        (2 : ZMod 4) • ((2 : ZMod 4) • x0 + (3 : ZMod 4) • x2 + (2 : ZMod 4) • y0 + y1 + (2 : ZMod 4) • y2) := by
        match_scalars <;> norm_num <;> decide
      _ = 0 := by rw [e0, e1, e2, e4, e5]; simp
  have h3 : x2 - y2 = 0 := by
    calc
      _ = (2 : ZMod 4) • ((3 : ZMod 4) • y0 + y1) +
        (1 : ZMod 4) • (x1 + (2 : ZMod 4) • y0 + (3 : ZMod 4) • y1 + (3 : ZMod 4) • y2) +
        (1 : ZMod 4) • ((2 : ZMod 4) • x0 + (3 : ZMod 4) • x1 + (2 : ZMod 4) • x2 + (2 : ZMod 4) • y0 + (2 : ZMod 4) • y1 + (2 : ZMod 4) • y2) +
        (1 : ZMod 4) • ((2 : ZMod 4) • x0 + (3 : ZMod 4) • x2 + (2 : ZMod 4) • y0 + y1 + (2 : ZMod 4) • y2) := by
        match_scalars <;> norm_num <;> decide
      _ = 0 := by rw [e1, e2, e4, e5]; simp
  have h4 : y0 - y2 = 0 := by
    calc
      _ = (2 : ZMod 4) • (x0 + (2 : ZMod 4) • x1 + (2 : ZMod 4) • x2) +
        (3 : ZMod 4) • ((3 : ZMod 4) • y0 + y1) +
        (3 : ZMod 4) • (x1 + (2 : ZMod 4) • y0 + (3 : ZMod 4) • y1 + (3 : ZMod 4) • y2) +
        (3 : ZMod 4) • ((2 : ZMod 4) • x0 + (3 : ZMod 4) • x1 + (2 : ZMod 4) • x2 + (2 : ZMod 4) • y0 + (2 : ZMod 4) • y1 + (2 : ZMod 4) • y2) +
        (2 : ZMod 4) • ((2 : ZMod 4) • x0 + (3 : ZMod 4) • x2 + (2 : ZMod 4) • y0 + y1 + (2 : ZMod 4) • y2) := by
        match_scalars <;> norm_num <;> decide
      _ = 0 := by rw [e0, e1, e2, e4, e5]; simp
  have h5 : y1 - y2 = 0 := by
    calc
      _ = (2 : ZMod 4) • (x0 + (2 : ZMod 4) • x1 + (2 : ZMod 4) • x2) +
        (2 : ZMod 4) • ((3 : ZMod 4) • y0 + y1) +
        (3 : ZMod 4) • (x1 + (2 : ZMod 4) • y0 + (3 : ZMod 4) • y1 + (3 : ZMod 4) • y2) +
        (2 : ZMod 4) • (x2 + y0 + (2 : ZMod 4) • y1 + (2 : ZMod 4) • y2) +
        (3 : ZMod 4) • ((2 : ZMod 4) • x0 + (3 : ZMod 4) • x1 + (2 : ZMod 4) • x2 + (2 : ZMod 4) • y0 + (2 : ZMod 4) • y1 + (2 : ZMod 4) • y2) := by
        match_scalars <;> norm_num <;> decide
      _ = 0 := by rw [e0, e1, e2, e3, e4]; simp
  exact ⟨h0, h1, h2, sub_eq_zero.mp h3, sub_eq_zero.mp h4, sub_eq_zero.mp h5⟩
end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound.IntegralNormalization

namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
open Subgroup
open scoped IsMulCommutative
open Sporadic.LeechRelated.HS BlockNormalizer
namespace IntegralNormalization
local notation "Q" => pCore 2 baseNormalizer
variable {K : Type*} [CommGroup K] [Module (ZMod 4) (Additive K)]

private theorem conj_cube (n : baseNormalizer) (q : Q) :
    MulAut.conjNormal (n ^ 3) q =
      MulAut.conjNormal n (MulAut.conjNormal n (MulAut.conjNormal n q)) := by
  rw [map_pow]
  rfl

/-- With the third actor killed, the other six basis values are one involution. -/
theorem normalized_values (h : IntegralActionData) (β : CoreCrossedHom K)
    (hc : β.toFun (h.actor 2) = 1) :
    ∃ z : K, z ^ 2 = 1 ∧ ∀ i j, β.toFun (h.actor i) (integralBasis j) ∈ zpowers z := by
  have hc3 : β.toFun (h.actor 2 ^ 3) = 1 := by
    apply MonoidHom.ext
    intro q
    rw [show h.actor 2 ^ 3 = h.actor 2 * h.actor 2 * h.actor 2 by simp [pow_succ]]
    simp only [β.mul_rule, hc, MonoidHom.one_apply, one_mul]
  let x0 := Additive.ofMul (β.toFun (h.actor 0) (integralBasis 0))
  let x1 := Additive.ofMul (β.toFun (h.actor 0) (integralBasis 1))
  let x2 := Additive.ofMul (β.toFun (h.actor 0) (integralBasis 2))
  let y0 := Additive.ofMul (β.toFun (h.actor 1) (integralBasis 0))
  let y1 := Additive.ofMul (β.toFun (h.actor 1) (integralBasis 1))
  let y2 := Additive.ofMul (β.toFun (h.actor 1) (integralBasis 2))
  have e0 : x0 + (2 : ZMod 4) • x1 + (2 : ZMod 4) • x2 = 0 := by
    calc
      _ = Additive.ofMul (β.toFun (h.actor 0 * h.actor 0) (integralBasis 1)) := by
        simp only [β.mul_rule,
          h.on_basis, integralMatrixImage, map_mul, map_pow]
        norm_num [integralMatrices, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        simp only [← Nat.cast_smul_eq_nsmul (R := ZMod 4)]
        dsimp [x0, x1, x2, y0, y1, y2]
        match_scalars <;> norm_num
      _ = 0 := congrArg Additive.ofMul (by simpa only [← pow_two] using
        (value_core β h.square_zero (integralBasis 1)))
  have e1 : (3 : ZMod 4) • y0 + y1 = 0 := by
    calc
      _ = Additive.ofMul (β.toFun (h.actor 1 * h.actor 1) (integralBasis 2)) := by
        simp only [β.mul_rule,
          h.on_basis, integralMatrixImage, map_mul, map_pow]
        norm_num [integralMatrices, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        simp only [← Nat.cast_smul_eq_nsmul (R := ZMod 4)]
        dsimp [x0, x1, x2, y0, y1, y2]
        match_scalars <;> decide
      _ = 0 := congrArg Additive.ofMul (by simpa only [← pow_two] using
        (value_core β h.square_one (integralBasis 2)))
  have e2 : x1 + (2 : ZMod 4) • y0 + (3 : ZMod 4) • y1 + (3 : ZMod 4) • y2 = 0 := by
    calc
      _ = Additive.ofMul (β.toFun (h.actor 2 * h.actor 0) (integralBasis 1)) -
          Additive.ofMul (β.toFun (h.actor 1 * h.actor 2) (integralBasis 1)) := by
        simp only [β.mul_rule, hc, MonoidHom.one_apply,
          h.on_basis, integralMatrixImage, map_mul, map_pow]
        norm_num [integralMatrices, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        simp only [← Nat.cast_smul_eq_nsmul (R := ZMod 4)]
        dsimp [x0, x1, x2, y0, y1, y2]
        match_scalars <;> norm_num <;> decide
      _ = 0 := sub_eq_zero.mpr (congrArg Additive.ofMul
        (value_eq β h.conjugation_relation (integralBasis 1)))
  have e3 : x2 + y0 + (2 : ZMod 4) • y1 + (2 : ZMod 4) • y2 = 0 := by
    calc
      _ = Additive.ofMul (β.toFun (h.actor 2 * h.actor 0) (integralBasis 2)) -
          Additive.ofMul (β.toFun (h.actor 1 * h.actor 2) (integralBasis 2)) := by
        simp only [β.mul_rule, hc, MonoidHom.one_apply,
          h.on_basis, integralMatrixImage, map_mul, map_pow]
        norm_num [integralMatrices, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        simp only [← Nat.cast_smul_eq_nsmul (R := ZMod 4)]
        dsimp [x0, x1, x2, y0, y1, y2]
        match_scalars <;> norm_num <;> decide
      _ = 0 := sub_eq_zero.mpr (congrArg Additive.ofMul
        (value_eq β h.conjugation_relation (integralBasis 2)))
  have e4 : (2 : ZMod 4) • x0 + (3 : ZMod 4) • x1 + (2 : ZMod 4) • x2 + (2 : ZMod 4) • y0 + (2 : ZMod 4) • y1 + (2 : ZMod 4) • y2 = 0 := by
    calc
      _ = Additive.ofMul (β.toFun (h.actor 0 * h.actor 1 * h.actor 2 * h.actor 1 * h.actor 0) (integralBasis 0)) -
          Additive.ofMul (β.toFun (h.actor 1 * h.actor 2 ^ 3) (integralBasis 0)) := by
        simp only [β.mul_rule, hc, hc3, MonoidHom.one_apply, conj_cube]
        simp only [h.on_basis, integralMatrixImage, map_mul, map_pow]
        norm_num [integralMatrices, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        simp only [← Nat.cast_smul_eq_nsmul (R := ZMod 4)]
        dsimp [x0, x1, x2, y0, y1, y2]
        match_scalars <;> norm_num <;> decide
      _ = 0 := sub_eq_zero.mpr (congrArg Additive.ofMul
        (value_eq β h.long_relation (integralBasis 0)))
  have e5 : (2 : ZMod 4) • x0 + (3 : ZMod 4) • x2 + (2 : ZMod 4) • y0 + y1 + (2 : ZMod 4) • y2 = 0 := by
    calc
      _ = Additive.ofMul (β.toFun (h.actor 0 * h.actor 1 * h.actor 2 * h.actor 1 * h.actor 0) (integralBasis 1)) -
          Additive.ofMul (β.toFun (h.actor 1 * h.actor 2 ^ 3) (integralBasis 1)) := by
        simp only [β.mul_rule, hc, hc3, MonoidHom.one_apply, conj_cube]
        simp only [h.on_basis, integralMatrixImage, map_mul, map_pow]
        norm_num [integralMatrices, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        simp only [← Nat.cast_smul_eq_nsmul (R := ZMod 4)]
        dsimp [x0, x1, x2, y0, y1, y2]
        match_scalars <;> norm_num <;> decide
      _ = 0 := sub_eq_zero.mpr (congrArg Additive.ofMul
        (value_eq β h.long_relation (integralBasis 1)))
  obtain ⟨hz, hx0, hx1, hx2, hy0, hy1⟩ := six_relations x0 x1 x2 y0 y1 y2 e0 e1 e2 e3 e4 e5
  refine ⟨β.toFun (h.actor 1) (integralBasis 2), ?_, ?_⟩
  · apply Additive.ofMul.injective
    simpa only [ofMul_pow, ofMul_one, ← Nat.cast_smul_eq_nsmul (R := ZMod 4),
      Nat.cast_ofNat] using hz
  · have hx0' : β.toFun (h.actor 0) (integralBasis 0) = 1 := Additive.ofMul.injective hx0
    have hx1' : β.toFun (h.actor 0) (integralBasis 1) = 1 := Additive.ofMul.injective hx1
    have hx2' : β.toFun (h.actor 0) (integralBasis 2) = β.toFun (h.actor 1) (integralBasis 2) :=
      Additive.ofMul.injective hx2
    have hy0' : β.toFun (h.actor 1) (integralBasis 0) = β.toFun (h.actor 1) (integralBasis 2) :=
      Additive.ofMul.injective hy0
    have hy1' : β.toFun (h.actor 1) (integralBasis 1) = β.toFun (h.actor 1) (integralBasis 2) :=
      Additive.ofMul.injective hy1
    intro i j
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> decide
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> decide
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      (try simp only [hx0', hx1', hx2', hy0', hy1', hc, MonoidHom.one_apply]) <;>
      first | exact (zpowers _).one_mem | exact mem_zpowers _

theorem hasCyclicError_of_module (h : IntegralActionData) (β : CoreCrossedHom K) :
    β.HasCyclicError := by
  let t := correctionCharacter h β
  obtain ⟨z, hz, hvalues⟩ := normalized_values h (correct β t) (killed_third h β)
  exact ⟨t, z, hz, values_mem h (correct β t) (zpowers z) hvalues⟩

end IntegralNormalization
end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
open Subgroup
open scoped IsMulCommutative
open Sporadic.LeechRelated.HS BlockNormalizer

/-- Integral normalization for an arbitrary commutative target. Only the supplied
literal action certificate is assumed; the target need not be finite or have
exponent four. -/
public theorem CoreCrossedHom.hasCyclicError (h : IntegralActionData)
    {K : Type*} [CommGroup K] (β : CoreCrossedHom K) : β.HasCyclicError := by
  let T : Subgroup K := (powMonoidHom 4).ker
  have hT (x : T) : x ^ 4 = 1 := Subtype.ext x.property
  let : Module (ZMod 4) (Additive T) := AddCommGroup.zmodModule (fun x => by
    exact congrArg Additive.ofMul (hT x.toMul))
  let γ : CoreCrossedHom T := {
    toFun n := (β.toFun n).codRestrict T (fun q => by
      change β.toFun n q ^ 4 = 1
      rw [← map_pow, CoreGeometry.core_fourth_power, map_one])
    mul_rule n m q := Subtype.ext (β.mul_rule n m q)
    core_rule u := by
      apply MonoidHom.ext
      intro q
      apply Subtype.ext
      exact IntegralNormalization.value_core β u.property q }
  obtain ⟨t, z, hz, herr⟩ := IntegralNormalization.hasCyclicError_of_module h γ
  refine ⟨T.subtype.comp t, z.val, congrArg Subtype.val hz, ?_⟩
  intro n q
  have he : T.subtype (γ.toFun n q * t q / t (MulAut.conjNormal n q)) ∈
      (zpowers z).map T.subtype := Subgroup.mem_map.mpr ⟨_, herr n q, rfl⟩
  rw [MonoidHom.map_zpowers] at he
  exact he

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
