module
public import Theory.GroupTheory.MinusExtraspecialA5Count.Calculation
public import Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
import all Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
import all Theory.SpecificGroups.MinusExtraspecial.ModelFixedFour

/-!
# Transport of the two local counts to the minus-extraspecial group

The existing intrinsic five-point action detects a nonidentity even involution
as a permutation moving four singular points. The checked coordinate counts
therefore give eight cocycles and eight compatible core involutions for every
such automorphism of the actual model.

The internal `import all` dependencies reuse the coordinate conversion and
five-point action proofs from the preceding fusion calculation. Their private
coordinates do not appear in the public group-theoretic statement.
Source: Aschbacher, *Sporadic Groups* (1994), 47.1, printed p.259.
-/

open Subgroup
namespace MinusExtraspecial.FixedFourCalculation.Outside.Count

private theorem count_card (f : B → Bool) :
    Nat.card {x : B // f x = true} = all.countP f := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hall : all.toFinset = Finset.univ := by decide +kernel
  rw [← hall, List.Nodup.card_eq_countP (show all.Nodup by decide +kernel)]
  simp only [Bool.decide_eq_true]

public theorem model_counts (a : MulAut Model) (ha : a ^ 2 = 1)
    (heven : Equiv.Perm.sign (fivePointAction a) = 1)
    (hne : fivePointAction a ≠ 1) :
    Nat.card {d : Model // d * a d = 1} = 8 ∧
    Nat.card {d : Model // orderOf d = 2 ∧
      (d * a d = quaternion z ∨ (d * a d) ^ 2 = quaternion z)} = 8 := by
  let ap : alternatingGroup (Fin 5) := ⟨fivePointAction a, heven⟩
  have hap : orderOf ap = 2 := orderOf_eq_prime
    (Subtype.ext (by change fivePointAction a ^ 2 = 1; rw [← map_pow, ha, map_one]))
    (fun hh => hne (congrArg Subtype.val hh))
  have hs : (fivePointAction a).support.card = 4 := by
    rw [← Equiv.Perm.sum_cycleType,
      alternatingGroup.involution_cycleType_of_degree_le_six (by decide) ap hap]
    rfl
  have hr := relations_aut a
  simp only [relations, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, and_assoc] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hr
  have hi : invol (encode (a (generators 0))) (encode (a (generators 1)))
      (encode (a (generators 2))) (encode (a (generators 3))) := by
    apply List.all_eq_true.mpr
    intro g _
    apply beq_iff_eq.mpr
    apply equiv.injective
    change decode (word _ _ _ _ (word _ _ _ _ g)) = decode g
    rw [decode_word, decode_word]
    have hh := congrArg (fun b : MulAut Model => b (decode g)) ha
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
  have hc := calculation_all (encode (a (generators 0))) h1 _ h2 h3 _ h4 h5 h6
    _ h7 h8 h9 h10 hi ((moved_eq a).trans hs)
  let w := word (encode (a (generators 0))) (encode (a (generators 1)))
    (encode (a (generators 2))) (encode (a (generators 3)))
  constructor
  · let e : {d : B // mul d (w d) == 0} ≃ {d : Model // d * a d = 1} :=
      Equiv.subtypeEquiv equiv (fun d => by
        simp only [beq_iff_eq, ← equiv.injective.eq_iff]
        change decode (mul d (w d)) = decode 0 ↔ decode d * a (decode d) = 1
        rw [decode_mul, decode_word, decode_zero])
    rw [← Nat.card_congr e, count_card]
    exact hc.1
  · let e : {d : B // mul d d == 0 && d != 0 &&
        (mul d (w d) == 2 || mul (mul d (w d)) (mul d (w d)) == 2)} ≃
        {d : Model // orderOf d = 2 ∧
          (d * a d = quaternion z ∨ (d * a d) ^ 2 = quaternion z)} :=
      Equiv.subtypeEquiv equiv (fun d => by
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne,
          orderOf_eq_prime_iff]
        change (mul d d = 0 ∧ d ≠ 0) ∧
          (mul d (w d) = 2 ∨ mul (mul d (w d)) (mul d (w d)) = 2) ↔
          ((decode d) ^ 2 = 1 ∧ decode d ≠ 1) ∧
          (decode d * a (decode d) = quaternion z ∨
            (decode d * a (decode d)) ^ 2 = quaternion z)
        have he (x y : B) : x = y ↔ decode x = decode y := equiv.injective.eq_iff.symm
        simp only [ne_eq, he, decode_mul, w, decode_word, decode_zero,
          show decode 2 = quaternion z from rfl, pow_two])
    rw [← Nat.card_congr e, count_card]
    exact hc.2
end MinusExtraspecial.FixedFourCalculation.Outside.Count
