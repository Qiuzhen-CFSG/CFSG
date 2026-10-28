module
public import Theory.GroupTheory.MinusExtraspecialOddInvolutions.Calculation
public import Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
import all Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
import all Theory.SpecificGroups.MinusExtraspecial.ModelFixedFour

/-!
# Correcting transposition lifts in a minus extraspecial group

Transport the kernel-checked norm certificate through the established five-bit
coordinates. The intrinsic five-point action, rather than an arbitrary quotient
marking, identifies a transposition. The resulting correction and fixed subgroup
count concern the literal quaternion–dihedral core.

Internal imports reuse coordinate conversion proofs; coordinates do not appear
in the public mathematical statements. Source application: Aschbacher–Smith
14.2.17(1), printed pp.986–987.
-/

open Subgroup
namespace MinusExtraspecial.FixedFourCalculation.OddInvolution
open Outside

private theorem calculated (a : MulAut Model)
    (hs : (fivePointAction a).IsSwap) :
    (∀ d : B,
      word (encode (a (generators 0))) (encode (a (generators 1)))
        (encode (a (generators 2))) (encode (a (generators 3))) d = d →
      squareInner (encode (a (generators 0))) (encode (a (generators 1)))
        (encode (a (generators 2))) (encode (a (generators 3))) d →
      ∃ q : B, mul (mul q (word (encode (a (generators 0))) (encode (a (generators 1)))
        (encode (a (generators 2))) (encode (a (generators 3))) q)) d = 0) ∧
    (Outside.invol (encode (a (generators 0))) (encode (a (generators 1)))
      (encode (a (generators 2))) (encode (a (generators 3))) →
      fixedCount (encode (a (generators 0))) (encode (a (generators 1)))
        (encode (a (generators 2))) (encode (a (generators 3))) = 8) := by
  have hr := relations_aut a
  simp only [relations, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, and_assoc] at hr
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ := hr
  exact calculation_all (encode (a (generators 0))) h1 _ h2 h3 _ h4 h5 h6
    _ h7 h8 h9 h10 ((moved_eq a).trans (Equiv.Perm.card_support_eq_two.mpr hs))

public theorem exists_norm_correction (a : MulAut Model)
    (hs : (fivePointAction a).IsSwap) (d : Model)
    (hd : a d = d) (ha : a ^ 2 = MulAut.conj d) :
    ∃ q : Model, q * a q * d = 1 := by
  have hfix : word (encode (a (generators 0))) (encode (a (generators 1)))
      (encode (a (generators 2))) (encode (a (generators 3))) (encode d) = encode d := by
    apply equiv.injective
    change decode (word _ _ _ _ _) = decode (encode d)
    rw [decode_word,decode_encode,hd]
  have hinner : squareInner (encode (a (generators 0))) (encode (a (generators 1)))
      (encode (a (generators 2))) (encode (a (generators 3))) (encode d) := by
    apply List.all_eq_true.mpr
    intro x _
    apply beq_iff_eq.mpr
    apply equiv.injective
    change decode (word _ _ _ _ (word _ _ _ _ x)) = decode (conj (encode d) x)
    rw [decode_word,decode_word,decode_conj,decode_encode]
    exact congrArg (fun b : MulAut Model => b (decode x)) ha
  obtain ⟨q,hq⟩ := (calculated a hs).1 (encode d) hfix hinner
  refine ⟨decode q,?_⟩
  have hh := congrArg decode hq
  simpa only [decode_mul,decode_word,decode_encode,decode_zero] using hh

public theorem fixed_card (a : MulAut Model) (ha : a ^ 2 = 1)
    (hs : (fivePointAction a).IsSwap) :
    Nat.card (a.toMonoidHom.eqLocus (MonoidHom.id Model)) = 8 := by
  have hi : Outside.invol (encode (a (generators 0))) (encode (a (generators 1)))
      (encode (a (generators 2))) (encode (a (generators 3))) := by
    apply List.all_eq_true.mpr
    intro x _
    apply beq_iff_eq.mpr
    apply equiv.injective
    change decode (word _ _ _ _ (word _ _ _ _ x)) = decode x
    rw [decode_word,decode_word]
    exact congrArg (fun b : MulAut Model => b (decode x)) ha
  let f := word (encode (a (generators 0))) (encode (a (generators 1)))
    (encode (a (generators 2))) (encode (a (generators 3)))
  let e : {x : B // f x = x} ≃ a.toMonoidHom.eqLocus (MonoidHom.id Model) :=
    Equiv.subtypeEquiv equiv (fun x => by
      change f x = x ↔ a (decode x) = decode x
      rw [←decode_word a x]
      exact equiv.injective.eq_iff.symm)
  rw [←Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hall : all.toFinset = Finset.univ := by decide +kernel
  have hnodup : all.Nodup := by decide +kernel
  rw [←hall,hnodup.card_eq_countP]
  exact (calculated a hs).2 hi
end MinusExtraspecial.FixedFourCalculation.OddInvolution
