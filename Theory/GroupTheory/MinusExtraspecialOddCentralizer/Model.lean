module
public import Theory.GroupTheory.MinusExtraspecialOddCentralizer.Relations
public import Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
import all Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
import all Theory.SpecificGroups.MinusExtraspecial.ModelFixedFour

/-!
# Unique involution squares in the transposition centralizer

Transport the checked four-generator identities to actual automorphisms of
Q₈ * D₈. The fixed root and central inner-square conclusions use the
intrinsic action on the five singular central cosets. These are the model
inputs to the literal extension centralizer, rather than an assumed
isomorphism type of that centralizer.
Source application: Aschbacher–Smith 14.2.17(1), printed p.987.
-/

open Subgroup
namespace MinusExtraspecial.FixedFourCalculation.OddCentralizer
open Outside OddInvolution

private theorem calculated (a : MulAut Model) (ha : a ^ 2 = 1)
    (hs : (fivePointAction a).IsSwap) :
    (all.any fun x => word (encode (a (generators 0))) (encode (a (generators 1)))
      (encode (a (generators 2))) (encode (a (generators 3))) x == x && mul x x == 2) ∧
    (all.all fun d => d == 0 || d == 2 || mul d d != 0 ||
      word (encode (a (generators 0))) (encode (a (generators 1)))
        (encode (a (generators 2))) (encode (a (generators 3))) d != d ||
      all.any (rootPair (encode (a (generators 0))) (encode (a (generators 1)))
        (encode (a (generators 2))) (encode (a (generators 3))) d)) := by
  have hr := relations_aut a
  have hm : (encode (a (generators 1)),encode (a (generators 2)),
      encode (a (generators 3))) ∈ row (encode (a (generators 0))) := mem_row _ _ _ _ hr
  have hi : Outside.invol (encode (a (generators 0))) (encode (a (generators 1)))
      (encode (a (generators 2))) (encode (a (generators 3))) := by
    apply List.all_eq_true.mpr
    intro x _
    apply beq_iff_eq.mpr
    apply equiv.injective
    change decode (word _ _ _ _ (word _ _ _ _ x)) = decode x
    rw [decode_word,decode_word]
    exact congrArg (fun b : MulAut Model => b (decode x)) ha
  have hmov := (moved_eq a).trans (Equiv.Perm.card_support_eq_two.mpr hs)
  have hh := List.all_eq_true.mp (fixed_checked (encode (a (generators 0)))) _ hm
  simpa only [hi,hmov,beq_self_eq_true,Bool.and_self,Bool.not_true,
    Bool.false_or,Bool.and_eq_true] using hh

/-- Every involutory transposition automorphism fixes a square root of the
central involution, whether its fixed core is dihedral or quaternion. -/
public theorem exists_fixed_root (a : MulAut Model) (ha : a ^ 2 = 1)
    (hs : (fivePointAction a).IsSwap) :
    ∃ x : Model, a x = x ∧ x ^ 2 = quaternion z := by
  obtain ⟨x,_,hx⟩ := List.any_eq_true.mp (calculated a ha hs).1
  simp only [Bool.and_eq_true,beq_iff_eq] at hx
  refine ⟨decode x,?_,?_⟩
  · simpa only [decode_word] using congrArg decode hx.1
  · simpa only [decode_mul,←pow_two,show decode 2 = quaternion z from rfl] using
      congrArg decode hx.2

/-- A commuting automorphism whose square is inner by a fixed involution
has central inner square. This controls order-four elements in extensions. -/
public theorem square_inner_central (a b : MulAut Model) (ha : a ^ 2 = 1)
    (hs : (fivePointAction a).IsSwap) (hab : Commute a b)
    (d : Model) (hd : d ^ 2 = 1) (had : a d = d) (_hbd : b d = d)
    (hb : b ^ 2 = MulAut.conj d) : d = 1 ∨ d = quaternion z := by
  by_cases hd1 : d=1
  · exact Or.inl hd1
  by_cases hdz : d=quaternion z
  · exact Or.inr hdz
  exfalso
  have hdd : mul (encode d) (encode d) = 0 := by
    apply equiv.injective
    change decode (mul (encode d) (encode d)) = decode 0
    simpa only [decode_mul,decode_encode,decode_zero,←pow_two] using hd
  have hda : word (encode (a (generators 0))) (encode (a (generators 1)))
      (encode (a (generators 2))) (encode (a (generators 3))) (encode d) = encode d := by
    apply equiv.injective
    change decode (word _ _ _ _ (encode d)) = decode (encode d)
    simpa only [decode_word,decode_encode] using had
  have hd0 : encode d ≠ 0 := fun h => hd1 (by
    simpa only [decode_encode,decode_zero] using congrArg decode h)
  have hd2 : encode d ≠ 2 := fun h => hdz (by
    simpa only [decode_encode,show decode 2 = quaternion z from rfl] using congrArg decode h)
  have hh := List.all_eq_true.mp (calculated a ha hs).2 (encode d) (mem_all _)
  simp only [Bool.or_eq_true,beq_iff_eq,bne_iff_ne,hd0,hd2,hdd,hda,
    ne_eq,not_true_eq_false,false_or] at hh
  obtain ⟨x,_,hx⟩ := List.any_eq_true.mp hh
  simp only [rootPair,Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at hx
  obtain ⟨⟨⟨hax,hx2⟩,hdx⟩,hy⟩ := hx
  have hax' : a (decode x)=decode x := by simpa only [decode_word] using congrArg decode hax
  have hx2' : (decode x)^2=quaternion z := by
    simpa only [decode_mul,←pow_two,show decode 2 = quaternion z from rfl] using congrArg decode hx2
  have hbz : b (quaternion z)=quaternion z := by
    have hc : b (quaternion z) ∈ center Model := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      obtain ⟨v,rfl⟩ := b.surjective y
      simpa only [map_mul] using congrArg b
        (Subgroup.mem_center_iff.mp ((MinusExtraspecial.mem_center_iff _).mpr (Or.inr rfl)) v)
    exact ((MinusExtraspecial.mem_center_iff _).mp hc).resolve_left (fun h =>
      (by decide +kernel : quaternion z ≠ 1) (b.injective (h.trans (map_one b).symm)))
  have hfixed : a (b (decode x))=b (decode x) := by
    have hc := congrArg (fun c : MulAut Model => c (decode x)) hab.eq
    change a (b (decode x))=b (a (decode x)) at hc
    rwa [hax'] at hc
  have hbroot : (b (decode x))^2=quaternion z := by rw [←map_pow,hx2',hbz]
  have hbpair : b (decode x)=decode x ∨ b (decode x)=(decode x)⁻¹ := by
    have hh := List.all_eq_true.mp hy (encode (b (decode x))) (mem_all _)
    have hfix : word (encode (a (generators 0))) (encode (a (generators 1)))
        (encode (a (generators 2))) (encode (a (generators 3))) (encode (b (decode x))) =
        encode (b (decode x)) := by
      apply equiv.injective
      change decode (word _ _ _ _ _) = decode (encode _)
      simpa only [decode_word,decode_encode] using hfixed
    have hsq : mul (encode (b (decode x))) (encode (b (decode x)))=2 := by
      apply equiv.injective
      change decode (mul _ _) = decode 2
      simpa only [decode_mul,decode_encode,←pow_two,show decode 2 = quaternion z from rfl] using hbroot
    simp only [Bool.or_eq_true,bne_iff_ne,beq_iff_eq,hfix,hsq,ne_eq,
      not_true_eq_false,false_or] at hh
    rcases hh with h | h
    · exact Or.inl (by simpa only [decode_encode] using congrArg decode h)
    · exact Or.inr (by simpa only [decode_encode,decode_inv] using congrArg decode h)
  have hb2 : (b^2) (decode x)=decode x := by
    change b (b (decode x))=decode x
    rcases hbpair with he | he
    · rw [he,he]
    · rw [he,map_inv,he,inv_inv]
  rw [hb] at hb2
  apply hdx
  apply equiv.injective
  change decode (conj (encode d) x)=decode x
  simpa only [decode_conj,decode_encode] using hb2
end MinusExtraspecial.FixedFourCalculation.OddCentralizer
