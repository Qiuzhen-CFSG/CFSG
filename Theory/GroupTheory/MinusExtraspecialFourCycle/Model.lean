module
public import Theory.GroupTheory.MinusExtraspecialFourCycle.Calculation
public import Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
import all Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
import all Theory.SpecificGroups.MinusExtraspecial.ModelFixedFour
public import Theory.SpecificGroups.MinusExtraspecial.CentralStructure

/-!
# Correcting a four-cycle lift in the minus extraspecial model

Transport the checked norm certificate through the established five-bit
coordinates of Q₈ * D₈. The permutation is the actual action on the five
singular central cosets. A corrected fourth norm belongs to the center;
no splitting or order-four lift is assumed.
The internal imports reuse the coordinate and five-point action proofs.
Source application: Aschbacher–Smith 14.2.17(1), printed p.987.
-/

open Subgroup
namespace MinusExtraspecial.FixedFourCalculation.FourCycle
open Outside

public def cycle : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3

public theorem cycle_fourth : cycle ^ 4 = 1 := by decide +kernel
public theorem cycle_square_ne : cycle ^ 2 ≠ 1 := by decide +kernel
public theorem cycle_square_even : Equiv.Perm.sign (cycle ^ 2) = 1 := by decide +kernel

public theorem exists_central_fourth_norm (a : MulAut Model)
    (haction : fivePointAction a = cycle) (d : Model)
    (hd : a d = d) (ha : a ^ 4 = MulAut.conj d) :
    ∃ q : Model, q * a q * a (a q) * a (a (a q)) * d ∈ center Model := by
  let u := encode (a (generators 0))
  let v := encode (a (generators 1))
  let r := encode (a (generators 2))
  let s := encode (a (generators 3))
  have hc : cyclic u v r s := by
    have h0 := (action_eq_iff a 0 1).mp (by rw [haction]; decide)
    have h1 := (action_eq_iff a 1 2).mp (by rw [haction]; decide)
    have h2 := (action_eq_iff a 2 3).mp (by rw [haction]; decide)
    have h3 := (action_eq_iff a 3 0).mp (by rw [haction]; decide)
    have h4 := (action_eq_iff a 4 4).mp (by rw [haction]; decide)
    have hw (x : B) : word u v r s x = encode (a (decode x)) := by
      rw [←decode_word a x,encode_decode]
    simp only [cyclic,hw,Bool.and_eq_true,beq_iff_eq]
    exact ⟨⟨⟨⟨h0,h1⟩,h2⟩,h3⟩,h4⟩
  have hfix : word u v r s (encode d) = encode d := by
    apply equiv.injective
    change decode (word _ _ _ _ _) = decode (encode d)
    rw [decode_word,decode_encode,hd]
  have hi : fourthInner u v r s (encode d) := by
    apply List.all_eq_true.mpr
    intro x _
    apply beq_iff_eq.mpr
    apply equiv.injective
    change decode (word _ _ _ _ (word _ _ _ _ (word _ _ _ _ (word _ _ _ _ x)))) =
      decode (conj (encode d) x)
    rw [decode_word,decode_word,decode_word,decode_word,decode_conj,decode_encode]
    have hh := congrArg (fun b : MulAut Model => b (decode x)) ha
    simpa only [show (4:Nat)=2+2 from rfl,pow_add,pow_two,MulAut.mul_apply] using hh
  obtain ⟨q,hq⟩ := calculation u v r s (encode d) (relations_aut a) hc hfix hi
  refine ⟨decode q,?_⟩
  have he : decode (norm u v r s q (encode d)) =
      decode q * a (decode q) * a (a (decode q)) * a (a (a (decode q))) * d := by
    simp only [norm,decode_mul,decode_word,decode_encode,u,v,r,s]
  rcases hq with hq | hq
  · apply (MinusExtraspecial.mem_center_iff _).mpr
    exact Or.inl (he.symm.trans (congrArg decode hq))
  · apply (MinusExtraspecial.mem_center_iff _).mpr
    exact Or.inr (he.symm.trans (congrArg decode hq))
end MinusExtraspecial.FixedFourCalculation.FourCycle
