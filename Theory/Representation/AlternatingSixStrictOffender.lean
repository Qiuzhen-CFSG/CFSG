module
public import Theory.Representation.AlternatingSixInvolutionDisplacement
public import Theory.Representation.BinaryOffender.FaithfulRankOne

/-!
# Small strict offenders in a faithful binary S6 action

A strict offender of order at most eight cannot have order at most two,
by faithfulness. A larger elementary actor contains an even involution;
the binary A6 displacement bound then forces fixed codimension at least two.
The strict cardinal inequality consequently forces order eight and fixed
codimension two. The original S6 action and actor subgroup are retained.

Source application: Meierfrankenfeld--Stellmacher (1993), (3.6), p.871.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.AlternatingSixInvolutionDisplacement
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem even_element_of_card_gt_two (A : Subgroup (Equiv.Perm (Fin 6)))
    (hA : 2 < Nat.card A) :
    ∃ a ∈ A, a ∈ alternatingGroup (Fin 6) ∧ a ≠ 1 := by
  by_contra! hn
  let f := Equiv.Perm.sign.comp A.subtype
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro a ha
    apply Subtype.ext
    exact hn a a.property ((Equiv.Perm.mem_alternatingGroup).mpr ha)
  have hh := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := ℤˣ),Fintype.card_units_int] at hh
  omega

theorem strict_small_elementary_card
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (hf : Function.Injective ρ) (A : Subgroup (Equiv.Perm (Fin 6)))
    [IsElementaryAbelian 2 A] (hsmall : Nat.card A ≤ 8)
    (hstrict : 2 * 2 ^ fixedCodim ρ A ≤ Nat.card A) :
    Nat.card A = 8 ∧ fixedCodim ρ A = 2 := by
  have hA : A ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hstrict
    have : 0 < 2 ^ fixedCodim ρ ⊥ := by positivity
    omega
  have hpos := fixedCodim_pos_of_faithful ρ hf hA
  have htwo : 2 ≤ 2 ^ fixedCodim ρ A := by
    exact (show 2^1 ≤ 2 ^ fixedCodim ρ A from Nat.pow_le_pow_right (by decide) hpos)
  obtain ⟨a,ha,he,ha1⟩ := even_element_of_card_gt_two A (by omega)
  have hao : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  have hρ : ∃ g : alternatingGroup (Fin 6), ρ g ≠ 1 := by
    refine ⟨⟨a,he⟩,?_⟩
    intro hz
    exact ha1 (hf (hz.trans (map_one ρ).symm))
  have hlo := fixedCodim_lower_of_even_involution_mem ρ hρ a hao he ha
  have hp : 4 ≤ 2 ^ fixedCodim ρ A :=
    show 2^2 ≤ 2 ^ fixedCodim ρ A from Nat.pow_le_pow_right (by decide) hlo
  have hcard : Nat.card A = 8 := by omega
  refine ⟨hcard,le_antisymm ?_ hlo⟩
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  change 2 ^ fixedCodim ρ A ≤ 4
  omega

end Representation.AlternatingSixInvolutionDisplacement
