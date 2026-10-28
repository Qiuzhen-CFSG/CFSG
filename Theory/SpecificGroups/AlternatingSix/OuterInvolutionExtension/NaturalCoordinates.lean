module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!
# Transposition coordinates for the natural A₆ extensions

An odd involution in S₆ has cycle type 2 or 2³. The exceptional
automorphism arising from the six pentads takes a representative of the
second type to the transposition (2 4). Conjugacy then treats the whole
class, and restriction to A₆ preserves the actual conjugation action.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192: the choice of six-point coordinates.
-/

public section

open Equiv Equiv.Perm Subgroup GLS3.Chapter5
open AlternatingSix.ShadowLocal

namespace AlternatingSix.OuterInvolutionExtension

private theorem odd_involution_cycleType (s : Perm (Fin 6))
    (hs : s ^ 2 = 1) (hodd : sign s = -1) :
    s.cycleType = {2} ∨ s.cycleType = {2, 2, 2} := by
  have ht := cycleType_of_pow_prime_eq_one hs
  have hbound := s.sum_cycleType_le
  rw [ht] at hbound
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hbound
  have hsign := sign_of_cycleType' s
  rw [ht] at hsign
  simp only [Multiset.map_replicate, Multiset.prod_replicate] at hsign
  have hcard : s.cycleType.card ≤ 3 := by omega
  interval_cases h : s.cycleType.card <;> simp_all

private theorem outer_triple_isSwap (s : Perm (Fin 6))
    (hs : s.cycleType = {2, 2, 2}) : (outerHom s).IsSwap := by
  let t : Perm (Fin 6) := swap 0 1 * swap 2 3 * swap 4 5
  have ht : t.cycleType = {2, 2, 2} := by decide +kernel
  have he : outerHom t = swap 2 4 := by
    apply Equiv.ext
    intro i
    fin_cases i <;> decide +kernel
  have ho : (outerHom t).IsSwap := he ▸ swap_isSwap_iff.mpr (by decide)
  have hc : IsConj t s := isConj_iff_cycleType_eq.mpr (ht.trans hs.symm)
  exact isSwap_iff_cycleType.mpr
    ((isConj_iff_cycleType_eq.mp (outerHom.map_isConj hc)).symm.trans
      (isSwap_iff_cycleType.mp ho))

/-- The exceptional six-point automorphism transports the actual conjugation action. -/
theorem outerAltAut_conjNormal (s : Perm (Fin 6)) :
    MulAut.congr outerAltAut (MulAut.conjNormal s) =
      MulAut.conjNormal (outerHom s) := by
  apply MulEquiv.ext
  intro k
  obtain ⟨x, rfl⟩ := outerAltAut.surjective k
  apply Subtype.ext
  change (outerAltAut (MulAut.conjNormal s (outerAltAut.symm (outerAltAut x)))).val = _
  rw [outerAltAut.symm_apply_apply]
  change outerHom (s * (x : Perm (Fin 6)) * s⁻¹) =
    outerHom s * outerHom x * (outerHom s)⁻¹
  simp only [map_mul, map_inv]

/-- Either odd involution class in the natural S₆ can be made a transposition
by changing the A₆ coordinates. -/
theorem natural_involution_transposition_coordinates (β : AutA6)
    (hβ : β ^ 2 = 1) (hn : β ∈ natural) (hout : β ∉ ShadowLocal.inner) :
    ∃ (a : MulAut A6) (s : Perm (Fin 6)), s.IsSwap ∧
      MulAut.congr a β = MulAut.conjNormal s := by
  obtain ⟨s, hs⟩ := hn
  have hs2 : s ^ 2 = 1 := by
    apply permutationAction_injective
    change MulAut.conjNormal (s ^ 2) = MulAut.conjNormal 1
    rw [map_pow, map_one, hs, hβ]
  have hodd : sign s = -1 := by
    rcases Int.units_eq_one_or (sign s) with hone | hneg
    · exact (hout ⟨⟨s, mem_alternatingGroup.mpr hone⟩,
        (MulAut.conjNormal_val).symm.trans hs⟩).elim
    · exact hneg
  rcases odd_involution_cycleType s hs2 hodd with ht | ht
  · refine ⟨MulEquiv.refl A6, s, isSwap_iff_cycleType.mpr ht, ?_⟩
    apply MulEquiv.ext
    intro x
    exact congrArg (fun f : AutA6 => f x) hs.symm
  · exact ⟨outerAltAut, outerHom s, outer_triple_isSwap s ht,
      hs ▸ outerAltAut_conjNormal s⟩

end AlternatingSix.OuterInvolutionExtension
