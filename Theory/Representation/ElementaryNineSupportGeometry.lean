module
public import Theory.Representation.ElementaryNineFixedDecomposition
public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.Representation.BinaryOffender.CubicMovedRank
import Mathlib.Tactic

/-!
# The geometry of three four-dimensional cubic supports

The four cubic-line fixed spaces of an elementary nine-group form a direct
sum when the whole group has no fixed vectors. If three lines move four
dimensions, their fixed dimensions are all n − 4. Summing them with the fourth
fixed space gives n ≤ 6. Faithfulness and binary cubic parity force n = 6;
the fourth fixed space is zero. Four support-four lines would instead give
3n = 16, so there are always at most three.

This numerical geometry is used in Aschbacher–Smith D.2.28–29, pp.191–192.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped BigOperators
namespace Representation.ElementaryNineSupportGeometry
variable {A V : Type*} [Group A] [Finite A] [IsElementaryAbelian 3 A]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) A V)

omit [IsElementaryAbelian 3 A] in
private theorem fixed_add_moved (K : Subgroup A) (hK : Nat.card K = 3) :
    Module.finrank (ZMod 2) (fixedSpace ρ K) +
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K) = Module.finrank (ZMod 2) V := by
  have hc : IsCompl (fixedSpace ρ K) (subspaceCommutator ρ ⊤ K) := by
    simpa only [RegularCyclicNormalClosure.displacementSpan, subspaceCommutator, eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) (show Odd (Nat.card K) by rw [hK]; decide))
  exact Submodule.finrank_add_eq_of_isCompl hc

/-- At most three cubic lines have four-dimensional support. -/
theorem card_support_four_le_three
    (hA : Nat.card A = 9)
    (hfixed : fixedSpace ρ ⊤ = ⊥) :
    Nat.card {K : {K : Subgroup A // Nat.card K = 3} //
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K.val) = 4} ≤ 3 := by
  classical
  let I := {K : Subgroup A // Nat.card K = 3}
  let : Fintype I := Fintype.ofFinite I
  have hsum := ElementaryNineFixedDecomposition.sum_fixed_finrank_eq ρ hA hfixed
  let s : Finset I := Finset.univ.filter fun K =>
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K.val) = 4
  have hi : Fintype.card I = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact IsElementaryAbelian.TernarySylowLine.card_cubic_subgroups hA
  have hs : Nat.card {K : I //
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K.val) = 4} = s.card := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, s]
  rw [hs]
  have hb : s.card ≤ 4 := hi ▸ Finset.card_le_univ s
  by_contra hn
  have hc : s.card = 4 := by omega
  have he : s = Finset.univ := Finset.eq_univ_of_card s (hc.trans hi.symm)
  have hm (K : I) : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K.val) = 4 := by
    have hh : K ∈ s := by rw [he]; exact Finset.mem_univ _
    exact (Finset.mem_filter.mp hh).2
  have hh := Finset.sum_congr (s₁ := (Finset.univ : Finset I)) rfl
    (fun K _ => fixed_add_moved ρ K.val K.property)
  simp only [Finset.sum_add_distrib, hm, Finset.sum_const, Finset.card_univ,
    hi, nsmul_eq_mul, Nat.cast_id] at hh
  have htotal : (∑ K : I, Module.finrank (ZMod 2) (fixedSpace ρ K.val)) =
      Module.finrank (ZMod 2) V := hsum
  omega

/-- Three support-four cubic lines determine three fixed planes and a unique
fixed-point-free fourth line, on a six-dimensional binary space. -/
theorem geometry
    (hA : Nat.card A = 9) (hf : Function.Injective ρ)
    (hfixed : fixedSpace ρ ⊤ = ⊥)
    (hS : Nat.card {K : {K : Subgroup A // Nat.card K = 3} //
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K.val) = 4} = 3) :
    Module.finrank (ZMod 2) V = 6 ∧
    (∀ K : Subgroup A, Nat.card K = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K) = 4 →
      Module.finrank (ZMod 2) (fixedSpace ρ K) = 2) ∧
    ∃ Z : Subgroup A, Nat.card Z = 3 ∧ fixedSpace ρ Z = ⊥ ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 6 ∧
      ∀ K : Subgroup A, Nat.card K = 3 →
        (K ≠ Z ↔ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K) = 4) := by
  classical
  let I := {K : Subgroup A // Nat.card K = 3}
  let : Fintype I := Fintype.ofFinite I
  have hsum := ElementaryNineFixedDecomposition.sum_fixed_finrank_eq ρ hA hfixed
  let s : Finset I := Finset.univ.filter fun K =>
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K.val) = 4
  have hs : s.card = 3 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, s] using hS
  have hi : Fintype.card I = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact IsElementaryAbelian.TernarySylowLine.card_cubic_subgroups hA
  obtain ⟨Z,hZ⟩ := Finset.card_eq_one.mp (show sᶜ.card = 1 by rw [Finset.card_compl,hi,hs])
  have hnot : Z ∉ s := by
    have hh : Z ∈ sᶜ := by rw [hZ]; exact Finset.mem_singleton_self _
    exact Finset.mem_compl.mp hh
  have hchar (K : I) : K ≠ Z ↔ K ∈ s := by
    have hh : (K ∉ s) ↔ K = Z := by rw [← Finset.mem_compl, hZ, Finset.mem_singleton]
    simpa only [not_not] using (not_congr hh).symm
  have hsplit (K : I) := fixed_add_moved ρ K.val K.property
  have hsval (K : I) (hK : K ∈ s) :
      Module.finrank (ZMod 2) (fixedSpace ρ K.val) = Module.finrank (ZMod 2) V - 4 := by
    have hh := (Finset.mem_filter.mp hK).2
    have hk := hsplit K
    omega
  have hsumS : ∑ K ∈ s, Module.finrank (ZMod 2) (fixedSpace ρ K.val) =
      3 * (Module.finrank (ZMod 2) V - 4) := by
    rw [Finset.sum_congr rfl hsval]
    simp only [Finset.sum_const, hs, nsmul_eq_mul, Nat.cast_id]
  have hsumAll : 3 * (Module.finrank (ZMod 2) V - 4) +
      Module.finrank (ZMod 2) (fixedSpace ρ Z.val) = Module.finrank (ZMod 2) V := by
    have hh := Finset.sum_add_sum_compl s (fun K => Module.finrank (ZMod 2) (fixedSpace ρ K.val))
    rw [hsumS, hZ, Finset.sum_singleton] at hh
    exact hh.trans hsum
  have hlow : 4 ≤ Module.finrank (ZMod 2) V := by
    obtain ⟨K,hK⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
    have hh := hsplit K
    have hk := (Finset.mem_filter.mp hK).2
    omega
  have heven : 2 ∣ Module.finrank (ZMod 2) V := by
    have hh := orderOf_two_dvd_fixedCodim_of_isPGroup ρ Nat.prime_three (by decide) ⊤
      ((IsElementaryAbelian.isPGroup 3 A).to_subgroup ⊤)
    have ho : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
    have hd := fixedCodim_add_finrank ρ ⊤
    rw [hfixed, finrank_bot, add_zero] at hd
    rwa [ho, hd] at hh
  have hzlow := two_le_finrank_subspaceCommutator_of_card_three ρ Z.val hf Z.property
  have hzsplit := hsplit Z
  have hdim : Module.finrank (ZMod 2) V = 6 := by omega
  have hzfix : Module.finrank (ZMod 2) (fixedSpace ρ Z.val) = 0 := by omega
  refine ⟨hdim, ?_, Z.val, Z.property, ?_, ?_, ?_⟩
  · intro K hK hm
    have hh := fixed_add_moved ρ K hK
    omega
  · exact Submodule.finrank_eq_zero.mp hzfix
  · omega
  · intro K hK
    have hh := hchar ⟨K,hK⟩
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hh
    constructor
    · intro hn
      exact hh.mp (fun he => hn (congrArg Subtype.val he))
    · intro hm he
      exact hh.mpr hm (Subtype.ext he)

end Representation.ElementaryNineSupportGeometry
