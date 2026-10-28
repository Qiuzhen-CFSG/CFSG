module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.TranspositionMarking
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.TransvectionSections.Sieve

/-!
# Rank one in the natural-quotient transvection case

On either concrete degree-eight permutation module, every involution acting
as a transvection is odd. Apply the exhaustive offender marking to its cyclic
subgroup, then use sign to show that an elementary group consisting of
transvections has order two. This does not assume that the whole actor has
fixed codimension one.

For the literal maximal submodule and natural quotient in 13.8.25, the
critical-line sieve now closes the quotient-line case. It retains the other
case as a common displacement line inside the faithful submodule; identifying
transvections in that arbitrary S₈-module remains separate. The fixed-space
lifting and both fixed codimensions follow from the quadratic-family bound.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.22–25, printed pp.957–960, particularly p.960 (PDF p.977).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.TransvectionSections
open Representation.BinaryOffender Subgroup BinaryPermutation
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

private theorem odd_of_involution_transvection (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (hmodel : IsEightNaturalOrCover ρ eH)
    (a : H) (hne : a ≠ 1) (hpow : a ^ 2 = 1)
    (hc : fixedCodim ρ (zpowers a) = 1) : (eH a).sign = -1 := by
  have hA : IsElementaryTwo (zpowers a) :=
    ⟨by simpa using hne, IsElementaryAbelian.zpowers_of_pow_eq_one hpow⟩
  obtain ⟨_, g, hg, _⟩ := codim_one_actor_marking ρ eH hmodel (zpowers a) hA hc
  let e' := conjugateMarking eH g
  have hm : e' a ∈ transpositionGroup := by
    rw [← hg]
    exact mem_map_of_mem e'.toMonoidHom (mem_zpowers a)
  have hm' : e' a ∈ zpowers (Equiv.swap (0 : Fin 8) 1) := by
    simpa only [zpowers_eq_closure] using hm
  have hswap : (Equiv.swap (0 : Fin 8) 1).IsSwap := ⟨0, 1, by decide, rfl⟩
  rw [mem_zpowers_iff_mem_range_orderOf, hswap.orderOf] at hm'
  have he : e' a = Equiv.swap 0 1 := by
    obtain ⟨n, hn, hnval⟩ := Finset.mem_image.mp hm'
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · simp only [pow_zero] at hnval
      exact (hne (e'.injective (hnval.symm.trans e'.map_one.symm))).elim
    · simpa using hnval.symm
  have hs : (e' a).sign = -1 := he ▸ hswap.sign_eq
  have hconj : (e' a).sign = (eH a).sign := by
    change Equiv.Perm.sign (g * eH a * g⁻¹) = _
    rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
  exact hconj.symm.trans hs

/-- A group of transvections on either concrete degree-eight model has rank
one. This applies to individual elements, without assuming fixed codimension
one for the whole actor. -/
theorem rank_one_of_model_transvections [Finite H]
    (ρ : Representation (ZMod 2) H U) (eH : H ≃* Perm)
    (hmodel : IsEightNaturalOrCover ρ eH) {A : Subgroup H}
    (hA : IsElementaryTwo A)
    (ht : ∀ a ∈ A, a ≠ 1 → fixedCodim ρ (zpowers a) = 1) : rank A = 1 := by
  let : IsElementaryAbelian 2 A := hA.2
  exact rank_one_of_nonidentity_odd eH.toMonoidHom hA (fun a ha hn =>
    odd_of_involution_transvection ρ eH hmodel a hn
      (elemPow_eq_one_of_isElementaryAbelian a ha) (ht a ha hn))

/-- With the already selected natural quotient, the quotient-line branch
forces rank one. Only the submodule-line branch still needs recognition of
transvections in an arbitrary faithful S₈-module. -/
theorem rank_one_or_submodule_line [Finite H] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ)
    (eH : H ≃* Perm) (hmodelQ : IsEightNatural W.quotientRepresentation eH)
    (hW : Function.Injective W.toRepresentation)
    (hQ : Function.Injective W.quotientRepresentation)
    {A : Subgroup H} (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (D : Submodule (ZMod 2) U)
    (hcritical : D ≤ fixedSpace ρ A ∨ ∃ S : Submodule (ZMod 2) U,
      IsAtom S ∧ ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hdim : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A)
    (hnoW : ¬ ∃ B ≤ A, IsBestOffender W.toRepresentation B ∧
      IsStrongOffender W.toRepresentation B)
    (hnoQ : ¬ ∃ B ≤ A, IsBestOffender W.quotientRepresentation B ∧
      IsStrongOffender W.quotientRepresentation B) :
    (rank A = 1 ∧ fixedCodim W.toRepresentation A = 1 ∧
      fixedCodim W.quotientRepresentation A = 1 ∧ fixedCodim ρ A = 2 ∧
      (fixedSpace ρ A).map W.toSubmodule.mkQ = fixedSpace W.quotientRepresentation A) ∨
    (∃ S : Submodule (ZMod 2) U, IsAtom S ∧ S ≤ W.toSubmodule ∧
      W.toSubmodule ≤ D ∧ subspaceCommutator ρ W.toSubmodule A = S ∧
      (∀ a ∈ A, a ≠ 1 → fixedCodim W.toRepresentation (zpowers a) = 1)) := by
  obtain ⟨S, hS, _, h | h⟩ :=
    local_transvection_alternatives ρ W D hW hQ hA hcritical hdim hnoW hnoQ
  · exact Or.inr ⟨S, hS, h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩
  · have hr := rank_one_of_model_transvections W.quotientRepresentation eH
      (Or.inl hmodelQ) hA h.2.2.2.2
    obtain ⟨hw, hq, hu⟩ := faithful_sections_of_fixedCodim_le_two ρ W hW hQ hA.1 (by omega)
    exact Or.inl ⟨hr, hw, hq, hu,
      fixedSpace_quotient_eq_map_of_fixedCodim_eq ρ W A (by omega)⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.TransvectionSections
