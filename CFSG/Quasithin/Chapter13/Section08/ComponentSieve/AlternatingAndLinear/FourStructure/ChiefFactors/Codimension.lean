module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SectionTransport

/-!
# Codimension in the six-dimensional-factor exclusion

If W is not contained in D and dim(U/D) is at most two, the image of D
in U/W has codimension at most one. If a nontrivial actor is faithful on
U/W and centralizes that image, both the quotient codimension and fixed
codimension are one, and dim(U/D) is two. This proves the numerical equality
needed for critical-pair symmetry, retaining the literal quotient image.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.25, printed p.961. Producing W not contained
in D, the rank-two actor and the symmetry implication remains part of the
six-dimensional-factor argument. A strong offender in a rank-two elementary
actor is also shown to fill that actor, giving the equality of the two
critical subgroups once the rank-two hypothesis has been obtained.
-/

public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

theorem quotient_codimension_one_of_rank_two
    (W : Subrepresentation ρ) (D : Submodule (ZMod 2) U) (A : Subgroup H)
    (hfaith : Function.Injective W.quotientRepresentation) (hA : A ≠ ⊥)
    (hbound : Module.finrank (ZMod 2) (U ⧸ D) ≤ 2)
    (hWD : ¬ W.toSubmodule ≤ D)
    (hfix : D.map W.toSubmodule.mkQ ≤ fixedSpace W.quotientRepresentation A) :
    Module.finrank (ZMod 2) ((U ⧸ W.toSubmodule) ⧸ D.map W.toSubmodule.mkQ) = 1 ∧
      Module.finrank (ZMod 2) (U ⧸ D) = 2 ∧
      fixedCodim W.quotientRepresentation A = 1 := by
  have hpos : 0 < Module.finrank (ZMod 2)
      (W.toSubmodule ⧸ D.comap W.toSubmodule.subtype) := by
    apply Module.finrank_pos_iff.mpr
    apply Submodule.Quotient.nontrivial_iff.mpr
    intro he
    apply hWD
    intro w hw
    have hh : (⟨w, hw⟩ : W.toSubmodule) ∈ D.comap W.toSubmodule.subtype := by
      rw [he]; trivial
    exact hh
  have hdecomp := codim_decomposition W.toSubmodule D
  have he := (Submodule.quotientQuotientEquivQuotientSup W.toSubmodule D).finrank_eq
  have hpositive := fixedCodim_pos_of_faithful W.quotientRepresentation hfaith hA
  have hD := (D.map W.toSubmodule.mkQ).finrank_quotient_add_finrank
  have hF := fixedCodim_add_finrank W.quotientRepresentation A
  have hle := Submodule.finrank_mono hfix
  omega

/-- A strong offender inside a faithful action of a four-group fills that
four-group: its fixed codimension is positive, so its rank is at least two. -/
theorem eq_four_group_of_contains_strong_offender [Finite H]
    (hfaith : Function.Injective ρ) (A V : Subgroup H) (hAV : A ≤ V)
    (hV : IsElementaryTwo V) (hVrank : rank V = 2)
    (hstrong : ∃ B ≤ A, IsStrongOffender ρ B) :
    A = V ∧ rank A = 2 ∧ Nat.card A = 4 := by
  obtain ⟨B, hBA, hB⟩ := hstrong
  have hBV := hBA.trans hAV
  have hpos := fixedCodim_pos_of_faithful ρ hfaith hB.1.1
  have hle : rank B ≤ rank V := Nat.log_monotone (Subgroup.card_le_of_le hBV)
  have hr : rank B = 2 := by have hs := hB.2; omega
  have he : B = V := Subgroup.eq_of_le_of_card_ge hBV (by
    rw [hB.1.card_eq_two_pow_rank, hV.card_eq_two_pow_rank, hr, hVrank])
  have hAVeq : A = V := le_antisymm hAV (he ▸ hBA)
  refine ⟨hAVeq, hAVeq.symm ▸ hVrank, ?_⟩
  rw [hAVeq, hV.card_eq_two_pow_rank, hVrank]
  norm_num

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
