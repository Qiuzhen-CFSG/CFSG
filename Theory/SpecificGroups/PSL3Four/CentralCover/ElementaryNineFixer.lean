module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.ProjectiveFixer
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage

/-!
# Pointwise fixers of elementary-nine subgroups in the four-cover

An elementary-nine subgroup projects faithfully through the central four.
Its image has the full three-part of the projective group order, hence is a
Sylow subgroup. Sylow conjugacy transports the concrete pointwise-fixer
calculation. The result concerns the full automorphism group, using the
proved binary projective automorphism coverage.

Source: Aschbacher–Smith 15.3.38, printed pp.1136–1137.
-/

public noncomputable section
namespace Matrix.PSL3Four
open Subgroup ExtendedCentralizer
variable {E : Type*} [Group E]

/-- Every elementary-nine subgroup embeds under the specified four-cover. -/
theorem FourCover.elementaryNine_projection_injective (c : FourCover E)
    (P : Subgroup E) (e : P ≃* ElementaryNine) :
    Function.Injective (c.toMonoidHom.comp P.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  let := c.center_isKleinFour
  have hz : (x : E) ∈ center E := c.ker_le_center hx
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    have hh := Monoid.pow_exponent_eq_one (⟨x, hz⟩ : center E)
    rw [IsKleinFour.exponent_two] at hh
    exact congrArg (fun z : center E => (z : E)) hh
  have hx3 : x ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    change (3 : ℕ) • (e x).toAdd = 0
    exact ZModModule.char_nsmul_eq_zero 3 _
  rw [pow_succ, hx2, one_mul] at hx3
  exact hx3

/-- The pointwise fixer of the actual projected elementary-nine subgroup
has order dividing eighteen. -/
theorem FourCover.elementaryNine_quotientFixer_card_dvd (c : FourCover E)
    (P : Subgroup E) (e : P ≃* ElementaryNine) :
    Nat.card (fixingSubgroup (MulAut PSL) (P.map c.toMonoidHom : Set PSL)) ∣ 18 := by
  have hc : Nat.card P = 9 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [ElementaryNine, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  have hq : Nat.card (P.map c.toMonoidHom) = 9 := by
    have he := Nat.card_congr (MonoidHom.ofInjective
      (c.elementaryNine_projection_injective P e)).toEquiv
    rw [MonoidHom.range_comp, range_subtype] at he
    exact he.symm.trans hc
  let Q : Sylow 3 PSL := Sylow.ofCard (P.map c.toMonoidHom) (by
    rw [hq, card_PSL]
    decide +kernel)
  have he := ProjectiveFixer.sylow_fixer_card Q
  rw [show (Q : Subgroup PSL) = P.map c.toMonoidHom from Sylow.coe_ofCard _ _,
    ProjectiveFixer.model_fixer_eq_candidate] at he
  have hstd : PSL3.OuterSolvable.standard F = ⊤ :=
    PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (m := 2) (by decide) card_F
  have hd : Nat.card (ProjectiveFixer.fixer (P.map c.toMonoidHom)) ∣ 18 := by
    rw [he]
    exact ProjectiveFixer.candidate_card_dvd
  simpa only [ProjectiveFixer.fixer, hstd, top_inf_eq] using hd

end Matrix.PSL3Four
end
