module

public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.PSL2.RootPrimeRank

/-!
# The actual odd PSL₂ field-degree bound in E.2.2

An actual subgroup of the source SQTK group marked as PSL₂(p^e) has an
odd elementary root subgroup of rank `e`. Strong quasithinness therefore
forces `e ≤ 2`, independently of the further minimal-parabolic hypotheses.
For the nonexceptional odd row (`|F| > 5`, `|F| ≠ 9`), this also forces
`p > 3`; the quadratic case automatically has field order one modulo eight.

These are source consequences, not a replacement for the centralizer,
automizer, or inner-field exclusions in E.2.2(2c), printed pp.215–216.
-/

public section

namespace CFSG.Quasithin.ChapterE.Structure
open BenderSuzuki.MatrixGroups

variable {H : Type*} [Group H] [Finite H]
variable {F : Type*} [Field F] [Finite F] {p e : ℕ} [Fact p.Prime]

/-- The literal marked subgroup in E.2.2 cannot have odd defining degree
larger than two. Only the source's strong quasithinness is needed. -/
theorem odd_linear_exponent_le_two (hH : IsStronglyQuasithin H)
    (K : Subgroup H) (eK : K ≃* PSL2MatrixGroup F)
    (ho : Odd p) (hF : Nat.card F = p ^ e) : e ≤ 2 := by
  let f := K.subtype.comp eK.symm.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp eK.symm.injective
  exact (Theory.PSL2.root_prime_rank_ge F hF).trans
    ((Theory.GroupTheory.primeRank_le_of_injective p f hf).trans (hH p Fact.out ho))

/-- Positivity of the field degree is derived from the actual finite field. -/
theorem odd_linear_exponent_eq_one_or_two (hH : IsStronglyQuasithin H)
    (K : Subgroup H) (eK : K ≃* PSL2MatrixGroup F)
    (ho : Odd p) (hF : Nat.card F = p ^ e) : e = 1 ∨ e = 2 := by
  have hb := odd_linear_exponent_le_two hH K eK ho hF
  have he : e ≠ 0 := by
    intro he
    have hc : Nat.card F = 1 := by simpa [he] using hF
    exact zero_ne_one ((Nat.card_eq_one_iff_unique.mp hc).1.elim (0 : F) 1)
  omega

/-- The genuine SQTK source input discharges the field and prime bounds
in the nonexceptional odd row; the fields of order five and nine retain
the separate binary model branches required by the source. -/
theorem odd_linear_source_parameters {κ : GroupClass}
    (hH : IsSQTK κ H) (K : Subgroup H) (eK : K ≃* PSL2MatrixGroup F)
    (ho : Odd p) (hF : Nat.card F = p ^ e)
    (hlarge : 5 < Nat.card F) (hnine : Nat.card F ≠ 9) :
    3 < p ∧ (e = 1 ∨ e = 2) := by
  have he := odd_linear_exponent_eq_one_or_two hH.stronglyQuasithin K eK ho hF
  refine ⟨?_, he⟩
  have hp : 3 ≤ p := (Nat.Prime.odd_iff Fact.out).mp ho
  by_contra! hsmall
  have hp3 : p = 3 := by omega
  rcases he with he | he
  · norm_num [hp3, he] at hF
    omega
  · norm_num [hp3, he] at hF
    exact hnine hF

omit [Field F] [Finite F] [Fact p.Prime] in
/-- The congruence in E.2.2(2c) follows automatically in the quadratic
case, without a Sylow or automizer recognition premise. -/
theorem odd_linear_quadratic_mod_eight (ho : Odd p)
    (hF : Nat.card F = p ^ 2) : Nat.card F % 8 = 1 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp ho
  have hb : p % 8 < 8 := Nat.mod_lt _ (by decide)
  have hr : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases hr with he | he | he | he <;> norm_num [hF, Nat.pow_mod, he]

end CFSG.Quasithin.ChapterE.Structure
