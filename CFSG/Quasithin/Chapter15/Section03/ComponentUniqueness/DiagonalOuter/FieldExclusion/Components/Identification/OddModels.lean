module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.SimpleSection
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.OddModels.LinearTwo
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.OddModels.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.OddModels.InnerFixed
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.OddModels.OuterFixed

/-!
# Identification of the odd-characteristic field-component model

Three-rank two and the actual PSL₃(2) fixed component exclude every PSL₂(pᵉ)
entry of Theorem C. In either remaining three-dimensional family, the inner
centralizer calculation forces the involution to be outer. Its entire fixed
group is then ternary orthogonal, and its ordinary component identifies the
field prime as seven. The unitary torus calculation excludes PSU₃(7) by
three-rank, leaving an actual isomorphism with PSL₃(7).

The proof retains the original coefficient fields and Hermitian forms through
the component calculations, including the unitary Frobenius conjugation and
fixed-field convention. Only the surviving linear model is finally transported
to the canonical seven-element field.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, proof of 15.3.38,
printed p.1137; Theorem C, printed p.33.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification

variable {S : Type*} [Group S] [Finite S] (s : SimpleInput S)
include s

/-- The remaining odd models after the rank and torus exclusions. -/
theorem SimpleInput.odd_model_remaining (h : ChapterA.Section02.IsTheoremCOddModel S) :
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL S 3 p) ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ p % 3 ≠ 1 ∧ ClassicalGroup.IsPSU S 3 p) := by
  cases h with
  | linear_two p e hp ho he hmodel => exact (s.not_linear_two hp ho he hmodel).elim
  | linear_three p hp ho hmodel => exact .inl ⟨p, hp, ho, hmodel⟩
  | unitary_three p hp ho hmodel =>
    exact .inr ⟨p, hp, ho, fun hmod => s.not_unitary_three_of_mod_one hp hmod hmodel, hmodel⟩

omit [Finite S] in
/-- The ordinary fixed component forces the odd-prime linear parameter to be seven. -/
theorem SimpleInput.linear_three_prime_eq_seven {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hmodel : ClassicalGroup.IsPSL S 3 p) : p = 7 := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let : IsSimpleGroup S := s.simple
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
    e.symm.isSimpleGroup
  obtain ⟨D, hD, ⟨f⟩⟩ := s.exists_fixed_component_of_equiv e
  apply linear_outer_component_prime_eq_seven (s.not_isSolvable_of_equiv e)
    hp ho hcard (MulAut.congr e s.involution)
    (((MulAut.congr e).orderOf_eq s.involution).trans s.involution_order) ?_ hD f
  rintro ⟨k, hk⟩
  exact s.linear_three_involution_not_inner hp ho hcard e ⟨k, hk.symm⟩

omit [Finite S] in
/-- The unitary parameter is the fixed-field order; its matrix field still has order p². -/
theorem SimpleInput.unitary_three_prime_eq_seven {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hmodel : ClassicalGroup.IsPSU S 3 p) : p = 7 := by
  obtain ⟨E, hE, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  let : IsSimpleGroup S := s.simple
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    e.symm.isSimpleGroup
  obtain ⟨D, hD, ⟨f⟩⟩ := s.exists_fixed_component_of_equiv e
  apply unitary_outer_component_prime_eq_seven J hp ho hcard hconj
    (MulAut.congr e s.involution)
    (((MulAut.congr e).orderOf_eq s.involution).trans s.involution_order) ?_ hD f
  rintro ⟨k, hk⟩
  exact s.unitary_three_involution_not_inner hp ho J hcard hconj e ⟨k, hk.symm⟩

/-- The forced unitary parameter seven contradicts three-rank two. -/
theorem SimpleInput.not_unitary_three {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSU S 3 p := by
  intro hmodel
  have hp7 := s.unitary_three_prime_eq_seven hp ho hmodel
  exact s.not_unitary_three_of_mod_one hp (by rw [hp7]) hmodel

/-- The complete odd-characteristic branch of the field-component sieve in 15.3.38.
All three constructors of Theorem C are treated, with no further classification
or model-calculation premises. -/
theorem SimpleInput.odd_model_equiv_psl3_seven
    (h : ChapterA.Section02.IsTheoremCOddModel S) :
    Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7)) := by
  cases h with
  | linear_two p e hp ho he hmodel => exact (s.not_linear_two hp ho he hmodel).elim
  | linear_three p hp ho hmodel =>
    have hp7 := s.linear_three_prime_eq_seven hp ho hmodel
    exact linear_three_seven_equiv (hp7 ▸ hmodel)
  | unitary_three p hp ho hmodel => exact (s.not_unitary_three hp ho hmodel).elim

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
