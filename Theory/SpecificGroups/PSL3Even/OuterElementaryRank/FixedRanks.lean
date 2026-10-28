module

public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.Reduction
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.Quartic
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.ModelBounds
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.FieldAction
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.GraphConjugacy
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.GraphFieldDescent
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient

/-!
# Fixed-group estimates from the three actual outer-involution models

Standard factorization and the fact that a linear involution is inner leave
precisely the field, graph and graph-field expressions. The standard graph
calculation and the linear and unitary rank theorems give the two estimates
consumed by `rank_le_of_fixed_calculations`. The three descent modules construct
the required conjugacy and whole fixed-group equivalences: field involutions
give PSL₃ over the quadratic fixed field, graph involutions give SL₂, and
graph-field involutions give a genuine projective special unitary group.

`fixed_estimates` discharges all three model-identification premises of the
retained conditional interface. Every standard outer involution has fixed
two-rank at most f, and graph-field involutions have fixed two-rank at most f-1.
No two-residual is substituted for a whole fixed group. The binary graph case
and unitary fixed-field degree one are retained. The elementary-actor application
requires only the independent outer-image bound and graph-field actor selection;
their final discharge belongs to the sharp-rank assembly.

Source: GLS3, Theorem 2.5.12 and §2.7; Aschbacher–Smith E.1.14(1),
printed p.214, and 16.1.4, printed p.1171.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace Matrix.PSL3Even.OuterElementaryRank.FixedRanks
open Matrix.PSL3.OuterSolvable
variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
/-- Eliminate the purely linear involution using its actual inner action.
No assertion about conjugacy or fixed-group identification is used here. -/
theorem outer_involution_cases (a : MulAut PSL(3,F)) (ha : a ∈ standard F)
    (hs : a ^ 2 = 1) (ho : a ∉ MulAut.innerSubgroup PSL(3,F)) :
    (∃ (g : GL (Fin 3) F) (σ : F ≃+* F), σ ≠ 1 ∧
      a = linearConj F g * fieldAction F σ) ∨
    (∃ g : GL (Fin 3) F, a = linearConj F g * graph F) ∨ IsGraphField a := by
  obtain ⟨g, σ, h | h⟩ := Matrix.PSL3.CartanActions.NormalizerForm.standard_factorization
    F field_linearConj graph_linearConj_exists field_commute_graph a ha
  · by_cases hσ : σ = 1
    · have he : a = linearConj F g := by simpa [hσ] using h
      apply False.elim
      apply ho
      rw [he]
      exact Matrix.PSL3.OddInvolutionFixed.linearConj_involution_inner g (he ▸ hs)
    · exact Or.inl ⟨g, σ, hσ, h⟩
  · by_cases hσ : σ = 1
    · exact Or.inr (Or.inl ⟨g, by simpa [hσ] using h⟩)
    · exact Or.inr (Or.inr ⟨g, σ, hσ, h⟩)

/-- A genuine graph-field involution forces an even field degree, so the
binary case of the sharper estimate is vacuous. -/
theorem isGraphField_even_degree {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (a : MulAut PSL(3,F)) (ha : IsGraphField a) (hs : a ^ 2 = 1) : Even f := by
  obtain ⟨g, σ, hne, rfl⟩ := ha
  obtain ⟨n, _, hfn, _⟩ :=
    fixedField_parameters hf hF σ (graphField_part_sq g σ hs) hne
  exact ⟨n, by omega⟩

/-- Construct precisely the uniform and mixed fixed-rank inputs from actual
model identifications. `fixed_estimates` below supplies these identifications. -/
theorem fixed_estimates_of_model_identifications {f : ℕ}
    (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (hfield : ∀ (g : GL (Fin 3) F) (σ : F ≃+* F), σ ≠ 1 →
      (linearConj F g * fieldAction F σ) ^ 2 = 1 →
      Nonempty ((linearConj F g * fieldAction F σ).fixedSubgroup ≃*
        PSL(3, FixedBy.subfield F σ)))
    (hgraph : ∀ g : GL (Fin 3) F, (linearConj F g * graph F) ^ 2 = 1 →
      ∃ c : MulAut PSL(3,F), MulAut.congr c (linearConj F g * graph F) = graph F)
    (hmixed : ∀ (g : GL (Fin 3) F) (σ : F ≃+* F), σ ≠ 1 →
      (linearConj F g * fieldAction F σ * graph F) ^ 2 = 1 →
      ∃ J : HermitianForm 3 F, J.conj = σ ∧
        Nonempty ((linearConj F g * fieldAction F σ * graph F).fixedSubgroup ≃*
          ProjectiveSpecialUnitaryMatrixGroup J)) :
    (∀ a : MulAut PSL(3,F), a ∈ standard F → a ^ 2 = 1 →
      a ∉ MulAut.innerSubgroup PSL(3,F) → primeRank 2 a.fixedSubgroup ≤ f) ∧
    (∀ a : MulAut PSL(3,F), IsGraphField a → a ^ 2 = 1 →
      primeRank 2 a.fixedSubgroup ≤ f - 1) := by
  have mixed : ∀ a : MulAut PSL(3,F), IsGraphField a → a ^ 2 = 1 →
      primeRank 2 a.fixedSubgroup ≤ f - 1 := by
    rintro _ ⟨g, σ, hne, rfl⟩ hs
    obtain ⟨J, hJ, ⟨e⟩⟩ := hmixed g σ hne hs
    exact graphField_fixed_rank_of_equiv hf hF _ σ (graphField_part_sq g σ hs) hne J hJ e
  refine ⟨?_, mixed⟩
  intro a ha hs ho
  rcases outer_involution_cases a ha hs ho with h | h | h
  · obtain ⟨g, σ, hne, rfl⟩ := h
    obtain ⟨e⟩ := hfield g σ hne hs
    exact (field_fixed_rank_of_equiv hf hF _ σ (field_part_sq g σ hs) hne e).le
  · obtain ⟨g, rfl⟩ := h
    obtain ⟨c, hc⟩ := hgraph g hs
    exact graph_fixed_rank_of_congr hF _ c hc
  · exact (mixed a h hs).trans (Nat.sub_le f 1)

/-- Application to the literal elementary-actor consumer. Model descent and
rank-two actor selection remain explicit and are not discharged by this lemma. -/
theorem actor_rank_of_model_identifications {f : ℕ}
    (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (hfield : ∀ (g : GL (Fin 3) F) (σ : F ≃+* F), σ ≠ 1 →
      (linearConj F g * fieldAction F σ) ^ 2 = 1 →
      Nonempty ((linearConj F g * fieldAction F σ).fixedSubgroup ≃*
        PSL(3, FixedBy.subfield F σ)))
    (hgraph : ∀ g : GL (Fin 3) F, (linearConj F g * graph F) ^ 2 = 1 →
      ∃ c : MulAut PSL(3,F), MulAut.congr c (linearConj F g * graph F) = graph F)
    (hmixed : ∀ (g : GL (Fin 3) F) (σ : F ≃+* F), σ ≠ 1 →
      (linearConj F g * fieldAction F σ * graph F) ^ 2 = 1 →
      ∃ J : HermitianForm 3 F, J.conj = σ ∧
        Nonempty ((linearConj F g * fieldAction F σ * graph F).fixedSubgroup ≃*
          ProjectiveSpecialUnitaryMatrixGroup J))
    (houterRank : primeRank 2 (standardOuter F) ≤ 2)
    (hselect : ∀ E : Subgroup (MulAut PSL(3,F)), IsElementaryAbelian 2 E →
      E ≤ standard F →
      primeRank 2 (E.map (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)))) = 2 →
      ∃ a ∈ E, IsGraphField a)
    (E : Subgroup (MulAut PSL(3,F))) (hE : IsElementaryAbelian 2 E)
    (hEO : ¬ E ≤ MulAut.innerSubgroup PSL(3,F)) : Group.rank E ≤ f + 1 := by
  obtain ⟨hfixed, hmixedFixed⟩ :=
    fixed_estimates_of_model_identifications hf hF hfield hgraph hmixed
  exact rank_le_of_fixed_calculations hf hF houterRank hfixed hmixedFixed hselect E hE hEO

/-- The two literal whole fixed-group bounds, with all model identifications
constructed from the involution equation. This retains every positive degree. -/
theorem fixed_estimates {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f) :
    (∀ a : MulAut PSL(3,F), a ∈ standard F → a ^ 2 = 1 →
      a ∉ MulAut.innerSubgroup PSL(3,F) → primeRank 2 a.fixedSubgroup ≤ f) ∧
    (∀ a : MulAut PSL(3,F), IsGraphField a → a ^ 2 = 1 →
      primeRank 2 a.fixedSubgroup ≤ f - 1) :=
  fixed_estimates_of_model_identifications hf hF
    semilinear_field_fixed_equiv (graph_involution_conjugate hf hF)
    GraphFieldDescent.exists_fixed_equiv_unitary

/-- Every standard outer involution of PSL₃(2ᶠ) has whole fixed-group
two-rank at most f. No descent or conjugacy hypothesis is required. -/
theorem outer_involution_fixed_rank_le {f : ℕ}
    (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (a : MulAut PSL(3,F)) (ha : a ∈ standard F) (hs : a ^ 2 = 1)
    (ho : a ∉ MulAut.innerSubgroup PSL(3,F)) : primeRank 2 a.fixedSubgroup ≤ f :=
  (fixed_estimates hf hF).1 a ha hs ho

/-- A literal graph-field involution has whole fixed-group two-rank at most
f-1, including f=2 and its full order-72 unitary fixed group. -/
theorem graphField_involution_fixed_rank_le {f : ℕ}
    (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (a : MulAut PSL(3,F)) (ha : IsGraphField a) (hs : a ^ 2 = 1) :
    primeRank 2 a.fixedSubgroup ≤ f - 1 :=
  (fixed_estimates hf hF).2 a ha hs

/-- Apply the proved fixed-group estimates to the literal elementary-actor
consumer. Only the independent outer-image and actor-selection inputs remain. -/
theorem actor_rank_of_outer_calculations {f : ℕ}
    (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (houterRank : primeRank 2 (standardOuter F) ≤ 2)
    (hselect : ∀ E : Subgroup (MulAut PSL(3,F)), IsElementaryAbelian 2 E →
      E ≤ standard F →
      primeRank 2 (E.map (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)))) = 2 →
      ∃ a ∈ E, IsGraphField a)
    (E : Subgroup (MulAut PSL(3,F))) (hE : IsElementaryAbelian 2 E)
    (hEO : ¬ E ≤ MulAut.innerSubgroup PSL(3,F)) : Group.rank E ≤ f + 1 :=
  rank_le_of_fixed_calculations hf hF houterRank
    (outer_involution_fixed_rank_le hf hF) (graphField_involution_fixed_rank_le hf hF)
    hselect E hE hEO

end Matrix.PSL3Even.OuterElementaryRank.FixedRanks
