module
public import Theory.SpecificGroups.PSL3Even.InvolutionResidualRows
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm

/-!
# The four involution rows for binary PSL₃

The standard automorphism factorization, quadratic descent, and root conjugacy
supply the four alternatives in Aschbacher--Smith 16.1.4(1),(4)--(6), printed
pp.1170--1171. Every row retains its actual matrix action. Only the comparison
of a twisted degree-two graph-field action with the standard GF(4) action
remains explicit; its fixed-residual calculation is already proved.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix BenderSuzuki.MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.LinearThree
open Matrix.PSL3Even.OuterElementaryRank.FixedRanks
namespace Matrix.PSL3Even.InvolutionResidualRows
variable {F : Type*} [Field F] [Finite F]

/-- The inner row includes the proper parabolic and the embedded local residual. -/
@[expose] def RootParabolicCase (a : MulAut PSL(3,F)) : Prop :=
  ∃ c : MulAut PSL(3,F), (∃ g : PSL(3,F), c = MulAut.conj g) ∧
    MulAut.congr c a = MulAut.conj (Matrix.PSL3.EvenInnerCentralizers.root F) ∧
    (pointParabolic F).comap c.toMonoidHom < ⊤ ∧
    a.fixedSubgroup ≤ (pointParabolic F).comap c.toMonoidHom ∧
    MulAut.embeddedFixedResidual 2 a =
      ((pResidual 2 (a.fixedSubgroup.subgroupOf ((pointParabolic F).comap c.toMonoidHom))).map
        (a.fixedSubgroup.subgroupOf ((pointParabolic F).comap c.toMonoidHom)).subtype).map
          ((pointParabolic F).comap c.toMonoidHom).subtype

/-- The field row retains a conjugator to the nontrivial coefficient involution. -/
@[expose] def FieldCase (n : ℕ) (a : MulAut PSL(3,F)) : Prop :=
  ∃ (g : GL (Fin 3) F) (σ : F ≃+* F), σ ≠ 1 ∧
    a = linearConj F g * fieldAction F σ ∧ σ ^ 2 = 1 ∧
    (∃ c : GL (Fin 3) F, MulAut.congr (linearConj F c) a = fieldAction F σ) ∧
    ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧ Nat.card (FixedBy.subfield F σ) = 2 ^ m ∧
      Nonempty (pResidual 2 a.fixedSubgroup ≃* commutator PSL(3, FixedBy.subfield F σ))

/-- The graph row retains conjugacy of actions and the derived PSL₂ endpoint. -/
@[expose] def GraphCase (a : MulAut PSL(3,F)) : Prop :=
  ∃ g : GL (Fin 3) F, a = linearConj F g * graph F ∧
    (∃ c : MulAut PSL(3,F), MulAut.congr c a = graph F) ∧
    Nonempty (pResidual 2 a.fixedSubgroup ≃* commutator PSL(2,F))

/-- The mixed row distinguishes degree two from all larger quadratic fields. -/
@[expose] def GraphFieldCase (n : ℕ) (a : MulAut PSL(3,F)) : Prop :=
  ∃ (g : GL (Fin 3) F) (σ : F ≃+* F), σ ≠ 1 ∧
    a = linearConj F g * fieldAction F σ * graph F ∧ σ ^ 2 = 1 ∧ Even n ∧
    ((n = 2 ∧ Nonempty (pResidual 2 a.fixedSubgroup ≃* Multiplicative (Fin 2 → ZMod 3))) ∨
      ∃ (m : ℕ) (J : HermitianForm 3 F), 1 < m ∧ n = 2 * m ∧ J.conj = σ ∧
        J.form = !![0,0,1; 0,1,0; 1,0,0] ∧ (∀ x, J.conj x = x ^ (2 ^ m)) ∧
        Nat.card F = (2 ^ m) ^ 2 ∧ Nat.card {x : F // J.conj x = x} = 2 ^ m ∧
        Nonempty (pResidual 2 a.fixedSubgroup ≃* ProjectiveSpecialUnitaryMatrixGroup J))

/-- Exhaustive source rows, conditional only on the indicated degree-two
marking. In particular no classification or proper-K assumption is used. -/
theorem involution_cases_of_four_marking {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (hsmall : FourGraphFieldMarking F)
    (a : MulAut PSL(3,F)) (ha : orderOf a = 2) :
    RootParabolicCase a ∨ FieldCase n a ∨ GraphCase a ∨ GraphFieldCase n a := by
  have hs : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  by_cases hi : ∃ t, a = MulAut.conj t
  · exact Or.inl (inner_row hn hF a ha hi)
  have hcover := standard_eq_top_of_two_power_card F hn hF
  obtain ⟨g, σ, he | he⟩ := Matrix.PSL3.CartanActions.NormalizerForm.standard_factorization
    F field_linearConj graph_linearConj_exists field_commute_graph a
      (hcover.symm ▸ mem_top a)
  · have hne : σ ≠ 1 := by
      intro hσ
      have hlin : a = linearConj F g := by simpa only [hσ, map_one, mul_one] using he
      obtain ⟨t, ht⟩ := Matrix.PSL3.OddInvolutionFixed.linearConj_involution_inner g (hlin ▸ hs)
      exact hi ⟨t, hlin.trans ht.symm⟩
    obtain ⟨m, hm, hnm, hK, hσ, hc, hr⟩ := field_row hn hF g σ hne (he ▸ hs)
    exact Or.inr (Or.inl ⟨g, σ, hne, he, hσ, he.symm ▸ hc, m, hm, hnm, hK, he.symm ▸ hr⟩)
  · by_cases hσ : σ = 1
    · have hg : a = linearConj F g * graph F := by simpa only [hσ, map_one, mul_one] using he
      obtain ⟨hc, hr⟩ := graph_row hn hF g (hg ▸ hs)
      exact Or.inr (Or.inr (Or.inl ⟨g, hg, hg.symm ▸ hc, hg.symm ▸ hr⟩))
    · have hsq := graphField_part_sq g σ (he ▸ hs)
      obtain ⟨m, hm, hnm, _⟩ := fixedField_parameters hn hF σ hsq hσ
      refine Or.inr (Or.inr (Or.inr ⟨g, σ, hσ, he, hsq, ⟨m, by omega⟩, ?_⟩))
      by_cases hn2 : n = 2
      · exact Or.inl ⟨hn2, he.symm ▸ graphField_four_row hsmall
          (by simpa [hn2] using hF) g σ hσ (he ▸ hs)⟩
      · exact Or.inr (he.symm ▸ graphField_large_row hn hF hn2 g σ hσ (he ▸ hs))
end Matrix.PSL3Even.InvolutionResidualRows
