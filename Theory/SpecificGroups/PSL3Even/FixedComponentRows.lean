module
public import Theory.SpecificGroups.PSL3Even.InvolutionResidualRows.Cases
public import Theory.SpecificGroups.SU3.FixedFieldTwo

/-!
# Complete fixed-component rows for binary PSL₃ involutions

The proved automorphism factorization gives inner, field, graph and mixed
rows. Inner fixed groups are solvable. Quadratic descent gives the genuine
linear-three residual in the field row and the unitary residual in the
larger mixed row. For every twisted degree-two mixed action the whole fixed
group is PSU₃(2), of order 72, hence solvable. This last argument needs no
identification of the action with a prescribed GF(4) representative.

The original involution, field degree and coefficient action are retained.
Source: Aschbacher–Smith 16.1.4(1),(4)–(6), printed pp.1170–1171;
applications in 2.5.19, printed p.561, and E.6.23, printed p.254.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix BenderSuzuki.MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.LinearThree
open Matrix.PSL3Even.OuterElementaryRank.FixedRanks
namespace Matrix.PSL3Even.InvolutionResidualRows
variable {F : Type*} [Field F] [Finite F]

/-- Twisted degree-two mixed actions have solvable whole fixed groups. -/
theorem graphField_four_fixed_solvable (hF : Nat.card F = 4)
    (g : GL (Fin 3) F) (σ : F ≃+* F) (hne : σ ≠ 1)
    (hs : (linearConj F g * fieldAction F σ * graph F)^2=1) :
    Group.IsSolvable (linearConj F g * fieldAction F σ * graph F).fixedSubgroup := by
  obtain ⟨m,hm,hnm,hK⟩ := fixedField_parameters (f:=2) (by decide)
    (by simpa using hF) σ (graphField_part_sq g σ hs) hne
  have hm1 : m=1 := by omega
  obtain ⟨J,hJ,⟨e⟩⟩ := GraphFieldDescent.exists_fixed_equiv_unitary g σ hne hs
  have hc : Nat.card F=2^2 := by simpa using hF
  have hf : Nat.card {x:F // J.conj x=x}=2 := by
    rw [hJ]
    change Nat.card (FixedBy.subfield F σ) = 2
    simpa only [hm1,pow_one] using hK
  let : Group.IsSolvable (ProjectiveSpecialUnitaryMatrixGroup J) :=
    HermitianForm.FixedFieldTwo.projective_isSolvable J hc
      (BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J 2 hc hf)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- The actual inner involution centralizer is solvable. -/
theorem inner_fixed_solvable {n:ℕ} (hn:0<n) (hF:Nat.card F=2^n)
    (a:MulAut PSL(3,F)) (ha:orderOf a=2) (hi:∃t,a=MulAut.conj t) :
    Group.IsSolvable a.fixedSubgroup := by
  obtain ⟨c,_,hc,_⟩ := inner_row hn hF a ha hi
  let e : a.fixedSubgroup ≃* Matrix.PSL3.EvenInnerCentralizers.centralizer F :=
    ((MulAut.fixedSubgroupCongr c a).trans
      (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup hc))).trans
        (MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj _))
  let : Group.IsSolvable (Matrix.PSL3.EvenInnerCentralizers.centralizer F) :=
    ResidualComparison.root_centralizer_solvable F hn hF
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- Complete involution rows sufficient for fixed-component classification.
The small mixed row is retained as its proved solvable endpoint. -/
theorem fixed_component_rows {n:ℕ} (hn:0<n) (hF:Nat.card F=2^n)
    (a:MulAut PSL(3,F)) (ha:orderOf a=2) :
    Group.IsSolvable a.fixedSubgroup ∨ FieldCase n a ∨ GraphCase a ∨
      ∃ (m:ℕ) (J:HermitianForm 3 F), 1<m ∧ n=2*m ∧
        (∀x,J.conj x=x^(2^m)) ∧ Nat.card F=(2^m)^2 ∧
        Nat.card {x:F // J.conj x=x}=2^m ∧
        Nonempty (pResidual 2 a.fixedSubgroup ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hs:a^2=1 := ha ▸ pow_orderOf_eq_one a
  by_cases hi:∃t,a=MulAut.conj t
  · exact Or.inl (inner_fixed_solvable hn hF a ha hi)
  have hcover := standard_eq_top_of_two_power_card F hn hF
  obtain ⟨g,σ,he|he⟩ := Matrix.PSL3.CartanActions.NormalizerForm.standard_factorization
    F field_linearConj graph_linearConj_exists field_commute_graph a
      (hcover.symm ▸ mem_top a)
  · have hne:σ≠1 := by
      intro hσ
      have hlin:a=linearConj F g := by simpa only [hσ,map_one,mul_one] using he
      obtain ⟨t,ht⟩ := Matrix.PSL3.OddInvolutionFixed.linearConj_involution_inner g (hlin ▸ hs)
      exact hi ⟨t,hlin.trans ht.symm⟩
    obtain ⟨m,hm,hnm,hK,hσ,hc,hr⟩ := field_row hn hF g σ hne (he ▸ hs)
    exact Or.inr (Or.inl ⟨g,σ,hne,he,hσ,he.symm ▸ hc,m,hm,hnm,hK,he.symm ▸ hr⟩)
  · by_cases hσ:σ=1
    · have hg:a=linearConj F g*graph F := by simpa only [hσ,map_one,mul_one] using he
      obtain ⟨hc,hr⟩ := graph_row hn hF g (hg ▸ hs)
      exact Or.inr (Or.inr (Or.inl ⟨g,hg,hg.symm ▸ hc,hg.symm ▸ hr⟩))
    · by_cases hn2:n=2
      · exact Or.inl (he.symm ▸ graphField_four_fixed_solvable
          (by simpa [hn2] using hF) g σ hσ (he ▸ hs))
      · obtain ⟨m,J,hm,hnm,_,_,hpow,hcard,hfixed,hr⟩ :=
          graphField_large_row hn hF hn2 g σ hσ (he ▸ hs)
        exact Or.inr (Or.inr (Or.inr ⟨m,J,hm,hnm,hpow,hcard,hfixed,he.symm ▸ hr⟩))
end Matrix.PSL3Even.InvolutionResidualRows
