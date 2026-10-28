module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.OddLie.Reduction
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Inner
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Graph
public import Theory.SpecificGroups.ClassicalOrthogonal.TernaryThreeRank

/-!
# The odd-prime linear-three fixed-group calculation

Every involution of PSL₃ over an odd prime field is inner or is a linear
conjugation followed by inverse transpose. In the inner case its fixed group
is an image of GL₂, whose derived subgroup has three-rank at most one. In the
graph case the full fixed group embeds in a ternary special orthogonal group,
whose three-rank is at most one when the field characteristic is not three.
Both calculations account for the scalar kernel of the projective quotient.

The final theorem transports the resulting derived-fixed-group bound through
the actual field and group equivalence stored in `ClassicalGroup.IsPSL`.
The earlier conditional interfaces are retained; their graph premise is now
discharged. Strong quasithinness is not needed for this model calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the inspection
in E.6.18, printed p.252 (PDF p.263), and Theorem C, printed p.33.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix.PSL3.OuterSolvable Matrix.PSL3.OddInvolutionFixed
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie

/-- The inner branch is discharged; only the actual graph fixed group remains. -/
theorem involutionDerivedThreeRank_linear_three_model_of_graph
    {F : Type*} [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]
    (hns : ¬ Group.IsSolvable PSL(3,F)) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) (hF : Nat.card F = p)
    (hgraph : ∀ g : Matrix.GeneralLinearGroup (Fin 3) F,
      orderOf (linearConj F g * graph F) = 2 →
        primeRank 3 (linearConj F g * graph F).fixedSubgroup ≤ 1) :
    InvolutionDerivedThreeRank PSL(3,F) := by
  intro a ha
  obtain ⟨g, h | h⟩ := automorphism_normal_form hns hp ho hF a
  · subst a
    exact inner_fixed_derived_three_rank hns hp ho hp3 hF _ ha
      (linearConj_involution_inner g (ha ▸ pow_orderOf_eq_one _))
  · subst a
    exact (primeRank_subgroup_le 3 _).trans (hgraph g ha)

/-- Conditional assembly preserving the genuine projective-model equivalence. -/
theorem involutionDerivedThreeRank_linear_three_of_graph
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ¬ IsMulCommutative S) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) (hS : ClassicalGroup.IsPSL S 3 p)
    (hgraph : ∀ (F : Type) [Field F] [Finite F], Nat.card F = p →
      ∀ g : Matrix.GeneralLinearGroup (Fin 3) F,
        orderOf (linearConj F g * graph F) = 2 →
          primeRank 3 (linearConj F g * graph F).fixedSubgroup ≤ 1) :
    InvolutionDerivedThreeRank S := by
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hS
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  have hns : ¬ Group.IsSolvable PSL(3,F) := by
    intro hs
    let : Group.IsSolvable PSL(3,F) := hs
    let : Group.IsSolvable S :=
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact hnc ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance⟩⟩
  exact InvolutionDerivedThreeRank.of_equiv
    (involutionDerivedThreeRank_linear_three_model_of_graph hns hp ho hp3 hF (hgraph F hF)) e

private theorem graph_fixed_three_rank
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) (hF : Nat.card F = p)
    (g : Matrix.GeneralLinearGroup (Fin 3) F)
    (hg : orderOf (linearConj F g * graph F) = 2) :
    primeRank 3 (linearConj F g * graph F).fixedSubgroup ≤ 1 := by
  obtain ⟨J, hJ, f, hf⟩ := exists_graphFixed_orthogonal_embedding g hg
  exact (Theory.GroupTheory.primeRank_le_of_injective 3 f hf).trans
    (J.primeRank_three_specialSubgroup_le_one hp ho hp3 hF hJ)

/-- Every involution of the actual odd-prime PSL₃ model has derived fixed
group of three-rank at most one, in characteristic different from three. -/
theorem involutionDerivedThreeRank_linear_three_model
    {F : Type*} [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]
    (hns : ¬ Group.IsSolvable PSL(3,F)) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) (hF : Nat.card F = p) :
    InvolutionDerivedThreeRank PSL(3,F) :=
  involutionDerivedThreeRank_linear_three_model_of_graph hns hp ho hp3 hF
    (graph_fixed_three_rank hp ho hp3 hF)

/-- The odd-prime linear-three fixed-group calculation, transported through
the genuine projective-model equivalence and with both involution branches proved. -/
theorem involutionDerivedThreeRank_linear_three
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ¬ IsMulCommutative S) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) (hS : ClassicalGroup.IsPSL S 3 p) :
    InvolutionDerivedThreeRank S :=
  involutionDerivedThreeRank_linear_three_of_graph hnc hp ho hp3 hS
    (fun _ _ _ hF => graph_fixed_three_rank hp ho hp3 hF)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie
