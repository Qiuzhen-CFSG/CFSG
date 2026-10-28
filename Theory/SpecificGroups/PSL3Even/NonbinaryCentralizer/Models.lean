module

public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraph.Orthogonal
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraph.Quotient
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import GorensteinWalter.PSL2PerfectOfCard
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Graph and field types for nonbinary PSL₃ centralizers

The type predicate records actual conjugacy of matrix automorphisms, and is
invariant under further conjugation. It does not assert that an arbitrary
outer involution has either type: graph-field involutions are separate.
The graph fixed subgroup is identified with the actual SL₂(F), using fixed
projective representatives and the characteristic-two orthogonal calculation.
For |F| ≥ 4 this proves simplicity and perfectness, also after conjugacy.

These are model inputs for Aschbacher–Smith E.1.14(1), printed p.214.
The action conventions are those of GLS3, Theorem 2.5.12 and §2.7.
Selecting this type inside an exact-rank elementary actor is still required.
-/

public section
open Matrix.PSL3.OuterSolvable
open scoped MatrixGroups
namespace Matrix.PSL3Even.NonbinaryCentralizer
variable {F : Type*} [Field F]

/-- Actual conjugacy to a graph or nontrivial involutory coefficient action. -/
@[expose] def IsGraphOrField (a : MulAut PSL(3,F)) : Prop :=
  IsConj a (graph F) ∨ ∃ σ : F ≃+* F, σ ≠ 1 ∧ σ ^ 2 = 1 ∧
    IsConj a (fieldAction F σ)

/-- Ambient conjugation preserves the selected automorphism type. -/
theorem IsGraphOrField.conj {a : MulAut PSL(3,F)} (ha : IsGraphOrField a)
    (b : MulAut PSL(3,F)) : IsGraphOrField (b * a * b⁻¹) := by
  have hc : IsConj (b * a * b⁻¹) a := (isConj_iff.mpr ⟨b, rfl⟩).symm
  rcases ha with h | ⟨σ, hn, hs, h⟩
  · exact Or.inl (hc.trans h)
  · exact Or.inr ⟨σ, hn, hs, hc.trans h⟩

/-- The literal inverse-transpose fixed group in characteristic two is SL₂. -/
noncomputable def graphFixedEquivSL2 [CharP F 2] :
    (graph F).fixedSubgroup ≃* SL(2,F) :=
  (Matrix.PSL3Four.GraphFixed.projectiveGraphFixedEquivSpecial F).trans
    (Matrix.PSL3Four.GraphFixed.graphSLFixedEquivSL2 F)

variable [Finite F] [CharP F 2]

/-- Above the binary field the graph fixed group is nonabelian simple. -/
theorem graph_fixed_simple_perfect (hF : 4 ≤ Nat.card F) :
    IsSimpleGroup (graph F).fixedSubgroup ∧ Group.IsPerfect (graph F).fixedSubgroup := by
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F) hF
  let : IsSimpleGroup SL(2,F) := (Theory.PSL2.sl2QuotientEquiv F).isSimpleGroup
  let := GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
  let : Group.IsPerfect SL(2,F) := Group.IsPerfect.ofSurjective
    (f := (Theory.PSL2.sl2QuotientEquiv F).symm.toMonoidHom)
    (Theory.PSL2.sl2QuotientEquiv F).symm.surjective
  exact ⟨(graphFixedEquivSL2 (F := F)).isSimpleGroup,
    Group.IsPerfect.ofSurjective (f := (graphFixedEquivSL2 (F := F)).symm.toMonoidHom)
      (graphFixedEquivSL2 (F := F)).symm.surjective⟩

/-- Graph conjugacy gives the same actual simple and perfect fixed group. -/
theorem graph_fixed_simple_perfect_of_isConj (hF : 4 ≤ Nat.card F)
    (a : MulAut PSL(3,F)) (ha : IsConj a (graph F)) :
    IsSimpleGroup a.fixedSubgroup ∧ Group.IsPerfect a.fixedSubgroup := by
  obtain ⟨c, hc⟩ := isConj_iff.mp ha
  have he : MulAut.congr c a = graph F := hc
  let e := (MulAut.fixedSubgroupCongr c a).trans
    (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup he))
  obtain ⟨hs, hp⟩ := graph_fixed_simple_perfect hF
  let := hs
  let := hp
  exact ⟨e.isSimpleGroup,
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

end Matrix.PSL3Even.NonbinaryCentralizer
