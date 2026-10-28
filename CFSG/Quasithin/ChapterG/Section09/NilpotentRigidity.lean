module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.Residuals
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DimensionArithmetic
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DegreeTransfer
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DecompositionConsequences
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralDegree
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.OrthogonalPair

/-!
# Nilpotent-action rigidity: assembly

This module proves the representation-theoretic implication in
Aschbacher--Smith G.9.2, including rank zero. The dihedral degree theorem
first excludes a prime above five using the specified-prime extraction,
then gives the degree equality for an entirely cubic product or a product
containing a five-factor. The equality theorem constructs the actual
internal group and displacement-space decompositions, using the proved
identification of the natural orthogonal action.

`conclusion_of_extraction_and_splitting` discharges every degree and
module-classification premise of `conclusion_of_dihedral_inputs`. Only the
earlier G.8.6/G.8.8 group extraction and A.1.44 splitting remain explicit.
Neither input includes a degree bound or a module classification; the
Section09 source assembly must supply these earlier theorems. The rank-zero
case is proved directly with the empty decomposition.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
G.9.2, printed pp.351--353, PDF pp.362--364.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {A X : Subgroup G} {m : ℕ}

/-- The extra bound in G.9.2 makes its rank-zero case a zero module. -/
theorem Hypothesis.degree_zero (h : Hypothesis ρ A X 0) :
    Module.finrank (ZMod 2) V = 0 := by
  have hA : A = ⊥ := Subgroup.card_eq_one.mp (by simpa using h.card_actor)
  have hc : ⁅threeResidual X, A⁆ = ⊥ := by
    rw [hA, Subgroup.commutator_bot_right]
  simpa using h.degree_le_of_centralizes hc

/-- All six source clauses hold at rank zero, using an empty internal
product and an empty direct sum. No nontriviality is silently imposed. -/
theorem rank_zero (h : Hypothesis ρ A X 0) : Conclusion ρ A X 0 := by
  have hA : A = ⊥ := Subgroup.card_eq_one.mp (by simpa using h.card_actor)
  have hc : ⁅threeResidual X, A⁆ = ⊥ := by
    rw [hA, Subgroup.commutator_bot_right]
  let : Subsingleton V := Module.finrank_zero_iff.mp h.degree_zero
  let dec : InternalDecomposition ρ (⊥ : Subgroup G) 0 :=
    { factor := Fin.elim0
      groupEquiv := MulEquiv.ofUnique
      group_inclusion := fun i => Fin.elim0 i
      spaceEquiv := LinearEquiv.ofSubsingleton _ _
      space_inclusion := fun i => Fin.elim0 i }
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hA, Subgroup.commutator_bot_right]
  · refine ⟨⊥, hA.le, bot_le, ⟨⟨0, dec, ?_, ?_⟩⟩⟩
    · exact fun hn => (hn hc).elim
    · exact fun i => Fin.elim0 i
  · intro _
    simpa using h.degree_zero
  · exact fun hn => (hn hc).elim

/-- The selected-prime refinement and dihedral lower bounds exclude
nontrivial action on the `{3,5}`-residual. -/
theorem residual_centralizes_of_dihedral_bounds (h : Hypothesis ρ A X m)
    (extract : DihedralExtraction A X m) (bounds : HasDihedralLowerBounds ρ) :
    ⁅threeFiveResidual X, A⁆ = ⊥ := by
  by_contra hn
  obtain ⟨D, _, _, hi⟩ := extract.large_prime_system hn
  exact (Nat.not_lt_of_ge h.degree_le) ((bounds m D).2.2 hi)

/-- The degree equalities follow from the dihedral degree bounds before
any equality-case module recognition is used. -/
theorem degree_equalities_of_dihedral_bounds (h : Hypothesis ρ A X m)
    (extract : DihedralExtraction A X m) (bounds : HasDihedralLowerBounds ρ) :
    (⁅threeResidual X, A⁆ = ⊥ → Module.finrank (ZMod 2) V = 2 * m) ∧
    (⁅threeResidual X, A⁆ ≠ ⊥ → Module.finrank (ZMod 2) V = 2 * (m + 1)) := by
  constructor
  · intro hc
    obtain ⟨D, _, _⟩ := extract.exists_system
    exact Nat.le_antisymm (h.degree_le_of_centralizes hc) (bounds m D).1
  · intro hn
    have hc := residual_centralizes_of_dihedral_bounds h extract bounds
    obtain ⟨D, _, _, i, hi⟩ := extract.five_system hc hn
    exact Nat.le_antisymm h.degree_le ((bounds m D).2.1
      ⟨i, by omega⟩)

/-- Conditional assembly from degree bounds and equality classification.
`conclusion_of_extraction_and_splitting` below discharges these two
representation-theoretic premises. -/
theorem conclusion_of_dihedral_inputs (h : Hypothesis ρ A X m)
    (extract : DihedralExtraction A X m) (bounds : HasDihedralLowerBounds ρ)
    (classify : HasDihedralEqualityCases ρ) : Conclusion ρ A X m := by
  have hres := residual_centralizes_of_dihedral_bounds h extract bounds
  obtain ⟨hcentral, hnoncentral⟩ := degree_equalities_of_dihedral_bounds h extract bounds
  refine ⟨hres, ?_, hcentral, hnoncentral⟩
  by_cases hc : ⁅threeResidual X, A⁆ = ⊥
  · obtain ⟨D, hAD, hDXA, hp⟩ := extract.cubic_system hc
    refine ⟨D.embedding.range, hAD, hDXA, ?_⟩
    simpa only [hc, ne_eq, not_true_eq_false] using
      (classify m D).1 hp (h.degree_le_of_centralizes hc)
  · obtain ⟨D, hAD, hDXA, hp⟩ := extract.five_system hres hc
    refine ⟨D.embedding.range, hAD, hDXA, ?_⟩
    simpa only [ne_eq, hc, not_false_eq_true] using
      (classify m D).2 hp h.degree_le

/-- The representation-theoretic implication of G.9.2, with all six source
clauses and no lower-bound, equality-classification, or model-recognition
premise. The only explicit earlier-theorem inputs are the group extraction
from G.8.6/G.8.8 and the genuine dihedral splitting from A.1.44.

The Section09 assembly supplies those earlier inputs. Rank zero uses the
empty internal product and direct sum, without a positivity assumption. -/
theorem conclusion_of_extraction_and_splitting (h : Hypothesis ρ A X m)
    (extract : DihedralExtraction A X m) (split : DihedralSplittingTheorem.{v}) :
    Conclusion ρ A X m := by
  by_cases hm : m = 0
  · subst m
    exact rank_zero h
  · have bounds := dihedralDegree_of_splitting split
    exact conclusion_of_dihedral_inputs h extract
      (dihedralLowerBounds_of_uniform bounds ρ h.faithful)
      (dihedralEqualityCases_of_inputs split bounds orthogonalPairTheorem ρ h.faithful)

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity
