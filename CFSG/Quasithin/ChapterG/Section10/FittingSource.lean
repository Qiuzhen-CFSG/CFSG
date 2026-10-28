module
public import CFSG.Quasithin.ChapterG.Section10.TwoCore
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.SolvableSource
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.FiveCore.OrdinarySource
public import Theory.GroupTheory.Fitting.PrimeSubgroups
public import Theory.ElementaryAbelian.GeneratorRank
import Mathlib.Tactic

/-!
# The solvable irreducible branches of the G.10 action

The original G.10 hypothesis makes its elementary subgroup act faithfully on
its Fitting subgroup when the ambient group is solvable.  Applying the proved
G.9 source branches gives the two four-dimensional orthogonal alternatives,
the dihedral alternative, or the remaining rank-two degree-six case.

The final theorem is the literal consumer of the actor-rank lower bound in
14.3.14: that bound eliminates degree six and forces the orthogonal case.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- Solvable Fitting self-centralization supplies the faithful elementary
actor required by G.9.4, on exactly the original G.10 representation. -/
theorem fittingHypothesis_of_solvable {K : GroupClass.{u}}
    (cover : Nonempty (Section09.SQTKCover K G))
    (hs : Group.IsSolvable G) (hi : Representation.IsIrreducible ρ) :
    Section09.FittingHypothesis K ρ X (finrank (ZMod 2) (Additive X)) := by
  refine { faithful := h.faithful
           elementary := inferInstance
           card_actor := ?_
           degree_le := ?_
           quotient := cover
           irreducible := hi
           faithful_fitting := ?_ }
  · change Nat.card (Additive X) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  · have hr := (Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
      (QuotientGroup.mk'_surjective X₀)).trans (IsElementaryAbelian.rank_le_finrank (p := 2) X)
    exact h.dimension_bound.1.trans (by omega)
  · have hp : IsPGroup 2 (X ⊓ centralizer (fittingSubgroup G : Set G) : Subgroup G) :=
      (IsElementaryAbelian.isPGroup 2 X).to_le inf_le_left
    have he := hp.le_pCore_of_le_fitting
      (inf_le_right.trans (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs))
    exact bot_unique (he.trans_eq h.twoCore_eq_bot)

/-- The solved irreducible solvable source branches, leaving exactly the
rank-two degree-six case required by the remaining original14.3 argument. -/
theorem solvable_irreducible_cases {K : GroupClass.{u}}
    (cover : Nonempty (Section09.SQTKCover K G))
    (hs : Group.IsSolvable G) (hi : Representation.IsIrreducible ρ) (hX : X ≠ ⊥) :
    let m := finrank (ZMod 2) (Additive X)
    Section09.FittingRecognition.CaseOne ρ m ∨
      Section09.FittingRecognition.CaseTwo ρ X m ∨
      Section09.FittingRecognition.CaseThree ρ m ∨
      Section09.FittingRecognition.CaseFour ρ m ∨
      (m = 2 ∧ finrank (ZMod 2) V = 6) := by
  let : Nontrivial X := X.nontrivial_iff_ne_bot.mpr hX
  have hm : 0 < finrank (ZMod 2) (Additive X) := Module.finrank_pos
  have d := h.fittingHypothesis_of_solvable cover hs hi
  by_cases hc : IsPGroup 3 (⁅fittingSubgroup G, X⁆ : Subgroup G)
  · rcases Section09.FittingRecognition.source_cubic_degree_cases d hm hc with
      hone | ⟨_,hd⟩ | ⟨_,hd⟩ | h6
    · exact Or.inl hone
    · have h4 := Section09.FittingRecognition.source_solvable_cubic_degree_four d hm hc hd hs
      exact h4.elim (fun hh => Or.inr (Or.inr (Or.inl hh.2)))
        (fun hh => Or.inr (Or.inr (Or.inr (Or.inl hh.2))))
    · have h4 := Section09.FittingRecognition.source_solvable_cubic_degree_four d hm hc hd hs
      exact h4.elim (fun hh => Or.inr (Or.inr (Or.inl hh.2)))
        (fun hh => Or.inr (Or.inr (Or.inr (Or.inl hh.2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h6)))
  · exact Or.inr (Or.inl (Section09.FittingRecognition.caseTwo_from_source d hm hc))

/-- The source lower bound on the elementary actor excludes the remaining
six-dimensional case and gives the literal orthogonal index-two conclusion. -/
theorem orthogonal_case_of_rank_bound {K : GroupClass.{u}}
    (cover : Nonempty (Section09.SQTKCover K G))
    (hs : Group.IsSolvable G) (hi : Representation.IsIrreducible ρ) (hX : X ≠ ⊥)
    (hr : 2 ≤ finrank (ZMod 2) (Additive X))
    (hd : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (Additive X)) :
    Section09.FittingRecognition.CaseFour ρ (finrank (ZMod 2) (Additive X)) := by
  rcases h.solvable_irreducible_cases cover hs hi hX with h1 | h2 | h3 | h4 | h6
  · have := h1.1; omega
  · have := h2.1; omega
  · have := h3.1; omega
  · exact h4
  · omega

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
