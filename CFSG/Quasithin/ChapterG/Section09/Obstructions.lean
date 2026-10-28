module

public import CFSG.Quasithin.ChapterG.Section09.Setup
public import Theory.Representation.SubrepresentationLattice

/-!
# The rank-zero boundary in G.9.4

The one-dimensional trivial binary representation of the trivial group is
faithful and irreducible. With the trivial actor it satisfies G.9.1 and
every additional hypothesis printed in G.9.4, for every class of groups
`K`. Its actor has rank zero, whereas all five printed conclusions have
rank one or two. Thus those hypotheses, without a positive-rank convention,
do not imply the displayed classification.

This records the exact obstruction without altering the source-hypothesis
interface. The nontrivial-actor version remains the intended input to
the G.11 applications; G.9.3 already forces a nontrivial actor.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
G.9.1 and G.9.4, printed pp.351 and 354.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.Obstructions

/-- The faithful one-dimensional representation of the trivial group. -/
def trivialAction : Representation (ZMod 2) Unit (ZMod 2) := 1

private theorem trivial_sqtk (K : GroupClass.{0}) : IsSQTK K Unit := by
  constructor
  · intro p _ _
    exact (Theory.GroupTheory.primeRank_le_card (G := Unit) p).trans (by simp)
  · intro S _ hS U f hf
    let : IsSimpleGroup S := hS
    let : Subsingleton S := hf.subsingleton
    exact (not_subsingleton S inferInstance).elim

/-- Every literal hypothesis of G.9.4 holds in this rank-zero example. -/
theorem rank_zero_fitting_hypothesis (K : GroupClass.{0}) :
    FittingHypothesis K trivialAction (⊥ : Subgroup Unit) 0 := by
  refine {
    faithful := fun _ _ _ => Subsingleton.elim _ _
    elementary := { exponent_dvd_p := by simp }
    card_actor := by simp
    degree_le := by simp
    quotient := ⟨{
      Cover := Unit
      sqtk := trivial_sqtk K
      projection := MonoidHom.id Unit
      surjective := Function.surjective_id }⟩
    irreducible := ?_
    faithful_fitting := by simp }
  refine { eq_bot_or_eq_top := fun W => ?_ }
  rcases eq_bot_or_eq_top W.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

/-- Even the rank disjunction common to all five G.9.4 conclusions fails
if no nontriviality hypothesis is imposed on the actor. -/
theorem not_unrestricted_fitting_rank_classification (K : GroupClass.{0}) :
    ¬ (∀ (G V : Type) [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
      [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
      (A : Subgroup G) (m : ℕ), FittingHypothesis K ρ A m → m = 1 ∨ m = 2) := by
  intro h
  have hzero := h Unit (ZMod 2) trivialAction ⊥ 0 (rank_zero_fitting_hypothesis K)
  simp at hzero

end CFSG.Quasithin.ChapterG.Section09.Obstructions
