module
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.CommutatorImage.Perfectness
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.CommutatorImage.Normality
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The exact commutator image in the minus-six exterior comparison

The unitary exterior image is nontrivial: its faithful action retains the
coordinate pair swap. Perfectness and containment in the literal orthogonal
commutator are proved in `CommutatorImage.Perfectness`. The concrete Siegel lifts
and singular-line transitivity in `CommutatorImage.Normality` establish relative
normality. Inherited simplicity of the commutator then gives exhaustion.

The final equality retains only descent and inherited simplicity as inputs,
with no additional perfectness, normality, order, generation or recognition
premise. It supplies exactly the image input to `specialEquivOmega_of_range`
in the parent comparison assembly, which owns the exceptional isomorphism.
Source conventions: GLS3 §2.7, printed pp.85–89; Aschbacher–Smith A.2.18
and Theorem D.
-/

public noncomputable section
namespace ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourGeneration

variable (n : ℕ) [NeZero n] (hD : Descends n)

/-- The descended image contains a nonidentity coordinate permutation. -/
theorem orthogonalAction_range_ne_bot : (orthogonalAction n hD).range ≠ ⊥ := by
  let s := pairSwap (Field n) (conjugation n)
    (Representation.OrthogonalFourMinus.FiniteModel.conjugation_involutive n)
  have hs : s ≠ 1 := by
    intro hs
    apply pairSwap_not_mem_point (Field n) (conjugation n)
      (Representation.OrthogonalFourMinus.FiniteModel.conjugation_involutive n)
    change s ∈ _
    rw [hs]
    exact Subgroup.one_mem _
  intro hbot
  have he : orthogonalAction n hD s = 1 := by
    have hm : orthogonalAction n hD s ∈ (orthogonalAction n hD).range := ⟨s, rfl⟩
    simpa only [hbot, Subgroup.mem_bot] using hm
  exact hs (orthogonalAction_injective n hD (he.trans (map_one _).symm))

/-- With inherited simplicity, relative normality is the sole remaining input
for exhaustion of the literal full-group commutator. Perfectness, containment
and nontriviality are all proved for the concrete action. -/
theorem orthogonalAction_range_eq_commutator_of_normal (hn : 1 < n)
    [IsSimpleGroup (Omega n)]
    (hN : ((orthogonalAction n hD).range.subgroupOf
      (commutator (FullOrthogonal n))).Normal) :
    (orthogonalAction n hD).range = commutator (FullOrthogonal n) := by
  have hsimple : IsSimpleGroup ↥(commutator (FullOrthogonal n)) := inferInstance
  exact ((Subgroup.isSimpleGroup_iff.mp hsimple).2 _
    (orthogonalAction_range_le_commutator n hn hD) hN).resolve_left
      (orthogonalAction_range_ne_bot n hD)

/-- The genuine descended SU₄ exterior image is exactly the literal commutator
of the full orthogonal group. The normality input is discharged by the concrete
Siegel lifts; only descent and inherited simplicity remain as source inputs. -/
theorem orthogonalAction_range_eq_commutator (hn : 1 < n)
    [IsSimpleGroup (Omega n)] :
    (orthogonalAction n hD).range = commutator (FullOrthogonal n) :=
  orthogonalAction_range_eq_commutator_of_normal n hD hn
    (orthogonalAction_range_subgroupOf_commutator_normal n hn hD)

end ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
