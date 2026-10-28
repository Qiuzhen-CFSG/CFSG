module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.Spanning
public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Action

/-!
# The actual local action on the odd short span

The existing Leech action of N1 is monomial, so it preserves the odd minimum
vectors. Equivariance of the fixed source lattice comparison and the exact
exhaustion of the odd short lifts prove stability, including both central
signs. Restriction of cShort gives the genuine local representation, with its
literal Griess inclusion and form invariance. An exact quotient conjugation
identity then gives the corresponding signed vector equation.

Source: Aschbacher, Sporadic Groups, 27.8(3), 29.6 and 29.8, printed pp. 150,
156--157. The monomial and conjugation comparison lemmas are reused from the
existing local octad action; the odd family is established here independently.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open Sporadic.Monster.Construction
open LocalC ShortFamilies TrialitySpin
open NOctad.LocalStructure
open scoped TensorProduct
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction

/-- Every literal N1 element preserves the odd family, including its central sign. -/
theorem cShortLift_n1_odd (g : N1) (x : Omega) (b : ParkerLoop) :
    ∃ y : Omega, ∃ c : ParkerLoop, rOdd y c = cShortLift (n1ToC g) (rOdd x b) := by
  apply (odd_iff _).mp
  refine ⟨shellPermutation (n1LeechRepresentation g) 4 (oddShell x b), ?_, ?_⟩
  · rw [shortReduction_transport, cShortLift_n1_class, rOdd_class]
  · obtain ⟨m, hm⟩ := n1Leech_monomial g
    change ((n1LeechRepresentation g).val (oddRepresentative x b)).val ∈ _
    rw [← hm]
    exact Atlas.Conway.monomial_odd_minimum_invariant m _ (oddRepresentative_mem x b)

/-- Stability under the existing C-action, through the actual map N1 → C. -/
theorem oddSpace_stable (g : N1) (v : BShort) (hv : v ∈ oddSpace) :
    cShort (n1ToC g) v ∈ oddSpace := by
  have h : oddSpace ≤ oddSpace.comap (cShort (n1ToC g)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x,b⟩, rfl⟩
    obtain ⟨y,c,hc⟩ := cShortLift_n1_odd g x b
    change cShort (n1ToC g) (shortVector sourceLatticeComparison (rOdd x b)) ∈ oddSpace
    rw [cShort_vector, ← hc]
    exact Submodule.subset_span ⟨(y,c), rfl⟩
  exact h hv

/-- The genuine restricted odd-family representation, before tensor transport. -/
def oddRepresentation : Representation ℝ N1 oddSpace where
  toFun g := (cShort (n1ToC g)).restrict (oddSpace_stable g)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change cShort (n1ToC 1) v.val = v.val
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change cShort (n1ToC (g * h)) v.val = cShort (n1ToC g) (cShort (n1ToC h) v.val)
    rw [map_mul, map_mul]
    rfl

@[simp] theorem oddRepresentation_val (g : N1) (v : oddSpace) :
    (oddRepresentation g v).val = cShort (n1ToC g) v.val := rfl

/-- An exact group conjugation identity gives its exact signed vector action. -/
theorem oddRepresentation_vector_of_conjugation (g : N1) (x y : Omega) (b c : ParkerLoop)
    (h : q1ImageConjugation g (rOddElement x b) = rOddElement y c) :
    oddRepresentation g (zeroOdd x b).1 = (zeroOdd y c).1 := by
  apply Subtype.ext
  change cShort (n1ToC g) (shortVector sourceLatticeComparison (rOdd x b)) =
    shortVector sourceLatticeComparison (rOdd y c)
  rw [cShort_vector]
  congr 1
  apply Subtype.ext
  exact (cShortLift_n1_val g (rOdd x b)).trans h

/-- The restriction intertwines the literal Griess-space inclusion. -/
theorem oddRepresentation_inclusion (g : N1) (v : oddSpace) :
    zeroInclusion (oddRepresentation g v, 0) =
      cRepresentation (n1ToC g) (zeroInclusion (v,0)) := by
  simp only [zeroInclusion_apply, map_zero, oddRepresentation_val, cRepresentation_apply]

/-- The genuine local action is an isometry on the odd summand. -/
theorem oddRepresentation_isometry (g : N1) (v w : oddSpace) :
    shortForm sourceLatticeComparison (oddRepresentation g v).val (oddRepresentation g w).val =
      shortForm sourceLatticeComparison v.val w.val := cShort_form (n1ToC g) v.val w.val

end Sporadic.Monster.Construction.NMonomial.ZeroAction
