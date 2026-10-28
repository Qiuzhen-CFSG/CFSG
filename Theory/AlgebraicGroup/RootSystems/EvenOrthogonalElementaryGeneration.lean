module

public import Theory.AlgebraicGroup.RootSystems.EvenOrthogonalElementaryGeneration.Symmetries
import Mathlib.Tactic

/-!
# Coordinate root generation of the rank-four orthogonal derived group

Over an algebraically closed field of characteristic two, the existing type-D₄
coordinate root matrices generate the commutator subgroup of the full isometry
group of the standard hyperbolic quadratic form. This is the concrete classical
realization of the root-generation statement in GLS3, Sections 1.10--1.12,
with Ω defined as in the paragraph following Theorem 1.10.7.

One inclusion follows from the explicit root commutators. For the other, the
proved split Cartan--Dieudonné and Clifford parity results factor every derived
element into an even word of anisotropic symmetries. Coordinate elimination
and normalization of quadratic norms show that every pair of those symmetries
lies in the coordinate-root closure. No abstract semisimple root-generation
or type-D identification theorem is used.
-/

universe u
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

private lemma even_symmetryProduct_mem_elementary
    (as : List (AnisotropicVector (hyperbolicForm (k := k) 4)))
    (has : Even as.length) :
    symmetryProductPoint as ∈ evenOrthogonalElementarySubgroup 4 := by
  induction as using List.twoStepInduction with
  | nil => simp
  | singleton a => simp at has
  | cons_cons a b as ih =>
      have has' : Even as.length := by
        obtain ⟨n, hn⟩ := has
        refine ⟨n - 1, ?_⟩
        simp only [List.length_cons] at hn
        omega
      rw [symmetryProductPoint_cons, symmetryProductPoint_cons, ← mul_assoc]
      exact mul_mem (EvenOrthogonalElementary.symmetryPair_mem a b) (ih has')

/-- The concrete coordinate type-D₄ root matrices generate Ω of the standard
hyperbolic quadratic space in characteristic two. -/
public theorem evenOrthogonalRoot_closure_eq_commutator :
    Subgroup.closure (Set.range fun p : StandardRootSystem.TypeDRootIndex 4 × k =>
      evenOrthogonalRootQuadraticPoint 4 p.1 p.2) =
      commutator (quadraticIsometrySubgroup (hyperbolicForm (k := k) 4)) := by
  apply le_antisymm (EvenOrthogonalElementary.le_commutator 4)
  intro g hg
  obtain ⟨as, has, hfac⟩ := exists_even_symmetryFactorization_of_mem_commutator
    (standardHyperbolicSplit 4) (by simp) hg
  rw [← hfac]
  exact even_symmetryProduct_mem_elementary as has

end Theory.AlgebraicGroup
