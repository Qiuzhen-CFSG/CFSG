module

public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.ChiefSurvival
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.TwoPerfectRefinement

/-!
# Noncentral binary chief counts in the two-residual

Intersect a complete chief series of a finite group K with O²(K), and refine
the resulting normal filtration. Each original noncentral binary chief
section survives the restricted action because K/O²(K) is a two-group.
Two-perfectness of O²(K) then forces a noncentral binary chief factor in
each such restricted interval. Counting these disjoint intervals proves
that the number of noncentral binary chief factors cannot decrease.

The refinement retains every literal intersected term, including repeated
ones. Both local action premises of the earlier conditional assembly are
discharged here. No assumption on K/O₂(K) is needed; in particular this
applies to the S₃ quotient in Aschbacher–Smith 14.7.70, printed p.1074
(PDF p.1091).
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {K : Type*} [Group K] [Finite K]

/-- A complete chief series has a complete refinement in the actual
two-residual retaining all intersections and at least its noncentral binary
count. Neither action survival nor refinement survival is an extra premise. -/
theorem ChiefSeries.exists_complete_pResidual_refinement
    (s : ChiefSeries K) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    ∃ (t : ChiefSeries (pResidual 2 K))
      (ι : Fin (s.length + 1) →o Fin (t.length + 1)),
      (∀ i, t (ι i) = restrictNormalNode (pResidual 2 K) (s i)) ∧
      ι 0 = 0 ∧ ι (Fin.last s.length) = Fin.last t.length ∧
      t.head = ⊥ ∧ t.last = ⊤ ∧ s.noncentralTwoCount ≤ t.noncentralTwoCount :=
  s.exists_comparison_of_pResidual h0 h1
    (fun t => t.exists_noncentralTwo_pResidual)

end NoncentralChiefRefinement
