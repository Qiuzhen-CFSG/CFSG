module

public import Theory.SpecificGroups.Lyons.GebhardtCosetGeometry

/-!
# Assembly of a coset cover for the Gebhardt presentation

A five-double-coset coverage proof and a finite transversal for their local
suffixes give a cover with 8,835,156 representatives. The transition witnesses
are products of the two subgroup witnesses, so both signed transitions are
equalities in the abstract presented group. This is the double-coset route of
Gebhardt, Experimental Mathematics 9 (2000), 333–338, Sections 2 and 3B.

The construction below is conditional on the two independent certificates;
neither the group order nor a permutation representation supplies them.
-/

namespace Lyons.Gebhardt

/-- Combine the two factorizations, retaining the actual local-subgroup witness. -/
public theorem covers_of_doubleCosets (outer : OuterDoubleCosetTransitions)
    (T : DoubleCosetTransversal) (x : Presentation) :
    ∃ (h : localSubgroup) (j : Fin 8835156), x = h.val * T.repr j := by
  obtain ⟨k, i, h, hx⟩ := doubleCosets_cover outer x
  obtain ⟨l, j, hj⟩ := T.cover i h
  refine ⟨k * l, j, ?_⟩
  rw [hx, hj, Subgroup.coe_mul, mul_assoc]

/-- The two certificates supply every positive and inverse generator transition. -/
public def gebhardtCosetCoverOfDoubleCosets (outer : OuterDoubleCosetTransitions)
    (T : DoubleCosetTransversal) :
    Subgroup.GeneratorCosetCover localSubgroup generator (Fin 8835156) where
  repr := T.repr
  initial := T.initial
  initial_eq := T.initial_eq
  step i a := covers_of_doubleCosets outer T (T.repr i * generator a)
  inv_step i a := covers_of_doubleCosets outer T (T.repr i * (generator a)⁻¹)

end Lyons.Gebhardt
