module

public import Theory.SpecificGroups.Lyons.GebhardtLocalParabolicCertificateSetup

/-!
# Assembly of the local parabolic relative-index bound

A certified 3906-state cover proves both positivity and the upper bound for
the index of `⟨a,b,c⟩` in `⟨a,b,c,d⟩`. Positivity comes from the finite coset
quotient, independently of any bound on the order of the parabolic.

The enumeration certificate remains an explicit input to this assembly.

Source: Gebhardt, Experimental Mathematics 9 (2000), 333–338, Section 3B.
-/

namespace Lyons.Gebhardt

/-- The finite-cover contract suffices for both local relative-index bounds. -/
public theorem localTowerLocal_relIndex_bounds_of_cover
    (C : LocalParabolicCertificate.Cover) :
    0 < LocalTower.parabolic.relIndex localSubgroup ∧
      LocalTower.parabolic.relIndex localSubgroup ≤ 3906 := by
  refine ⟨C.index_pos LocalParabolicCertificate.closure_range_generator, ?_⟩
  change LocalParabolicCertificate.parabolic.index ≤ 3906
  simpa using C.index_le_card LocalParabolicCertificate.closure_range_generator

end Lyons.Gebhardt
