module

public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions

/-!
# Reduction of PSL₃ outer solvability to its standard automorphisms

The lower module constructs the actual linear, field and graph actions and
proves that the diagonal image modulo inner automorphisms is abelian.
The assembly here still requires two independent results: coverage of all
automorphisms by the standard subgroup, and solvability of its outer image.
These hypotheses are explicit; this module does not yet prove the source
automorphism theorem.

Source: GLS3, Theorem 2.5.12 and §2.7, `refs/KGroup/GLS3/chapter2.tex`.
The consequence is used for the extension-control step of Theorem 6.5.3.
-/

namespace Matrix.PSL3.OuterSolvable

open scoped MatrixGroups

variable (F : Type*) [Field F]

/-- Full standard-automorphism coverage also covers the actual outer quotient. -/
public theorem standardOuter_eq_top_of_standard_eq_top (h : standard F = ⊤) :
    standardOuter F = ⊤ := by
  change (standard F).map (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) = ⊤
  rw [h, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)

/-- Conditional assembly: both the coverage and the standard-image calculation
must be supplied before this yields unconditional outer solvability. -/
public theorem outer_isSolvable_of_standard_inputs (hcover : standard F = ⊤)
    (hsolv : Group.IsSolvable (standardOuter F)) :
    Group.IsSolvable (MulAut.Outer PSL(3,F)) := by
  let := hsolv
  apply Group.isSolvable_of_surjective (f := (standardOuter F).subtype)
  intro x
  exact ⟨⟨x, by rw [standardOuter_eq_top_of_standard_eq_top F hcover]; trivial⟩, rfl⟩

end Matrix.PSL3.OuterSolvable
