module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.Reduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Intertwiners

/-!
# Constructing ambient implementers for automorphisms fixing `a`

The remaining representation calculation separates into irreducibility of the
literal binary module and nonvanishing of its intertwiner spaces with twists
fixing `a`. The kernel argument in `Intertwiners` turns their nonzero elements
into invertible matrices and gives the exact ambient conjugation equations.

Both inputs remain explicit below. The unconditional `ambientImplementation`
still requires proofs of these model facts; in particular, no invariance of
the 112-dimensional representation follows from the generator orders alone.
Source motivation: GLS3, Table 5.3i; Aschbacher–Smith, printed pp.33 and 510.
The table's small-representation clause asserts existence and absolute
irreducibility, not uniqueness or invariance under automorphism twists.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator

/-- The final linear-algebra assembly, conditional on the two independent
representation facts. Neither input contains an invertible conjugator. -/
theorem ambientImplementation_of_generatorIrreducible
    (hirr : GeneratorIrreducible)
    (htwist : ∀ α : MulAut Model, α a = a → generatorIntertwiners α ≠ ⊥) :
    AmbientImplementation := by
  intro α ha
  obtain ⟨U, hU, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (htwist α ha)
  exact ambient_unit_of_nonzero_generatorIntertwiner hirr α ha hU hne

end Janko4.OuterReduction.FixedGenerator
