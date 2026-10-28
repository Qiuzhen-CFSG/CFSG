module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Absolute

/-!
# Irreducibility at the concrete binary model boundary

The natural, dual-natural and trace-zero adjoint actions span their full
endomorphism algebras. Applying density directly exposes their ordinary
irreducibility without repeatedly transporting through an algebraic closure.
These are the three nontrivial models of Aschbacher–Smith H.6.1, printed p.386.
-/

public section

open Representation
namespace BinaryLinearThree.IrreducibleCatalogue

theorem natural_irreducible : IsIrreducible W :=
  irreducible_of_jacobson_density_surjective W natural_density

theorem dual_irreducible : IsIrreducible W.dual :=
  irreducible_of_jacobson_density_surjective W.dual dual_density

theorem steinberg_irreducible : IsIrreducible S := by
  let : Nontrivial Steinberg := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank (ZMod 2) Steinberg by rw [finrank_steinberg]; decide)
  exact irreducible_of_jacobson_density_surjective S steinberg_density

end BinaryLinearThree.IrreducibleCatalogue
