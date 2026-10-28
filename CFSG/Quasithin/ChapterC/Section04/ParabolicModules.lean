module

public import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# The parabolic module step in C.4.8

Aschbacher--Smith, *The Classification of Quasithin Groups*, Section C.4,
Theorem C.4.8, final paragraph (printed p. 154). The matrix calculations for
the natural, dual, and exterior-square representations identify the fixed-space
commutator module. The lemma below then passes the resulting homogeneous
semisimple structure to each invariant submodule, as needed for the module `V`
in the theorem. The explicit parabolic calculations are separate prerequisites.
-/

namespace CFSG.Quasithin.ChapterC.Section04

universe u v w

/-- Every invariant submodule of a semisimple homogeneous module is a direct
sum of copies of the same simple module. This is the final submodule step in
the parabolic calculation of C.4.8. -/
public theorem parabolic_isotypic_submodule_decomposition
    {A : Type v} {W : Type u} {N : Type w} [Ring A]
    [AddCommGroup W] [Module A W]
    [AddCommGroup N] [Module A N]
    [IsSemisimpleModule A W]
    (hW : IsIsotypicOfType A W N) (V : Submodule A W) :
    ∃ ι : Type u, Nonempty (V ≃ₗ[A] ι →₀ N) := by
  have hV : IsIsotypicOfType A V N :=
    hW.of_injective V.subtype V.subtype_injective
  exact hV.linearEquiv_finsupp

end CFSG.Quasithin.ChapterC.Section04
