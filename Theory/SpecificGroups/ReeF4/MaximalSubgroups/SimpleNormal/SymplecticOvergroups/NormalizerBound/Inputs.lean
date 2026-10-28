module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SymplecticOvergroups.Inputs
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SymplecticOvergroups.NormalizerBound.BinaryAlternating

/-!
# The embedded binary centralizer needed for the Ree normalizer bound

The subgroup below is the image of the actual A₆ polar representation,
extended from F₂ to F and transported through the supplied symplectic
equivalence. The required centralizer is relative to M. The source's stronger
trivial ambient centralizer would suffice, but is not required by this contract.

Malle, Section 2.2, excludes field automorphisms using this A₆. Section 2.7,
Proposition 2.10, discusses the conjugacy and trivial centralizer of arbitrary
A₆ subgroups in the Ree group; its local analysis is a remaining geometric
obligation. Reference: J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E.

This is not the already supplied trivial centralizer of S. Since A₆ is smaller
than S, its centralizer can be larger. No centralizer assertion is proved by
the definition, and no normalizer index or placement conclusion is assumed.
-/

@[expose] public section

namespace ReeF4.MaximalSubgroups.SimpleNormal

open Subgroup Matrix NormalizerBound

/-- The precise remaining Ree centralizer calculation for the upper bound.
Characteristic two is derived from the field cardinality by the caller. -/
def SymplecticBinaryCentralizers : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
        Nat.card F = 2 ^ (2 * m + 1) →
        ∀ e : S ≃* symplecticGroup (Fin 2) F,
          centralizer ((binaryAlternatingInSubgroup S e).range : Set M) = ⊥

end ReeF4.MaximalSubgroups.SimpleNormal
