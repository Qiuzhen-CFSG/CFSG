module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalBounds

/-!
# Marked orthogonal section specifications

These predicates specify actual equivariant modules and literal commutator
subspaces in the orthogonal branch of 13.8.25. Coordinate changes use inner
automorphisms of the same symmetric group. The seven-dimensional alternative
is the augmentation core, as in `IsEightNaturalOrCover`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed p.960, PDF p.977. These are specifications
of intermediate outputs, not assumptions proving section recognition.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels
open Representation.BinaryOffender BinaryPermutation
abbrev Perm := Equiv.Perm (Fin 8)
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- A concrete natural module, equivariant for the specified permutation marking. -/
def IsEightNatural (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) : Prop :=
  ∃ e : U ≃ₗ[ZMod 2] natural (Fin 8),
    ∀ g u, e (ρ g u) = naturalRepresentation (Fin 8) (eH g) (e u)

/-- Change all permutation coordinates by the same inner automorphism. -/
def conjugateMarking (eH : H ≃* Perm) (g : Perm) : H ≃* Perm :=
  eH.trans (MulAut.conj g)

/-- The actual commutator submodule is natural or its augmentation cover.
The equality retains the submodule and its inclusion in the original module. -/
def IsCommutatorNaturalOrCover (ρ : Representation (ZMod 2) H U)
    (K : Subgroup H) (eH : H ≃* Perm) : Prop :=
  ∃ J : Subrepresentation ρ,
    J.toSubmodule = subspaceCommutator ρ ⊤ K ∧ IsEightNaturalOrCover J.toRepresentation eH

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels
