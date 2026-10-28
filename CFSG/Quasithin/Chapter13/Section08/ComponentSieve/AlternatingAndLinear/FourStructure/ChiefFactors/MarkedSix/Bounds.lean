module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.Models

/-!
# The intrinsic calculation needed on the exterior square

The marked radical fixes a plane pointwise and acts trivially modulo that
plane in the natural four-space. Its exterior-square action is different:
quadratic subgroups have rank at most two, and nontrivial elementary
subgroups of rank at most two have fixed codimension greater than their rank.

`ExteriorRadicalBounds` specifies these two universal calculations on the
actual exterior power. `MarkedSix.Calculations` proves both calculations;
this interface keeps their transport independent of the coordinate proof.
The transport module uses it to handle every source conjugator and every
literal section.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.25,
printed p.961 (PDF p.978), using B.3.2(6), printed p.84. A direct proof of
these calculations avoids needing a comparison with the deleted permutation
module; any proof using that module must supply the equivariant comparison.
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix
open Alignment

/-- The actual GL₄(2) action on its exterior square. -/
noncomputable abbrev modelAction :=
  exteriorSquareAction (MulEquiv.refl (BinaryLinear.GL NaturalSpace))

/-- Two intrinsic, universal model obligations. Neither source actor, a chief
factor identification, nor the conclusion `SixActorFacts` occurs here. -/
structure ExteriorRadicalBounds : Prop where
  quadratic_rank : ∀ (P : Submodule (ZMod 2) NaturalSpace),
    Module.finrank (ZMod 2) P = 2 →
    ∀ A : Subgroup (BinaryLinear.GL NaturalSpace), A ≤ BinaryLinear.radical P →
      IsQuadratic modelAction A → rank A ≤ 2
  small_fixedCodim : ∀ (P : Submodule (ZMod 2) NaturalSpace),
    Module.finrank (ZMod 2) P = 2 →
    ∀ A : Subgroup (BinaryLinear.GL NaturalSpace), A ≤ BinaryLinear.radical P →
      IsElementaryTwo A → rank A ≤ 2 → rank A < fixedCodim modelAction A

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix
