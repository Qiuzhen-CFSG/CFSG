module

public import Theory.Representation.Mathieu.M24Degree44Displacement.Inputs
public import Theory.Representation.MathieuCodeRestriction
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Golay exterior squares and their actual sections

The exterior-square action is induced by the literal action on the code or
cocode. A section is an equivariant surjective image of an invariant subspace;
it includes nonsplit composition factors and retains the native M₂₄ marking.

Two independent inputs remain: every binary irreducible module of degree 44
occurs as such a section, and order-five elements have at most eleven fixed
dimensions on the two exterior squares. These are contracts, not assertions
of a representation catalogue. The latter bound descends to eight on a
degree-44 section because its fixed dimension is divisible by four.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, manuscript p.17; James, The modular characters of the Mathieu
groups, J. Algebra 27 (1973), 57--111.
-/

@[expose] public section
namespace Representation.MathieuM24Degree44.FiveSpace
open Sporadic.Mathieu BinaryOffender
universe v

/-- The functorial exterior-square action, with the original group marking. -/
noncomputable def exteriorSquare {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) :
    Representation F G (⋀[F]^2 V) where
  toFun g := exteriorPower.map 2 (ρ g)
  map_one' := by
    rw [map_one]
    exact exteriorPower.map_id
  map_mul' g h := by
    rw [map_mul]
    exact exteriorPower.map_comp (ρ h) (ρ g)

/-- A literal invariant section, presented without a splitting assumption. -/
def IsSectionOf {F G V W : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (ρ : Representation F G V) (σ : Representation F G W) : Prop :=
  ∃ S : Subrepresentation σ, ∃ f : S.toRepresentation.IntertwiningMap ρ,
    Function.Surjective f

/-- Exterior square of the native eleven-dimensional code modulo constants. -/
noncomputable def codeExterior := exteriorSquare MathieuCode.codeRepresentation

/-- Exterior square of the native eleven-dimensional even cocode. -/
noncomputable def cocodeExterior := exteriorSquare MathieuCode.cocodeRepresentation

theorem finrank_codeExterior : Module.finrank (ZMod 2) (⋀[ZMod 2]^2 MathieuCode.Code) = 55 := by
  rw [exteriorPower.finrank_eq, MathieuCode.finrank_code]
  decide

theorem finrank_cocodeExterior :
    Module.finrank (ZMod 2) (⋀[ZMod 2]^2 MathieuCode.Cocode) = 55 := by
  rw [exteriorPower.finrank_eq, MathieuCode.finrank_cocode]
  decide

/-- Universal section placement; arbitrary binary irreducibles are retained. -/
def GolayExteriorPlacement : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M24 V),
    Function.Injective ρ → ρ.IsIrreducible → Module.finrank (ZMod 2) V = 44 →
      IsSectionOf ρ codeExterior ∨ IsSectionOf ρ cocodeExterior

/-- The concrete exterior-square calculation, independent of section placement. -/
def GolayExteriorFiveBound : Prop :=
  ∀ x : M24, orderOf x = 5 →
    Module.finrank (ZMod 2) (fixedSpace codeExterior (Subgroup.zpowers x)) ≤ 11 ∧
    Module.finrank (ZMod 2) (fixedSpace cocodeExterior (Subgroup.zpowers x)) ≤ 11

end Representation.MathieuM24Degree44.FiveSpace
