module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed.Coordinates
public import Mathlib.RepresentationTheory.Basic

/-!
# Inputs to the central-root displacement calculation

The two interfaces separate independent calculations. The seed calculation
places its fixed vector in the image of the simple root I+E₀₁ and supplies
the cyclic-branch dimensions and fixation by three upper triangular roots.
The lower-factor calculation constructs the natural or dual coordinate
directions. Neither interface includes membership in the central-root image.

These are explicit intermediate proof contracts, not encodings of source
13.8.25. Their realization from the marked generating seed and the compatible
natural-or-dual lower module is required before source assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed p.962 (PDF p.979).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed
open Representation BinaryLinear.MiddleParabolic

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- The simple-root image and rank information to be extracted from the actual seed.
The central-root membership of the marked vector is deliberately absent. -/
structure SeedRootFrame (ρ : Representation (ZMod 2) H U)
    (φ : BinaryLinear.GL V ≃* H) (A : Subgroup H) (v : U) : Prop where
  central_mem : φ centralRoot ∈ A
  simple_rank : Module.finrank (ZMod 2) (LinearMap.range (ρ (φ (actor 1)) - 1)) = 2
  central_rank : Module.finrank (ZMod 2) (LinearMap.range (ρ (φ centralRoot) - 1)) = 2
  simple_displacement : v ∈ LinearMap.range (ρ (φ (actor 1)) - 1)
  cross_fixed : ρ (φ (actor 3)) v = v
  shear_fixed : ρ (φ (actor 5)) v = v
  central_fixed : ρ (φ centralRoot) v = v

/-- The coordinate alternatives supplied by a compatible natural or dual lower factor.
In the dual case the second shear moves the lower direction outside the first bound. -/
def HasLowerRootDirections (ρ : Representation (ZMod 2) H U)
    (φ : BinaryLinear.GL V ≃* H) (v : U) : Prop :=
  ∃ w : U,
    w ∈ LinearMap.range (ρ (φ (actor 1)) - 1) ∧ w ≠ 0 ∧
    v ∉ Submodule.span (ZMod 2) ({w} : Set U) ∧
    ρ (φ centralRoot) w = w ∧
    (ρ (φ (actor 3)) w = w ∨
      ∃ a b : U, ρ (φ (actor 3)) w = w + a ∧
        ρ (φ (actor 5)) w = w + b ∧ ρ (φ (actor 5)) a = a ∧
        b ∉ Submodule.span (ZMod 2) ({v, w, a} : Set U))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed
