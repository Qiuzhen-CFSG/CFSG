module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# The six-dimensional alternative for an L₄ head

The six-dimensional model is the exterior square of the actual natural binary
four-space. Its action uses the same actor identification as the natural and
dual alternatives. An identification with this model includes a linear
isomorphism and its intertwining equation, not just a dimension or family tag.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.4.2(9–10),
B.4.5 and their application in 13.8.25, printed pp.960–961. The classification
and the marked-parabolic exclusion are not asserted by these definitions.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment

abbrev ExteriorSquare := ⋀[ZMod 2]^2 NaturalSpace

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

noncomputable def exteriorSquareAction (eH : H ≃* BinaryLinear.GL NaturalSpace) :
    Representation (ZMod 2) H ExteriorSquare where
  toFun g := exteriorPower.map 2 (naturalAction eH g)
  map_one' := by
    change exteriorPower.map 2 (naturalAction eH 1) = LinearMap.id
    exact (congrArg (exteriorPower.map 2) (naturalAction eH).map_one).trans
      exteriorPower.map_id
  map_mul' g h := by
    change exteriorPower.map 2 (naturalAction eH (g * h)) =
      (exteriorPower.map 2 (naturalAction eH g)).comp
        (exteriorPower.map 2 (naturalAction eH h))
    exact (congrArg (exteriorPower.map 2) ((naturalAction eH).map_mul g h)).trans
      (exteriorPower.map_comp _ _)

theorem exteriorSquare_finrank : Module.finrank (ZMod 2) ExteriorSquare = 6 := by
  rw [exteriorPower.finrank_eq]
  norm_num [NaturalSpace]
  decide

def IsExteriorSquare (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) : Prop :=
  ∃ e : U ≃ₗ[ZMod 2] ExteriorSquare,
    ∀ g u, e (ρ g u) = exteriorSquareAction eH g (e u)

/-- The two L₄ representation alternatives used from B.4.2/B.4.5. This is a
specification of their conclusion; it does not assert that a module satisfies
it without the faithful irreducible small-ratio hypotheses. -/
def HeadAlternatives (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) : Prop :=
  IsNaturalOrDual ρ eH ∨ IsExteriorSquare ρ eH

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
