module

public import Theory.AtlasPort.LinearGroups.G2.WeylMaps
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# An explicit octonion pair for the fixed G₂(5) presentation

Put `c = F(1) E(2)`. The pair is `R, c (R S)² c⁻¹`, expressed in
the genuine split-octonion root and Weyl automorphisms. Its definition thus
requires no recognition of the reference ATLAS matrices. The faithful matrix
map below allows subsequent finite certificates to be checked in eight
coordinates. Relation and generation certificates are separate results.

Sources: the root and Weyl formulas in the imported ATLAS port (Wilson's
split-octonion coordinates); the fixed presentation in `AtlasPresentation.lean`.
The short conjugating word was found by finite exploration of these formulas.
-/

@[expose] public section

namespace G2Five.AtlasPresentation

instance octonionFivePrime : Fact (Nat.Prime 5) := ⟨by decide⟩

open Atlas.G2 Atlas.SplitOctonion

/-- The conjugating element used in the order-three generator. -/
def octonionConjugator : Atlas.G2.Model (ZMod 5) := rootF 1 * rootE 2

/-- A fixed pair of actual octonion automorphisms, indexed as in the presentation. -/
def octonionGenerator : Bool → Atlas.G2.Model (ZMod 5)
  | false => weylR
  | true => octonionConjugator * (weylR * weylS)^2 * octonionConjugator⁻¹

/-- The faithful eight-coordinate matrix representation. -/
def octonionMatrix : Atlas.G2.Model (ZMod 5) →* Matrix (Fin 8) (Fin 8) (ZMod 5) where
  toFun g := LinearMap.toMatrix' g.val.toLinearMap
  map_one' := LinearMap.toMatrix'_one
  map_mul' g h := LinearMap.toMatrix'_comp g.val.toLinearMap h.val.toLinearMap

theorem octonionMatrix_injective : Function.Injective octonionMatrix := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact LinearMap.toMatrix'.injective he

@[simp] theorem octonionMatrix_apply (g : Atlas.G2.Model (ZMod 5)) (i j : Fin 8) :
    octonionMatrix g i j = g.val (basisVector j) i := rfl

/-- The involution matrix, acting on column vectors. -/
def octonionMatrixA : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![4,0,0,0,0,0,0,0;
     0,0,4,0,0,0,0,0;
     0,4,0,0,0,0,0,0;
     0,0,0,1,0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,0,0,0,0,4,0;
     0,0,0,0,0,4,0,0;
     0,0,0,0,0,0,0,4]

/-- The order-three matrix, acting on column vectors. -/
def octonionMatrixB : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![0,2,4,1,4,0,3,1;
     0,3,1,4,1,1,0,1;
     2,3,2,4,1,0,1,4;
     2,2,0,1,0,4,1,4;
     3,3,0,0,1,1,4,1;
     2,2,0,0,0,0,1,4;
     1,1,1,4,1,1,0,0;
     0,0,1,4,1,1,0,0]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem octonionMatrix_false : octonionMatrix (octonionGenerator false) = octonionMatrixA :=
  by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem octonionMatrix_true : octonionMatrix (octonionGenerator true) = octonionMatrixB :=
  by decide

theorem octonionGenerator_false_sq : octonionGenerator false ^ 2 = 1 := weylR_sq

end G2Five.AtlasPresentation
