module

public import Theory.Representation.SpecialLinearNatural
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Data.ZMod.Basic

/-!
# Exterior-power models for ten-dimensional SL₅(2) modules

We construct the actual action of determinant-one matrices on exterior powers
of the natural five-dimensional binary module. The second and third exterior
powers both have dimension ten. The center of SL₅(2) is trivial, so the canonical
projection identifies this matrix group with L₅(2) = PSL₅(2).

Functoriality of exterior powers proves the representation laws; the exterior
basis gives the dimensions. The scalar-matrix description of the center reduces
its triviality to the two possible scalars in F₂.

These are models for the calculation in Aschbacher--Smith, *The Classification
of Quasithin Groups*, Lemma I.1.6(7), printed p.408/PDF p.419. This module does
not assert that the models exhaust the ten-dimensional irreducibles.
-/

@[expose] public section

open scoped TensorProduct

namespace Representation.SL5TenDimensional
/-- The determinant-one matrix group SL₅(2). -/
abbrev Group := Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
/-- The exterior power of the natural five-dimensional binary module. -/
abbrev ExteriorModule (r : ℕ) := ⋀[ZMod 2]^r (Fin 5 → ZMod 2)

/-- The action induced on exterior powers by the natural matrix action. -/
noncomputable def exteriorAction (r : ℕ) : Representation (ZMod 2) Group (ExteriorModule r) where
  toFun g := exteriorPower.map r (specialLinearNatural (k := ZMod 2) 5 g)
  map_one' := by
    change exteriorPower.map r (specialLinearNatural (k := ZMod 2) 5 1) = LinearMap.id
    exact (congrArg (exteriorPower.map r)
      (specialLinearNatural (k := ZMod 2) 5).map_one).trans exteriorPower.map_id
  map_mul' g h := by
    change exteriorPower.map r (specialLinearNatural (k := ZMod 2) 5 (g * h)) =
      (exteriorPower.map r (specialLinearNatural (k := ZMod 2) 5 g)).comp
        (exteriorPower.map r (specialLinearNatural (k := ZMod 2) 5 h))
    exact (congrArg (exteriorPower.map r)
      ((specialLinearNatural (k := ZMod 2) 5).map_mul g h)).trans
        (exteriorPower.map_comp _ _)

/-- The standard exterior-basis dimension formula specialized to F₂⁵. -/
theorem finrank_exteriorModule (r : ℕ) :
    Module.finrank (ZMod 2) (ExteriorModule r) = Nat.choose 5 r := by
  rw [exteriorPower.finrank_eq]
  simp

/-- There are no nonidentity scalar matrices of determinant one over F₂. -/
theorem center_eq_bot : Subgroup.center Group = ⊥ := by
  apply eq_bot_iff.mpr
  intro mat hmat
  change mat = 1
  obtain ⟨scalar, hpower, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hmat
  have hroot : ∀ scalar : ZMod 2, scalar ^ 5 = 1 → scalar = 1 := by decide
  have hscalarOne : scalar = 1 := hroot scalar (by simpa using hpower)
  apply Subtype.ext
  simpa [hscalarOne] using hscalar.symm

/-- The canonical projection identifies SL₅(2) with L₅(2). -/
noncomputable def projectiveEquiv :
    Group ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2) :=
  MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', center_eq_bot],
    QuotientGroup.mk'_surjective _⟩

/-- Coordinate formula on decomposable exterior products. -/
theorem exteriorAction_ιMulti (r : ℕ) (g : Group) (v : Fin r → Fin 5 → ZMod 2) :
    exteriorAction r g (exteriorPower.ιMulti (ZMod 2) r v) =
      exteriorPower.ιMulti (ZMod 2) r (fun j => Matrix.mulVec g.val (v j)) :=
  exteriorPower.map_apply_ιMulti _ _

/-- The exterior square is ten-dimensional. -/
theorem finrank_exteriorModule_two : Module.finrank (ZMod 2) (ExteriorModule 2) = 10 := by
  rw [finrank_exteriorModule]
  decide

/-- The exterior cube is ten-dimensional. -/
theorem finrank_exteriorModule_three : Module.finrank (ZMod 2) (ExteriorModule 3) = 10 := by
  rw [finrank_exteriorModule]
  decide

/-- The group identification uses the canonical quotient map. -/
@[simp] theorem projectiveEquiv_apply (g : Group) :
    projectiveEquiv g = QuotientGroup.mk' (Subgroup.center Group) g := rfl

end Representation.SL5TenDimensional
