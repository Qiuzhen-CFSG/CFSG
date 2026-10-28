module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedGeometry
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Module.ZMod

/-!
# Determinant one on the original homocyclic normalizer core

Coordinates on the whole C₄³ core turn actual conjugation by its normalizer
into matrices over Z/4. Since that core is abelian, the action factors through
the original PSL₃(2) quotient. Perfectness kills its determinant character.
The statement holds for every choice of coordinates on the original core.

This supplies the determinant constraint in the dual-plane involution-lift
calculation for the subgroup construction of I.4.8.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims

private def coordinateAdd {D : Type*} [Group D]
    (e : D ≃* Multiplicative (Fin 3 → ZMod 4)) (a : MulAut D) :
    (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4) where
  toFun x := (e (a (e.symm (Multiplicative.ofAdd x)))).toAdd
  map_zero' := by simp
  map_add' x y := by
    change (e (a (e.symm (Multiplicative.ofAdd x * Multiplicative.ofAdd y)))).toAdd = _
    simp

private def coordinateAction {D : Type*} [Group D]
    (e : D ≃* Multiplicative (Fin 3 → ZMod 4)) :
    MulAut D →* Module.End (ZMod 4) (Fin 3 → ZMod 4) where
  toFun a := (coordinateAdd e a).toZModLinearMap 4
  map_one' := by apply LinearMap.ext; intro x; funext i; simp [coordinateAdd]
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    funext i
    change (e ((a * b) (e.symm (Multiplicative.ofAdd x)))).toAdd i =
      (e (a (e.symm (e (b (e.symm (Multiplicative.ofAdd x))))))).toAdd i
    simp

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The actual conjugation representation of the whole normalizer core in
arbitrary homocyclic coordinates. -/
def TypeAt.coreMatrixAction (_h : TypeAt z V)
    (e : pCore 2 (normalizer (V : Set G)) ≃* Multiplicative (Fin 3 → ZMod 4)) :
    normalizer (V : Set G) →* Matrix (Fin 3) (Fin 3) (ZMod 4) :=
  LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp
    ((coordinateAction e).comp (MulAut.conjNormal :
      normalizer (V : Set G) →* MulAut (pCore 2 (normalizer (V : Set G)))))

/-- The matrix representation has the original conjugation action on every
element of the full two-core, with no quotient or coordinate factor omitted. -/
theorem TypeAt.coreMatrixAction_apply (h : TypeAt z V)
    (e : pCore 2 (normalizer (V : Set G)) ≃* Multiplicative (Fin 3 → ZMod 4))
    (g : normalizer (V : Set G)) (q : pCore 2 (normalizer (V : Set G))) :
    (h.coreMatrixAction e g).mulVec (e q).toAdd =
      (e (MulAut.conjNormal g q)).toAdd := by
  change (LinearMap.toMatrix' ((coordinateAdd e (MulAut.conjNormal g)).toZModLinearMap 4)).mulVec
    (e q).toAdd = _
  rw [LinearMap.toMatrix'_mulVec]
  change (e (MulAut.conjNormal g (e.symm (e q)))).toAdd = _
  rw [e.symm_apply_apply]

/-- Every matrix of the original normalizer action has determinant one over
Z/4, because the action factors through its perfect PSL₃(2) quotient. -/
theorem TypeAt.coreMatrixAction_det (h : TypeAt z V)
    (e : pCore 2 (normalizer (V : Set G)) ≃* Multiplicative (Fin 3 → ZMod 4))
    (g : normalizer (V : Set G)) : (h.coreMatrixAction e g).det = 1 := by
  let M := normalizer (V : Set G)
  let P := pCore 2 M
  let f := h.coreMatrixAction e
  have hk : P ≤ f.ker := by
    intro p hp
    have ha : (MulAut.conjNormal p : MulAut P) = 1 := by
      apply MulEquiv.ext
      intro q
      apply Subtype.ext
      change p * (q : M) * p⁻¹ = (q : M)
      have hc : p * (q : M) = (q : M) * p := by
        have hh : (⟨p, hp⟩ : P) * q = q * ⟨p, hp⟩ := e.injective (by
          simp only [map_mul, mul_comm])
        exact congrArg Subtype.val hh
      rw [hc, mul_inv_cancel_right]
    change LinearMap.toMatrixAlgEquiv' (coordinateAction e (MulAut.conjNormal p)) = 1
    rw [ha, map_one, map_one]
  let d := (Matrix.detMonoidHom.comp (QuotientGroup.lift P f hk)).toHomUnits
  obtain ⟨F, hF, hfin, hcard, ⟨q⟩⟩ := h.normalizer_quotient
  let := hF
  let := hfin
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
    Atlas.psl_perfect 3 (by decide)
  let b := (QuotientGroup.quotientMulEquivOfEq h.normalizer_fitting.symm).trans q
  let : Group.IsPerfect (M ⧸ P) :=
    Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  have hd : d (QuotientGroup.mk' P g) = 1 :=
    Abelianization.commutator_subset_ker d Group.IsPerfect.mem_commutator
  exact congrArg (fun u : (ZMod 4)ˣ => (u : ZMod 4)) hd

end CFSG.Quasithin.HigmanSims
