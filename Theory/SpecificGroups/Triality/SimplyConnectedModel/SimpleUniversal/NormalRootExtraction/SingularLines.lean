module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The singular-line definition and action are adapted from
Atlas/LinearGroups/Orthogonal/SingularPoints.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: use the existing CFSG Clifford Spin carrier and its natural action,
and add the concrete first-root fixed-line calculation.
-/

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RootPoints
public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# Singular lines of the concrete Spin D4 natural module

These are the singular projective points of the actual eight-dimensional
hyperbolic quadratic space. Spin acts through its already constructed natural
representation. The first positive simple root fixes the line through the
first vector of the first hyperbolic summand.

This supplies a common geometric interface for the primitive-action and
abelian-stabilizer arguments. Neither primitivity nor simplicity is assumed
in these definitions or fixed-point calculations. Only the forward natural
action is used; no algebraic inverse to the Spin cover is asserted.
Source: the classical type-D realization underlying GLS3, 1.10.1(b),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.NormalRootExtraction
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Pinning
open scoped LinearAlgebra.Projectivization
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

omit [IsAlgClosed k] [CharP k 2] in
theorem singular_mk_iff (v : QuadraticSpace k) (hv : v ≠ 0) :
    quadraticForm k (Projectivization.mk k v hv).rep = 0 ↔ quadraticForm k v = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  rw [← ha]
  change quadraticForm k (a.val • v) = 0 ↔ _
  rw [(quadraticForm k).map_smul, smul_eq_mul]
  simp only [mul_eq_zero, a.ne_zero, false_or]

/-- The singular one-dimensional subspaces of the hyperbolic natural module. -/
abbrev SingularLines := {p : ℙ k (QuadraticSpace k) // quadraticForm k p.rep = 0}

/-- A nonzero singular vector determines its projective line. -/
def singularLineMk (v : QuadraticSpace k) (hv : v ≠ 0)
    (hq : quadraticForm k v = 0) : SingularLines k :=
  ⟨Projectivization.mk k v hv, (singular_mk_iff k v hv).mpr hq⟩

/-- The action comes from the given Spin natural representation. -/
instance singularLinesAction : MulAction (Points k) (SingularLines k) where
  smul g p := ⟨(naturalAction k g).val • p.val, by
    rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk]
    apply (singular_mk_iff k _ _).mpr
    exact ((mem_quadraticIsometrySubgroup _ _).mp (naturalAction k g).prop _).trans p.prop⟩
  one_smul p := Subtype.ext (by
    change (naturalAction k 1).val • p.val = p.val
    rw [map_one]
    exact one_smul _ _)
  mul_smul g h p := Subtype.ext (by
    change (naturalAction k (g * h)).val • p.val =
      (naturalAction k g).val • ((naturalAction k h).val • p.val)
    rw [map_mul]
    exact mul_smul _ _ _)

omit [CharP k 2] in
theorem singularLineMk_smul (g : Points k) (v : QuadraticSpace k) (hv : v ≠ 0)
    (hq : quadraticForm k v = 0) :
    g • singularLineMk k v hv hq =
      singularLineMk k ((naturalAction k g).val v)
        (fun h => hv ((naturalAction k g).val.injective
          (h.trans (map_zero _).symm)))
        (((mem_quadraticIsometrySubgroup _ _).mp (naturalAction k g).prop v).trans hq) := rfl

/-- The first vector of the first hyperbolic summand. -/
def baseVector : QuadraticSpace k := (Pi.single 0 1, 0)

omit [IsAlgClosed k] [CharP k 2] in
theorem baseVector_ne_zero : baseVector k ≠ 0 := by
  intro h
  have := congrArg (fun v : QuadraticSpace k => v.1 0) h
  simp [baseVector] at this

omit [IsAlgClosed k] [CharP k 2] in
theorem baseVector_singular : quadraticForm k (baseVector k) = 0 := by
  simp [quadraticForm, baseVector, hyperbolicForm_apply]

/-- The singular line stabilized by the first positive simple root. -/
def baseLine : SingularLines k :=
  singularLineMk k (baseVector k) (baseVector_ne_zero k) (baseVector_singular k)

theorem positiveSimplePoint_zero_fixes_baseVector (a : k) :
    (naturalAction k (positiveSimplePoint k 0 a)).val (baseVector k) = baseVector k := by
  rw [naturalAction_rootPoint]
  simp [typeDSimpleRootIndex, show (-1 : ℝ) ≠ 1 by norm_num,
    evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
    hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv, baseVector]

theorem positiveSimplePoint_zero_fixes_baseLine (a : k) :
    positiveSimplePoint k 0 a • baseLine k = baseLine k := by
  apply Subtype.ext
  change (naturalAction k (positiveSimplePoint k 0 a)).val •
    Projectivization.mk k (baseVector k) _ = Projectivization.mk k (baseVector k) _
  rw [Projectivization.smul_mk]
  change Projectivization.mk k ((naturalAction k (positiveSimplePoint k 0 a)).val
    (baseVector k)) _ = _
  simp only [positiveSimplePoint_zero_fixes_baseVector]

end Triality.SimplyConnected.NormalRootExtraction
