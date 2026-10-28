module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
/-!
# Compatible matrix marks for the binary parabolics

The point mark consists of translations extended by the order-three subgroup
of its two-dimensional Levi factor. Its translation subgroup is a four-group.
The inverse-transpose automorphism, adjusted by coordinate reversal, transports
both marks to the standard incident line parabolic. Subsequent modules identify
these marks with the intrinsic two-residual and two-core.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.21(1), printed p.957, covered-A₆ paragraph.
-/

@[expose] public section
open Matrix Subgroup
namespace Matrix.PSL3Two.MarkedAutomorphisms

def pointResidualPred (g : SL) : Prop :=
  g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧
  ((g.val 1 1 = 1 ∧ g.val 1 2 = 0 ∧ g.val 2 1 = 0 ∧ g.val 2 2 = 1) ∨
   (g.val 1 1 = 0 ∧ g.val 1 2 = 1 ∧ g.val 2 1 = 1 ∧ g.val 2 2 = 1) ∨
   (g.val 1 1 = 1 ∧ g.val 1 2 = 1 ∧ g.val 2 1 = 1 ∧ g.val 2 2 = 0))
instance : DecidablePred pointResidualPred := fun _ => inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def pointA : Subgroup SL where
  carrier := {g | pointResidualPred g}
  one_mem' := by decide
  mul_mem' := by
    have h : ∀ g : SL, pointResidualPred g → ∀ h : SL, pointResidualPred h →
        pointResidualPred (g*h) := by decide +kernel
    intro a b ha hb
    exact h a ha b hb
  inv_mem' := by
    have h : ∀ g : SL, pointResidualPred g → pointResidualPred g⁻¹ := by decide +kernel
    exact h
instance : DecidablePred (· ∈ pointA) := fun g => inferInstanceAs (Decidable (pointResidualPred g))

def pointCorePred (g : SL) : Prop :=
  g.val 0 0 = 1 ∧ g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧
  g.val 1 1 = 1 ∧ g.val 1 2 = 0 ∧ g.val 2 1 = 0 ∧ g.val 2 2 = 1
instance : DecidablePred pointCorePred := fun _ => inferInstanceAs (Decidable (_ ∧ _))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def pointV : Subgroup SL where
  carrier := {g | pointCorePred g}
  one_mem' := by decide
  mul_mem' := by
    have h : ∀ g : SL, pointCorePred g → ∀ h : SL, pointCorePred h →
        pointCorePred (g*h) := by decide +kernel
    intro a b ha hb
    exact h a ha b hb
  inv_mem' := by
    have h : ∀ g : SL, pointCorePred g → pointCorePred g⁻¹ := by decide +kernel
    exact h
instance : DecidablePred (· ∈ pointV) := fun g => inferInstanceAs (Decidable (pointCorePred g))

private theorem transpose_mul (x y : SL) :
    SpecialLinearGroup.transpose (x * y) =
      SpecialLinearGroup.transpose y * SpecialLinearGroup.transpose x := by
  apply Subtype.ext
  exact Matrix.transpose_mul _ _
private theorem transpose_transpose (x : SL) :
    SpecialLinearGroup.transpose (SpecialLinearGroup.transpose x) = x := by
  apply Subtype.ext
  exact Matrix.transpose_transpose _
private theorem transpose_inv (x : SL) :
    SpecialLinearGroup.transpose x⁻¹ = (SpecialLinearGroup.transpose x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← transpose_mul, mul_inv_cancel]
  apply Subtype.ext
  exact Matrix.transpose_one

def inverseTranspose : MulAut SL where
  toFun x := (SpecialLinearGroup.transpose x)⁻¹
  invFun x := (SpecialLinearGroup.transpose x)⁻¹
  left_inv x := by dsimp only; rw [transpose_inv, transpose_transpose, inv_inv]
  right_inv x := by dsimp only; rw [transpose_inv, transpose_transpose, inv_inv]
  map_mul' x y := by rw [transpose_mul, _root_.mul_inv_rev]

def diagram : MulAut SL := MulAut.conj (Bruhat.perm 5) * inverseTranspose

theorem inverseTranspose_involutive : Function.Involutive inverseTranspose := by
  intro g
  change (SpecialLinearGroup.transpose (SpecialLinearGroup.transpose g)⁻¹)⁻¹ = g
  rw [transpose_inv, transpose_transpose, inv_inv]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem diagram_involutive : Function.Involutive diagram := by
  intro g
  have hw : inverseTranspose (Bruhat.perm 5) = Bruhat.perm 5 := by decide +kernel
  have hww : Bruhat.perm 5 * Bruhat.perm 5 = 1 := by decide +kernel
  change Bruhat.perm 5 * inverseTranspose
    (Bruhat.perm 5 * inverseTranspose g * (Bruhat.perm 5)⁻¹) * (Bruhat.perm 5)⁻¹ = g
  rw [map_mul, map_mul, map_inv, hw, inverseTranspose_involutive]
  calc
    _ = (Bruhat.perm 5 * Bruhat.perm 5) * g *
        (Bruhat.perm 5 * Bruhat.perm 5)⁻¹ := by group
    _ = g := by rw [hww]; simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem diagram_point_line (g : SL) : diagram g ∈ lineParabolicSL ↔
    g ∈ pointParabolicSL := by
  have he : diagram g =
      (Bruhat.perm 5 * SpecialLinearGroup.transpose g * (Bruhat.perm 5)⁻¹)⁻¹ := by
    change Bruhat.perm 5 * (SpecialLinearGroup.transpose g)⁻¹ * (Bruhat.perm 5)⁻¹ = _
    group
  rw [he, inv_mem_iff]
  have h : ∀ g : SL,
      Bruhat.perm 5 * SpecialLinearGroup.transpose g * (Bruhat.perm 5)⁻¹ ∈
        lineParabolicSL ↔ g ∈ pointParabolicSL := by decide +kernel
  exact h g

def lineA : Subgroup SL := pointA.comap diagram.toMonoidHom
def lineV : Subgroup SL := pointV.comap diagram.toMonoidHom
instance : DecidablePred (· ∈ lineA) := fun g => inferInstanceAs (Decidable (diagram g ∈ pointA))
instance : DecidablePred (· ∈ lineV) := fun g => inferInstanceAs (Decidable (diagram g ∈ pointV))

private theorem map_eq_comap_of_involutive {G : Type*} [Group G]
    (e : MulAut G) (he : Function.Involutive e) (H : Subgroup G) :
    H.map e.toMonoidHom = H.comap e.toMonoidHom := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    change e (e x) ∈ H
    rwa [he]
  · intro hg
    exact ⟨e g, hg, he g⟩

theorem pointA_map_diagram : pointA.map diagram.toMonoidHom = lineA :=
  map_eq_comap_of_involutive diagram diagram_involutive pointA

theorem pointV_map_diagram : pointV.map diagram.toMonoidHom = lineV :=
  map_eq_comap_of_involutive diagram diagram_involutive pointV

end Matrix.PSL3Two.MarkedAutomorphisms
