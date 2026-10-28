module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.ProjectiveOmega
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Transport of the orthogonal commutator group

A quadratic isometry conjugates the full isometry groups, hence identifies
their commutator subgroups. The resulting group equivalence intertwines the
literal actions on the two vector spaces. This is the change-of-coordinates
step in the Hermitian construction of Ω₄⁻; it preserves quadratic values in
characteristic two. See Aschbacher--Smith I.1.6(3), printed p.408.
-/

@[expose] public noncomputable section

namespace Representation.OrthogonalFourMinus.HermitianEquiv
open ClassicalOrthogonal.Minus
universe u
variable {k V W : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {Q : QuadraticForm k V} {R : QuadraticForm k W}

/-- Conjugation of the full quadratic-isometry groups by an isometry. -/
def orthogonalCongr (e : Q.IsometryEquiv R) :
    Orthogonal k V Q ≃* Orthogonal k W R where
  toFun g := ⟨e.toLinearEquiv.symm.trans (g.val.trans e.toLinearEquiv), by
    apply (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr
    intro w
    change R (e (g.val (e.symm w))) = R w
    rw [e.map_app, (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp g.property, e.symm.map_app]⟩
  invFun g := ⟨e.toLinearEquiv.trans (g.val.trans e.toLinearEquiv.symm), by
    apply (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr
    intro v
    change Q (e.symm (g.val (e v))) = Q v
    rw [e.symm.map_app, (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp g.property, e.map_app]⟩
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change e.symm (e (g.val (e.symm (e v)))) = g.val v
    simp
  right_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    change e (e.symm (g.val (e (e.symm w)))) = g.val w
    simp
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    change e (g.val (h.val (e.symm w))) = e (g.val (e.symm (e (h.val (e.symm w)))))
    simp

@[simp] theorem orthogonalCongr_apply (e : Q.IsometryEquiv R)
    (g : Orthogonal k V Q) (v : V) :
    (orthogonalCongr e g).val (e v) = e (g.val v) := by
  change e (g.val (e.symm (e v))) = _
  rw [e.symm_apply_apply]

/-- Conjugation carries the commutator onto the commutator, without recognition assumptions. -/
theorem map_commutator_orthogonalCongr (e : Q.IsometryEquiv R) :
    (commutator (Orthogonal k V Q)).map (orthogonalCongr e).toMonoidHom =
      commutator (Orthogonal k W R) := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (orthogonalCongr e).surjective, ← commutator_def]

/-- The induced equivalence of the literal Omega subgroups. -/
def omegaCongr (e : Q.IsometryEquiv R) : Omega k V Q ≃* Omega k W R :=
  ((orthogonalCongr e).subgroupMap (commutator (Orthogonal k V Q))).trans
    (MulEquiv.subgroupCongr (map_commutator_orthogonalCongr e))

@[simp] theorem omegaCongr_apply (e : Q.IsometryEquiv R)
    (g : Omega k V Q) (v : V) :
    (omegaCongr e g).val.val (e v) = e (g.val.val v) :=
  orthogonalCongr_apply e g.val v

end Representation.OrthogonalFourMinus.HermitianEquiv
