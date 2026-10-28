module
public import Theory.SpecificGroups.Triality.ShortRootCentralizer.Action
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Faithful PSL₂(q) action on the triality long-root plane

The central Levi is PSL₂(q), including q=4. Its conjugation action on the
characteristic long-root plane is nontrivial by the explicit torus equation.
Simplicity makes the kernel trivial, giving the faithful natural action
used in the nonunitary case of Aschbacher--Smith F.4.42, printed p.295
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Triality.Standard.ShortRootCentralizer
open Parabolics

@[expose] def planeLeviAction (P : Parameters) : levi P .central →* MulAut (plane P) :=
  (plane P).normalizerMonoidHom.comp
    (inclusion ((levi_le_parabolic P .central).trans (plane_normalized P)))

theorem planeLeviAction_apply (P : Parameters) (a : levi P .central) (v : plane P) :
    (planeLeviAction P a v).val = a.val*v.val*a.val⁻¹ := rfl

theorem planeLeviAction_injective (m : ℕ) (hm : 0<m) (hm2 : 1<m) :
    Function.Injective (planeLeviAction (binaryParameters m hm)) := by
  let P := binaryParameters m hm
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField P.prime P.exponent)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [card_baseField]
      exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hm2)
  let : IsSimpleGroup (levi P .central) := (leviCentralEquivPSL2 P rfl).isSimpleGroup
  apply (planeLeviAction P).ker_eq_bot_iff.mp
  rcases (planeLeviAction P).normal_ker.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hq : 2 < P.q := Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) hm2
    apply levi_moves_plane P rfl hq
    intro a ha v hv
    have he : planeLeviAction P ⟨a,ha⟩ = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [h]
      trivial
    have hh := congrArg (fun f : MulAut (plane P) => (f ⟨v,hv⟩).val) he
    change a*v*a⁻¹=v at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

/-- The actual central PSL₂(q) acts faithfully on the characteristic plane. -/
theorem plane_faithful_psl2 (m : ℕ) (hm : 0<m) (hm2 : 1<m) :
    let P := binaryParameters m hm
    ∃ ρ : PSL(2,GaloisField P.prime P.exponent) →* MulAut (plane P),
      Function.Injective ρ ∧
      (∀ a : levi P .central, ∀ v : plane P,
        (ρ (leviCentralEquivPSL2 P rfl a) v).val = a.val*v.val*a.val⁻¹) := by
  let P := binaryParameters m hm
  let ρ := (planeLeviAction P).comp (leviCentralEquivPSL2 P rfl).symm.toMonoidHom
  refine ⟨ρ,(planeLeviAction_injective m hm hm2).comp
    (leviCentralEquivPSL2 P rfl).symm.injective,?_⟩
  intro a v
  change (planeLeviAction P ((leviCentralEquivPSL2 P rfl).symm
    (leviCentralEquivPSL2 P rfl a)) v).val = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end Triality.Standard.ShortRootCentralizer
