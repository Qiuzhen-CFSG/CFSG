module

public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Self-duality of the binary natural SL₂(4) module

The trace of the determinant of two columns is an invariant binary bilinear
form on F₄². Its radical is zero, so it identifies the natural binary module
with its contragredient without changing the SL₂(4) marking. The only finite
check tests nondegeneracy on the sixteen vectors. Upper unipotents and the
coordinate interchange also show that the common fixed space is zero.

Application: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(3), printed p.432 (PDF p.443): the commutator dual Q/HC of U/Z
is again the natural L₂(4)-module.
-/

@[expose] public section
noncomputable section
namespace Representation.SL2FourNatural

/-- The trace-determinant form over the binary ground field. -/
def binaryPairing : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V where
  toFun v := {
    toFun w := QuadraticAlgebra.trace (wedge v w)
    map_add' w x := by
      rw [show wedge v (w + x) = wedge v w + wedge v x by
        simp only [wedge, Pi.add_apply]; ring, map_add]
    map_smul' c w := by
      change QuadraticAlgebra.trace (wedge v (c • w)) =
        c • QuadraticAlgebra.trace (wedge v w)
      rw [show wedge v (c • w) = c • wedge v w by
        simp [wedge, Pi.smul_apply, smul_sub], map_smul] }
  map_add' v w := by
    apply LinearMap.ext
    intro x
    change QuadraticAlgebra.trace (wedge (v + w) x) =
      QuadraticAlgebra.trace (wedge v x) + QuadraticAlgebra.trace (wedge w x)
    rw [show wedge (v + w) x = wedge v x + wedge w x by
      simp only [wedge, Pi.add_apply]; ring, map_add]
  map_smul' c v := by
    apply LinearMap.ext
    intro w
    change QuadraticAlgebra.trace (wedge (c • v) w) =
      c • QuadraticAlgebra.trace (wedge v w)
    rw [show wedge (c • v) w = c • wedge v w by
      simp [wedge, Pi.smul_apply, smul_sub], map_smul]

theorem binaryPairing_apply (v w : V) :
    binaryPairing v w = QuadraticAlgebra.trace (wedge v w) := rfl

theorem binaryPairing_invariant (g : SL) (v w : V) :
    binaryPairing (action g v) (action g w) = binaryPairing v w := by
  simp only [binaryPairing_apply, wedge_action]

theorem binaryPairing_injective : Function.Injective binaryPairing := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  have hn : ∀ v : V, (∀ w : V, QuadraticAlgebra.trace (wedge v w) = 0) → v = 0 := by
    decide +kernel
  exact hn v (fun w => congrArg (fun f : Module.Dual (ZMod 2) V => f w) hv)

/-- The invariant form identifies the natural module with its linear dual. -/
def selfDual : V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V :=
  LinearEquiv.ofBijective binaryPairing
    ⟨binaryPairing_injective,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (Subspace.dual_finrank_eq (K := ZMod 2) (V := V)).symm).mp binaryPairing_injective⟩

theorem selfDual_equivariant (g : SL) (v : V) :
    selfDual (action g v) = (selfDual v).comp (action g⁻¹).toLinearMap := by
  apply LinearMap.ext
  intro w
  change binaryPairing (action g v) w = binaryPairing v (action g⁻¹ w)
  have h := binaryPairing_invariant g v (action g⁻¹ w)
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
  exact h

/-- The given natural action, regarded as a representation on the binary space. -/
def naturalRepresentation : Representation (ZMod 2) SL V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp action

theorem naturalRepresentation_apply (g : SL) (v : V) :
    naturalRepresentation g v = action g v := rfl

/-- The full natural SL₂(4) action has no nonzero fixed vector. -/
theorem natural_fixed_eq_zero (v : V) (hv : ∀ g : SL, action g v = v) : v = 0 := by
  have h1 : v 1 = 0 := (upper_fixed_iff v).mp (fun a => hv (upper a))
  let s : SL := ⟨!![0, 1; 1, 0], by
    simp [Matrix.det_fin_two]; decide⟩
  have h0 : v 0 = v 1 := by
    have h := congrFun (hv s) 1
    change s.val.mulVec v 1 = v 1 at h
    simpa [s, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  funext i
  fin_cases i
  · exact h0.trans h1
  · exact h1

end Representation.SL2FourNatural
