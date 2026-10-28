module

public import Theory.Representation.OrthogonalFourPlusMatrix.HyperplaneFixedMatrix
public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Theory.Representation.BinaryOffender.HyperplaneFixed
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.FinCases

/-!
# Sylow fixed vectors of binary determinant hyperplane stabilizers

For a binary hyperplane in the eight-dimensional determinant module over F₄,
the fixed space of a Sylow two-subgroup of its actual setwise stabilizer lies
inside the hyperplane. Applying the imaginary-coordinate functional on F₄ to
the polar form gives a nondegenerate binary pairing, so every hyperplane is the
perpendicular space of a vector. The matrix point-stabilizer calculation puts
the full stabilizer's fixed space inside that perpendicular space; odd-orbit
averaging then gives the same containment for its Sylow two-subgroups.

The subgroup in the conclusion is the literal image of the Sylow subgroup
under the stabilizer inclusion into `SL₂(4) × SL₂(4)`. This supplies the matrix
geometry used in Aschbacher–Smith, 9.2.3 (1 March 2004 manuscript).
-/

@[expose] public noncomputable section

open Matrix Representation.BinaryOffender
namespace ClassicalOrthogonal.FourPlusMatrix.Binary.HyperplaneFixed
open HyperplaneFixedAux

/-- The binary polar pairing in the fixed concrete F₄ coordinates. -/
def pairing : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (fun (z x : V) => (polar z x).im)
    (by intro z w x; simp only [map_add, LinearMap.add_apply, QuadraticAlgebra.im_add])
    (by
      intro c z x
      have he := LinearMap.congr_fun (polar.map_smul_of_tower c z) x
      simpa only [LinearMap.smul_apply, QuadraticAlgebra.im_smul] using congrArg QuadraticAlgebra.im he)
    (by intro z x y; simp only [map_add, QuadraticAlgebra.im_add])
    (by
      intro c z x
      simpa only [QuadraticAlgebra.im_smul] using
        congrArg QuadraticAlgebra.im ((polar z).map_smul_of_tower c x))

theorem pairing_apply (z x : V) : pairing z x = (polar z x).im := rfl

/-- Every nonzero matrix is detected by the binary polar pairing. -/
theorem pairing_nondegenerate {z : V} (h : ∀ x, pairing z x = 0) : z = 0 := by
  have hcoeff (c : F) (hc : ∀ t : F, (c * t).im = 0) : c = 0 := by
    by_contra hn
    have he := hc (c⁻¹ * QuadraticAlgebra.omega)
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul] at he
    exact one_ne_zero he
  have h00 : z 0 0 = 0 := by
    apply hcoeff
    intro t
    have he := h !![0,0;0,t]
    rw [pairing_apply, polar_formula] at he
    simpa only [of_apply, cons_val_zero, cons_val_one, mul_zero, zero_add, add_zero] using he
  have h01 : z 0 1 = 0 := by
    apply hcoeff
    intro t
    have he := h !![0,0;t,0]
    rw [pairing_apply, polar_formula] at he
    simpa only [of_apply, cons_val_zero, cons_val_one, mul_zero, zero_add, add_zero] using he
  have h10 : z 1 0 = 0 := by
    apply hcoeff
    intro t
    have he := h !![0,t;0,0]
    rw [pairing_apply, polar_formula] at he
    simpa only [of_apply, cons_val_zero, cons_val_one, mul_zero, zero_add, add_zero] using he
  have h11 : z 1 1 = 0 := by
    apply hcoeff
    intro t
    have he := h !![t,0;0,0]
    rw [pairing_apply, polar_formula] at he
    simpa only [of_apply, cons_val_zero, cons_val_one, mul_zero, zero_add, add_zero] using he
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> assumption

theorem pairing_injective : Function.Injective pairing := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_bot_iff.mp
  intro z hz
  apply pairing_nondegenerate
  intro x
  exact LinearMap.congr_fun hz x

theorem pairing_surjective : Function.Surjective pairing :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by exact Subspace.dual_finrank_eq.symm)).mp pairing_injective

theorem pairing_action (g : G) (z x : V) :
    pairing (action g z) (action g x) = pairing z x := by
  exact congrArg QuadraticAlgebra.im (polar_action g z x)

/-- Every binary hyperplane is the kernel of pairing with a matrix. -/
theorem exists_pairing_ker (W : Submodule (ZMod 2) V)
    (hW : Module.finrank (ZMod 2) (V ⧸ W) = 1) :
    ∃ z : V, (pairing z).ker = W := by
  let e : (V ⧸ W) ≃ₗ[ZMod 2] ZMod 2 := LinearEquiv.ofFinrankEq _ _ (by
    simpa using hW)
  let f : V →ₗ[ZMod 2] ZMod 2 := e.toLinearMap.comp W.mkQ
  obtain ⟨z, hz⟩ := pairing_surjective f
  refine ⟨z, ?_⟩
  rw [hz]
  ext x
  change e (W.mkQ x) = 0 ↔ x ∈ W
  rw [map_eq_zero_iff e e.injective]
  exact Submodule.Quotient.mk_eq_zero W

theorem functional_invariant_of_stabilizer (W : Submodule (ZMod 2) V)
    (z : V) (hz : (pairing z).ker = W)
    (g : subspaceStabilizer action W) (x : V) :
    pairing z (action g x) = pairing z x := by
  have he : pairing z (action g x) = 0 ↔ pairing z x = 0 := by
    change action g x ∈ (pairing z).ker ↔ x ∈ (pairing z).ker
    rw [hz]
    exact g.property x
  have hb : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
  exact hb _ _ he

theorem point_fixed_of_stabilizer (W : Submodule (ZMod 2) V)
    (z : V) (hz : (pairing z).ker = W)
    (g : subspaceStabilizer action W) : action g z = z := by
  apply pairing_injective
  ext x
  have he := pairing_action (g : G) z (action (g : G)⁻¹ x)
  have hx : action (g : G) (action (g : G)⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hx] at he
  rw [he]
  exact functional_invariant_of_stabilizer W z hz g⁻¹ x

/-- The full setwise stabilizer fixes no vector outside the hyperplane. -/
theorem fixedSpace_stabilizer_le (W : Submodule (ZMod 2) V)
    (hW : Module.finrank (ZMod 2) (V ⧸ W) = 1) :
    fixedSpace action (subspaceStabilizer action W) ≤ W := by
  obtain ⟨z, hz⟩ := exists_pairing_ker W hW
  intro x hx
  rw [← hz]
  change pairing z x = 0
  have hp : polar z x = 0 := by
    apply polar_zero_of_fixed
    intro g hg
    have hstab : g ∈ subspaceStabilizer action W := by
      intro y
      rw [← hz]
      change pairing z (action g y) = 0 ↔ pairing z y = 0
      have he := pairing_action g z y
      change matrixAction g z = z at hg
      change pairing (matrixAction g z) (action g y) = pairing z y at he
      rw [hg] at he
      rw [he]
    exact hx ⟨g, hstab⟩
  rw [pairing_apply, hp]
  rfl

/-- A Sylow two-subgroup of the actual hyperplane stabilizer fixes no vector
outside the hyperplane, with its image in the original matrix group retained. -/
theorem fixedSpace_sylow_le (W : Submodule (ZMod 2) V)
    (hW : Module.finrank (ZMod 2) (V ⧸ W) = 1)
    (S : Sylow 2 (subspaceStabilizer action W)) :
    fixedSpace action ((S : Subgroup (subspaceStabilizer action W)).map
      (subspaceStabilizer action W).subtype) ≤ W := by
  obtain ⟨z, hz⟩ := exists_pairing_ker W hW
  have hfix : Representation.invariants
      (action.comp (subspaceStabilizer action W).subtype) ≤ (pairing z).ker := by
    intro x hx
    rw [hz]
    exact fixedSpace_stabilizer_le W hW hx
  have hs := sylow_fixedSpace_le_ker_of_invariant
    (action.comp (subspaceStabilizer action W).subtype) (pairing z)
    (fun g x => functional_invariant_of_stabilizer W z hz g x) hfix S
  intro x hx
  have hxs : x ∈ fixedSpace (action.comp (subspaceStabilizer action W).subtype)
      (S : Subgroup (subspaceStabilizer action W)) := by
    intro s
    exact hx ⟨s.1.1, Subgroup.mem_map.mpr ⟨s.1, s.2, rfl⟩⟩
  have he := hs hxs
  rwa [hz] at he

end ClassicalOrthogonal.FourPlusMatrix.Binary.HyperplaneFixed
