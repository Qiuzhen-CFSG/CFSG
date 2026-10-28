module

public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.NoncommRing
/-!
# Four-element scalars from an inverted order-five action

For a binary representation of D₁₀ with fixed-point-free rotation r, the
operator r+r⁻¹ satisfies X²+X+1=0. Evaluating the concrete quadratic field
at that operator supplies F₄ scalars on the original additive carrier.
The dihedral action and every commuting action are linear for these scalars.

This is the scalar construction for the dihedral rows of Aschbacher–Smith,
Proposition 8.2.8(5), printed pp.718–719. In particular no field structure or
tensor decomposition is an input. The marked quotient application is in
Chapter8/Section02/Normalizer/TensorRecognition/Dihedral.
-/

@[expose] public section
namespace InvertedFiveTensor
abbrev F := Representation.SL2FourNatural.F
abbrev D := DihedralGroup 5
abbrev rot : D := DihedralGroup.r 1
abbrev invt : D := DihedralGroup.sr 0
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (σ : Representation (ZMod 2) D V)
theorem rot_fifth : rot ^ 5 = 1 := by decide +kernel
theorem invt_square : invt * invt = 1 := by decide +kernel
theorem invt_rot : invt * rot = rot ^ 4 * invt := by decide +kernel
private theorem op_fifth : σ rot ^ 5 = 1 := by rw [← map_pow, rot_fifth, map_one]
private theorem norm_zero (hf : ∀ v, σ rot v = v → v = 0) :
    σ rot ^ 4 + σ rot ^ 3 + σ rot ^ 2 + σ rot + 1 = 0 := by
  have h : (σ rot - 1) * (σ rot ^ 4 + σ rot ^ 3 + σ rot ^ 2 + σ rot + 1) = 0 := by
    calc
      _ = σ rot ^ 5 - 1 := by noncomm_ring
      _ = 0 := by rw [op_fifth, sub_self]
  ext v
  apply hf
  have he := LinearMap.congr_fun h v
  change σ rot ((σ rot ^ 4 + σ rot ^ 3 + σ rot ^ 2 + σ rot + 1 : Module.End (ZMod 2) V) v) -
    (σ rot ^ 4 + σ rot ^ 3 + σ rot ^ 2 + σ rot + 1 : Module.End (ZMod 2) V) v = 0 at he
  exact sub_eq_zero.mp he

def scalarOperator : Module.End (ZMod 2) V := σ rot + σ rot ^ 4

theorem scalar_quadratic (hf : ∀ v, σ rot v = v → v = 0) :
    scalarOperator σ ^ 2 + scalarOperator σ + 1 = 0 := by
  have h8 : σ rot ^ 8 = σ rot ^ 3 := by
    calc
      _ = σ rot ^ 5 * σ rot ^ 3 := (pow_add _ 5 3)
      _ = σ rot ^ 3 := by rw [op_fifth, one_mul]
  have h2 (x : Module.End (ZMod 2) V) : x + x = 0 := by
    simpa only [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul, one_smul] using
      (add_smul (1 : ZMod 2) 1 x).symm
  calc
    _ = (σ rot ^ 4 + σ rot ^ 3 + σ rot ^ 2 + σ rot + 1) +
        (σ rot ^ 5 + σ rot ^ 5) := by
      dsimp [scalarOperator]
      rw [show (σ rot + σ rot ^ 4) ^ 2 = σ rot ^ 2 + σ rot ^ 8 +
        (σ rot ^ 5 + σ rot ^ 5) by noncomm_ring, h8]
      abel
    _ = 0 := by rw [norm_zero σ hf, h2, add_zero]

theorem scalar_commutes (g : D) : Commute (σ g) (scalarOperator σ) := by
  have hh : ∀ g : D,
      (g * rot = rot * g ∧ g * rot ^ 4 = rot ^ 4 * g) ∨
      (g * rot = rot ^ 4 * g ∧ g * rot ^ 4 = rot * g) := by decide +kernel
  change σ g * (σ rot + σ rot ^ 4) = (σ rot + σ rot ^ 4) * σ g
  rw [mul_add, add_mul, ← map_pow, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  rcases hh g with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2, add_comm]

abbrev omega : F := ⟨0, 1⟩
theorem omega_ne_zero : omega ≠ 0 := by decide +kernel

def scalarMap (hf : ∀ v, σ rot v = v → v = 0) : F →ₐ[ZMod 2] Module.End (ZMod 2) V :=
  QuadraticAlgebra.lift ⟨scalarOperator σ, by
    have he : scalarOperator σ ^ 2 = -(scalarOperator σ + 1) := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [add_assoc] using scalar_quadratic σ hf
    have hn (a : Module.End (ZMod 2) V) : -a = a := by
      rw [← neg_one_smul (ZMod 2), show (-1 : ZMod 2) = 1 by decide, one_smul]
    simpa only [pow_two, hn, one_smul, add_comm] using he⟩

@[instance_reducible] def fieldModule (hf : ∀ v, σ rot v = v → v = 0) : Module F V :=
  Module.compHom _ (scalarMap σ hf).toRingHom

theorem fieldTower (hf : ∀ v, σ rot v = v → v = 0) : letI := fieldModule σ hf
    IsScalarTower (ZMod 2) F V := by
  let := fieldModule σ hf
  constructor
  intro r a v
  change scalarMap σ hf (r • a) v = r • (scalarMap σ hf a v)
  rw [map_smul]
  rfl

variable (hf : ∀ v, σ rot v = v → v = 0)

/-- Promote a commuting binary operator to the recovered field. -/
def fieldLinear (f : Module.End (ZMod 2) V) (hc : Commute f (scalarOperator σ)) :
    letI := fieldModule σ hf; Module.End F V := by
  let := fieldModule σ hf
  refine { f.toAddHom with map_smul' := ?_ }
  intro a v
  change f (a.re • v + a.im • scalarOperator σ v) =
    a.re • f v + a.im • scalarOperator σ (f v)
  rw [map_add, map_smul, map_smul]
  exact congrArg (fun w => a.re • f v + a.im • w) (LinearMap.congr_fun hc.eq v)

def fieldRepresentation : letI := fieldModule σ hf; Representation F D V := by
  let := fieldModule σ hf
  exact { toFun := fun g => fieldLinear σ hf (σ g) (scalar_commutes σ g)
          map_one' := by ext v; exact LinearMap.congr_fun σ.map_one v
          map_mul' := by intro g h; ext v; exact LinearMap.congr_fun (σ.map_mul g h) v }

theorem omega_smul (v : V) : letI := fieldModule σ hf
    omega • v = σ rot v + (σ rot ^ 4) v := by
  change (0 : ZMod 2) • v + (1 : ZMod 2) • scalarOperator σ v = _
  simp only [zero_smul, one_smul, zero_add]
  rfl



/-- A binary operator commuting with the rotation is linear over the recovered field. -/
def commutingFieldLinear (f : Module.End (ZMod 2) V) (hc : Commute f (σ rot)) :
    letI := fieldModule σ hf; Module.End F V :=
  fieldLinear σ hf f (by
    change f * (σ rot + σ rot ^ 4) = (σ rot + σ rot ^ 4) * f
    rw [mul_add, add_mul, hc.eq, (hc.pow_right 4).eq])

/-- The original commuting group action, now over the recovered field. -/
def commutingFieldRepresentation {K : Type*} [Monoid K]
    (κ : Representation (ZMod 2) K V) (hc : ∀ k, Commute (κ k) (σ rot)) :
    letI := fieldModule σ hf; Representation F K V := by
  let := fieldModule σ hf
  exact { toFun := fun k => commutingFieldLinear σ hf (κ k) (hc k)
          map_one' := by ext v; exact LinearMap.congr_fun κ.map_one v
          map_mul' := by intro g h; ext v; exact LinearMap.congr_fun (κ.map_mul g h) v }

theorem commutingFieldRepresentation_apply {K : Type*} [Monoid K]
    (κ : Representation (ZMod 2) K V) (hc : ∀ k, Commute (κ k) (σ rot)) (k : K) (v : V) :
    commutingFieldRepresentation σ hf κ hc k v = κ k v := rfl

/-- The binary dimension is twice the recovered field dimension. -/
theorem field_finrank : letI := fieldModule σ hf
    2 * Module.finrank F V = Module.finrank (ZMod 2) V := by
  let := fieldModule σ hf
  let := fieldTower σ hf
  have h := Module.finrank_mul_finrank (ZMod 2) F V
  rwa [QuadraticAlgebra.finrank_eq_two] at h

end InvertedFiveTensor
