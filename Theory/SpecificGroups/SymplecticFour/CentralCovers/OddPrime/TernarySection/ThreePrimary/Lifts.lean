module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.ThreePrimary.Coordinates
public import Theory.GroupTheory.CentralThreeInvertedPlane
public import Theory.GroupTheory.Commutator.CentralExtensionPairing
import Mathlib.Tactic.FinCases

/-!
# Compatible cubic lifts for the ternary symplectic Sylow subgroup

The diagonal matrix `d` inverts `c`, so a commutator of lifts gives a cubic
lift C of c. Likewise h inverts the first symmetric-basis unipotent a₀,
giving a cubic lift X. Since h and a₀ both centralize a₁, X commutes with
every lift of a₁: conjugation by such a lift changes each commutator input
only by a central factor. Set Y = CXC⁻¹ and Z = CYC⁻¹. The equation C³ = 1
and conjugation now give all three commuting relations and the cyclic action.
Thus X,Y,Z,C define a lift of the actual order-81 matrix embedding.

This works for every surjective central extension, without a restriction on
the kernel or an assumption about the two-primary multiplier. Its consumer
in `ThreePrimary` transports this lift to the actual matrix subgroup and
applies transfer at its index 640.

Source: the ternary defining-prime step underlying Aschbacher–Smith
I.1.4(1), printed p.408, and GLS3 §6.1. The cubic commutator lift is the
existing `MonoidHom.inverted_cubic_commutator_lift`.
-/

@[expose] public section

open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.ThreePrimary
noncomputable section

def a (i : Fin 3) : G := u (Pi.single i 1)

theorem u_nsmul (x : V) (n : ℕ) : u x ^ n = u (n • x) :=
  (uHom.map_pow (.ofAdd x) n).symm

theorem a_cube (i : Fin 3) : a i ^ 3 = 1 := by
  rw [a, u_nsmul]
  have he : 3 • (Pi.single i (1 : K) : V) = 0 := by
    ext j
    simp [nsmul_eq_mul, Pi.single_apply, show (3 : K) = 0 from rfl]
  rw [he, u_zero]

theorem a_commute (i j : Fin 3) : Commute (a i) (a j) := by
  change u (Pi.single i 1) * u (Pi.single j 1) = u (Pi.single j 1) * u (Pi.single i 1)
  rw [← u_add, ← u_add, add_comm]

theorem c_conjugate_a0 : c*a 0*c⁻¹ = a 1 := by
  rw [a, c_mul_u, mul_inv_cancel_right]
  congr 1
  ext i; fin_cases i <;> simp

theorem c_conjugate_a1 : c*a 1*c⁻¹ = a 2 := by
  rw [a, c_mul_u, mul_inv_cancel_right]
  congr 1
  ext i; fin_cases i <;> simp

theorem h_conjugate_a0 : h*a 0*h⁻¹ = (a 0)⁻¹ := by
  rw [a, h_mul_u, mul_inv_cancel_right]
  change u _ = (uHom (.ofAdd (Pi.single 0 1)))⁻¹
  rw [← map_inv]
  congr 1
  ext i; fin_cases i <;> simp

theorem h_commute_a1 : Commute h (a 1) := by
  change h * u (Pi.single 1 1) = u (Pi.single 1 1) * h
  rw [h_mul_u]
  congr 2
  ext i; fin_cases i <;> simp

/-- A lifted commutator centralizes every lift of the common image centralizer. -/
theorem commute_commutator_of_image_commute {E B : Type*} [Group E] [Group B]
    (f : E →* B) (hk : f.ker ≤ Subgroup.center E)
    {r x y : E} (hr : Commute (f r) (f y)) (hx : Commute (f x) (f y)) :
    Commute ⁅r,x⁆ y := by
  have hh : y * ⁅r,x⁆ * y⁻¹ = ⁅r,x⁆ := by
    rw [conjugate_commutatorElement]
    apply CentralExtension.commutator_eq_of_image_eq f hk
    · simp only [map_mul, map_inv]
      rw [hr.symm.eq, mul_inv_cancel_right]
    · simp only [map_mul, map_inv]
      rw [hx.symm.eq, mul_inv_cancel_right]
  exact ((mul_inv_eq_iff_eq_mul).mp hh).symm

/-- Three commuting cubic elements give a homomorphism from the coordinate cube. -/
def tripleHom {H : Type*} [Group H] (x y z : H)
    (hx : x^3=1) (hy : y^3=1) (hz : z^3=1)
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z) :
    Multiplicative V →* H where
  toFun a := x ^ (a.toAdd 0).val * y ^ (a.toAdd 1).val * z ^ (a.toAdd 2).val
  map_one' := by simp
  map_mul' a b := by
    change x ^ (a.toAdd 0+b.toAdd 0).val * y ^ (a.toAdd 1+b.toAdd 1).val *
      z ^ (a.toAdd 2+b.toAdd 2).val = _
    rw [ZMod.val_add, ZMod.val_add, ZMod.val_add, ← pow_eq_pow_mod _ hx,
      ← pow_eq_pow_mod _ hy, ← pow_eq_pow_mod _ hz, pow_add, pow_add, pow_add,
      (hxy.pow_pow (b.toAdd 0).val (a.toAdd 1).val).mul_mul_mul_comm]
    exact ((hxz.pow_pow (b.toAdd 0).val (a.toAdd 2).val).mul_left
      (hyz.pow_pow (b.toAdd 1).val (a.toAdd 2).val)).mul_mul_mul_comm _ _

theorem a_pow (i : Fin 3) (k : K) : a i ^ k.val = u (Pi.single i k) := by
  rw [a, u_nsmul]
  congr 1
  ext j
  simp [Pi.single_apply, nsmul_eq_mul]

theorem u_decomposition (x : V) :
    u x = a 0 ^ (x 0).val * a 1 ^ (x 1).val * a 2 ^ (x 2).val := by
  rw [a_pow, a_pow, a_pow, ← u_add, ← u_add]
  congr 1
  ext i; fin_cases i <;> simp

theorem exists_compatible_generators {E : Type*} [Group E]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    ∃ C X Y Z : E,
      f C = c ∧ f X = a 0 ∧ f Y = a 1 ∧ f Z = a 2 ∧
      C^3=1 ∧ X^3=1 ∧ Y^3=1 ∧ Z^3=1 ∧
      Commute X Y ∧ Commute X Z ∧ Commute Y Z ∧
      C*X*C⁻¹=Y ∧ C*Y*C⁻¹=Z ∧ C*Z*C⁻¹=X := by
  obtain ⟨C₀, hC₀⟩ := hf c
  obtain ⟨D, hD⟩ := hf d
  obtain ⟨hC, hC3⟩ := f.inverted_cubic_commutator_lift hk C₀ D
    (by rw [hC₀]; exact c_cube) (by rw [hC₀, hD]; exact d_conjugate_c)
  let C := ⁅D,C₀⁆
  have hCf : f C = c := hC.trans hC₀
  obtain ⟨X₀, hX₀⟩ := hf (a 0)
  obtain ⟨H, hH⟩ := hf h
  obtain ⟨hX, hX3⟩ := f.inverted_cubic_commutator_lift hk X₀ H
    (by rw [hX₀]; exact a_cube 0) (by rw [hX₀, hH]; exact h_conjugate_a0)
  let X := ⁅H,X₀⁆
  have hXf : f X = a 0 := hX.trans hX₀
  let Y := C*X*C⁻¹
  let Z := C*Y*C⁻¹
  have hYf : f Y = a 1 := by
    simp only [Y, map_mul, map_inv, hCf, hXf]
    exact c_conjugate_a0
  have hZf : f Z = a 2 := by
    simp only [Z, map_mul, map_inv, hCf, hYf]
    exact c_conjugate_a1
  have hY3 : Y^3=1 := by dsimp [Y]; rw [conj_pow, hX3]; simp
  have hZ3 : Z^3=1 := by dsimp [Z]; rw [conj_pow, hY3]; simp
  have hcycle : C*Z*C⁻¹=X := by
    have h : C^3*X*(C^3)⁻¹=X := by rw [hC3]; simp
    simpa only [Z, Y, pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc] using h
  have hXY : Commute X Y := by
    apply commute_commutator_of_image_commute f hk
    · rw [hH, hYf]; exact h_commute_a1
    · rw [hX₀, hYf]; exact a_commute 0 1
  have hYZ : Commute Y Z := hXY.map (MulAut.conj C).toMonoidHom
  have hZX : Commute Z X := by
    have hh := hYZ.map (MulAut.conj C).toMonoidHom
    change Commute Z (C*Z*C⁻¹) at hh
    rwa [hcycle] at hh
  exact ⟨C,X,Y,Z,hCf,hXf,hYf,hZf,hC3,hX3,hY3,hZ3,hXY,hZX.symm,hYZ,rfl,rfl,hcycle⟩


/-- Every central extension lifts the actual order-81 matrix embedding. -/
theorem exists_embedding_lift {E : Type*} [Group E]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    ∃ s : Model →* E, f.comp s = embedding := by
  obtain ⟨C,X,Y,Z,hC,hX,hY,hZ,hC3,hX3,hY3,hZ3,hXY,hXZ,hYZ,hCX,hCY,hCZ⟩ :=
    exists_compatible_generators f hf hk
  let t := tripleHom X Y Z hX3 hY3 hZ3 hXY hXZ hYZ
  have hft (x : Multiplicative V) : f (t x) = uHom x := by
    change f (X ^ (x.toAdd 0).val * Y ^ (x.toAdd 1).val * Z ^ (x.toAdd 2).val) = u _
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, hX, hY, hZ]
    exact (u_decomposition x.toAdd).symm
  have ht (x : Multiplicative V) : C * t x * C⁻¹ = t (rotate x) := by
    change (MulAut.conj C) (X ^ (x.toAdd 0).val * Y ^ (x.toAdd 1).val *
      Z ^ (x.toAdd 2).val) = _
    rw [map_mul, map_mul, map_pow, map_pow, map_pow]
    change (C*X*C⁻¹) ^ (x.toAdd 0).val * (C*Y*C⁻¹) ^ (x.toAdd 1).val *
      (C*Z*C⁻¹) ^ (x.toAdd 2).val =
      X ^ (x.toAdd 2).val * Y ^ (x.toAdd 0).val * Z ^ (x.toAdd 1).val
    rw [hCX, hCY, hCZ]
    rw [mul_assoc (X ^ (x.toAdd 2).val)]
    exact ((hXY.pow_pow (x.toAdd 2).val (x.toAdd 0).val).mul_right
      (hXZ.pow_pow (x.toAdd 2).val (x.toAdd 1).val)).eq.symm
  let s : Model →* E := SemidirectProduct.lift t (cubicHom C hC3) (by
    intro k
    apply MonoidHom.ext
    intro x
    exact (conjugate_pow t rotate C ht k.toAdd.val x).symm)
  refine ⟨s, MonoidHom.ext fun x => ?_⟩
  change f (t x.left * C ^ x.right.toAdd.val) = embedding x
  rw [map_mul, map_pow, hft, hC]
  rfl

end
end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.ThreePrimary
