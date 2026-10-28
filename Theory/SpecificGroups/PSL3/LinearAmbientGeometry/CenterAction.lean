module
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Theory.FieldTheory.CubicDisplacement
public import Mathlib.Algebra.CharP.Reduced

/-!
# The central action of a root-plane preserving automorphism

The commutator pairing in UT₃ reconstructs one field automorphism from
the two root-plane actions. Cubic torus displacements force that field
automorphism to fix every cube. Outside the four-element field it is
trivial; a two-power automorphism then fixes the center pointwise.
This is the intrinsic calculation for the nonexceptional core-containment
step of Aschbacher–Smith §5.3.7, printed p.660 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3.LinearAmbientGeometry
open Matrix.PSL3Even.UnipotentGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem comm_coordinates (u v : U F) :
    ⁅u,v⁆ = central F (Multiplicative.ofAdd (u.x*v.y-v.x*u.y)) := by
  apply U.ext <;>
    simp only [commutatorElement_def, mul_x, mul_y, mul_c]
  all_goals dsimp [Inv.inv, central]
  all_goals ring

omit [CharP F 2] in
/-- A plane-preserving automorphism of UT₃ acts semilinearly on its center. -/
theorem center_semilinear (a : MulAut (U F))
    (h₁ : ∀ u ∈ V₁ F, a u ∈ V₁ F)
    (h₂ : ∀ u ∈ V₂ F, a u ∈ V₂ F) :
    ∃ (c : F) (σ : F ≃+* F), c ≠ 0 ∧
      ∀ x : F, a (central F (Multiplicative.ofAdd x)) =
        central F (Multiplicative.ofAdd (c * σ x)) := by
  let C : F → F := fun x => (a (central F (Multiplicative.ofAdd x))).c
  have hC (x : F) : a (central F (Multiplicative.ofAdd x)) =
      central F (Multiplicative.ofAdd (C x)) := by
    apply U.ext
    · exact (mem_V₂ F _).mp (h₂ _ (by simp [central]))
    · exact (mem_V₁ F _).mp (h₁ _ (by simp [central]))
    · rfl
  have hC0 : C 0 = 0 := by
    change (a 1).c = 0
    rw [map_one,one_c]
  have hCi : Function.Injective C := by
    intro x y hxy
    exact Multiplicative.ofAdd.injective (central_injective F
      (a.injective ((hC x).trans ((congrArg (fun t => central F (Multiplicative.ofAdd t)) hxy).trans (hC y).symm))))
  have hCn : C 1 ≠ 0 := by
    intro hh
    exact one_ne_zero (hCi (hh.trans hC0.symm))
  have hCa (x y : F) : C (x+y) = C x+C y := by
    have hh := congrArg U.c (map_mul a (central F (Multiplicative.ofAdd x))
      (central F (Multiplicative.ofAdd y)))
    rw [← map_mul (central F)] at hh
    rw [hC,hC] at hh
    simpa [C,central] using hh
  let A : F → F := fun x => (a (⟨x,0,0⟩ : U F)).x
  let B : F → F := fun y => (a (⟨0,y,0⟩ : U F)).y
  have hc (x y : F) : C (x*y) = A x * B y := by
    have hh := map_commutatorElement a (⟨x,0,0⟩ : U F) (⟨0,y,0⟩ : U F)
    rw [comm_coordinates,comm_coordinates] at hh
    have ha := (mem_V₁ F _).mp (h₁ (⟨x,0,0⟩ : U F) (by simp))
    have hb := (mem_V₂ F _).mp (h₂ (⟨0,y,0⟩ : U F) (by simp))
    have hh' := congrArg U.c hh
    simpa [C,A,B,ha,hb,central] using hh'
  have hCm (x y : F) : C (x*y) * C 1 = C x * C y := by
    rw [hc,show C 1 = A 1*B 1 from by simpa using hc 1 1,
      show C x = A x*B 1 from by simpa using hc x 1,
      show C y = A 1*B y from by simpa using hc 1 y]
    ring
  let σ : F →+* F := {
    toFun x := C x / C 1
    map_zero' := by rw [hC0,zero_div]
    map_one' := div_self hCn
    map_add' x y := by rw [hCa,add_div]
    map_mul' x y := by
      have hh := hCm x y
      field_simp
      exact hh }
  have hσi : Function.Injective σ := by
    intro x y hh
    exact hCi ((div_left_inj' hCn).mp hh)
  let e : F ≃+* F := RingEquiv.ofBijective σ ⟨hσi,Finite.surjective_of_injective hσi⟩
  refine ⟨C 1,e,hCn,fun x => ?_⟩
  rw [hC]
  congr 2
  change C x = C 1 * (C x/C 1)
  field_simp

/-- Cubic torus displacement eliminates the field part outside field four. -/
theorem center_fixed_of_cubic_torus (hq : 4 < Nat.card F)
    (a : MulAut (U F))
    (h₁ : ∀ u ∈ V₁ F, a u ∈ V₁ F)
    (h₂ : ∀ u ∈ V₂ F, a u ∈ V₂ F)
    (hp : ∃ k : ℕ, a ^ (2^k) = 1)
    (ht : ∀ t : Fˣ,
      (a (⟨(t:F)^3,0,0⟩ : U F)).x = (t:F)^3 * (a (⟨1,0,0⟩ : U F)).x) :
    ∀ x : F, a (central F (Multiplicative.ofAdd x)) = central F (Multiplicative.ofAdd x) := by
  obtain ⟨c,σ,hc,hσ⟩ := center_semilinear a h₁ h₂
  have hcross (x y : F) : c * σ (x*y) =
      (a (⟨x,0,0⟩ : U F)).x * (a (⟨0,y,0⟩ : U F)).y := by
    have hh := map_commutatorElement a (⟨x,0,0⟩ : U F) (⟨0,y,0⟩ : U F)
    rw [comm_coordinates,comm_coordinates] at hh
    have ha := (mem_V₁ F _).mp (h₁ (⟨x,0,0⟩ : U F) (by simp))
    have hb := (mem_V₂ F _).mp (h₂ (⟨0,y,0⟩ : U F) (by simp))
    simp only [zero_mul,sub_zero] at hh
    rw [hσ] at hh
    simpa [central,ha,hb] using congrArg U.c hh
  have hfix (x : F) : σ (x^3) = x^3 := by
    by_cases hx : x = 0
    · simp [hx]
    apply mul_left_cancel₀ hc
    have hh := hcross (x^3) 1
    have htx := ht (Units.mk0 x hx)
    change (a (⟨x^3,0,0⟩ : U F)).x = x^3 * (a (⟨1,0,0⟩ : U F)).x at htx
    rw [mul_one,htx] at hh
    have h1 := hcross 1 1
    simp only [mul_one,map_one] at h1
    rw [hh,mul_assoc,←h1,mul_comm]
  have he : σ = 1 := (FiniteField.eq_one_or_card_le_four_of_cubes_fixed σ hfix).resolve_right
    (Nat.not_le_of_lt hq)
  have hscalar (x : F) : a (central F (Multiplicative.ofAdd x)) =
      central F (Multiplicative.ofAdd (c*x)) := by simpa [he] using hσ x
  have hpow (k : ℕ) (x : F) : (a^k) (central F (Multiplicative.ofAdd x)) =
      central F (Multiplicative.ofAdd (c^k*x)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ',MulAut.mul_apply,ih,hscalar,pow_succ']
      simp only [mul_assoc]
  obtain ⟨k,hk⟩ := hp
  have hck : c^(2^k) = 1 := by
    have hh := hpow (2^k) 1
    rw [hk] at hh
    simpa [central] using (congrArg U.c hh).symm
  have hc1 : c = 1 := by
    simpa using (ExpChar.pow_prime_pow_mul_eq_one_iff 2 k 1 c).mp (by simpa using hck)
  intro x
  simpa [hc1] using hscalar x
end Matrix.PSL3.LinearAmbientGeometry
