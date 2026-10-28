module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.Operators
public import Theory.Representation.TensorInvolutionDisplacement
public import Mathlib.RepresentationTheory.Invariants

/-!
# Uniform displacement of adjoint-only tensor words

For square-one operators in characteristic two, tensoring with another such
operator cannot decrease the displacement fraction of the first factor.
The proof uses the exact tensor displacement formula and the half-dimension
upper bound for displacement. Thus one adjoint transpose already gives the
bound `dim ≤ 3 * displacement`, regardless of the number and positions of
other adjoint factors. Trivial factors are removed by the same formula.

The last theorem transports this bound to the literal common invariant
quotient of an arbitrary actor representation. It assumes an actual operator
intertwiner, whose source construction is a separate obligation.
Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.11,
internal pp.31--32; §2.2 and §3.5.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module
open scoped TensorProduct
open Representation.SL3.BinaryDefiningFactors
open Representation.BinaryOffender.NaturalTensor
open Representation.TensorInvolutionDisplacement
namespace Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement
variable {K : Type*} [Field K] [CharP K 2]

private theorem left_displacement_le_tensor {U W : Type*}
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A : Module.End K U) (B : Module.End K W) (hA : A * A = 1) (hB : B * B = 1) :
    finrank K W * operatorFixedCodim A ≤ operatorFixedCodim (TensorProduct.map A B) := by
  have h := tensor_displacement_formula A B hA hB
  have ha := twice_displacement_le A hA
  have hn := Nat.mul_le_mul_right (operatorFixedCodim B) ha
  nlinarith

/-- An adjoint-only word containing an adjoint factor moves at least a third of its dimension. -/
theorem wordDegree_le_three_displacement (w : List Factor)
    (hn : naturalCount w = 0) (ha : 0 < adjointCount w) :
    wordDegree w ≤ 3 * operatorFixedCodim (wordTranspose (K := K) w) := by
  induction w with
  | nil => simp [adjointCount] at ha
  | cons a w ih =>
    cases a with
    | natural => simp [naturalCount] at hn
    | dual => simp [naturalCount] at hn
    | trivial =>
      have hn' : naturalCount w = 0 := by simpa [naturalCount] using hn
      have ha' : 0 < adjointCount w := by simpa [adjointCount] using ha
      have h := tensor_displacement_formula (1 : Module.End K K)
        (wordTranspose (K := K) w) (by simp) (wordTranspose_sq w)
      have hz : operatorFixedCodim (1 : Module.End K K) = 0 := by
        simp [operatorFixedCodim]
      simp only [hz, Nat.mul_zero, Nat.zero_mul, add_zero, zero_add,
        Module.finrank_self, Nat.one_mul] at h
      change wordDegree (.trivial :: w) ≤ 3 * operatorFixedCodim
        (TensorProduct.map (1 : Module.End K K) (wordTranspose (K := K) w))
      rw [h]
      simpa [wordDegree, Factor.dimension] using ih hn' ha'
    | adjoint =>
      have h := left_displacement_le_tensor (U := Space K .adjoint) (W := WordSpace K w)
        (adjointTranspose (K := K))
        (wordTranspose (K := K) w) adjointTranspose_sq (wordTranspose_sq w)
      rw [finrank_wordSpace] at h
      have hr := three_le_adjointTranspose_displacement (K := K)
      have hd : wordDegree (.adjoint :: w) = 8 * wordDegree w := by
        simp [wordDegree, Factor.dimension]
      change wordDegree (.adjoint :: w) ≤ 3 * operatorFixedCodim (k := K)
        (V := Space K .adjoint ⊗[K] WordSpace K w)
        (TensorProduct.map (adjointTranspose (K := K)) (wordTranspose w))
      rw [hd]
      nlinarith

variable {G V : Type*} [Group G] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [CharP K 2] in
/-- Common invariants are contained in the fixed space of each literal actor. -/
theorem operatorFixedCodim_le_invariants_quotient (ρ : Representation K G V) (a : G) :
    operatorFixedCodim (ρ a) ≤ finrank K (V ⧸ ρ.invariants) := by
  have hle : ρ.invariants ≤ LinearMap.ker (ρ a - 1) := fun v hv => sub_eq_zero.mpr (hv a)
  have hm := Submodule.finrank_mono hle
  have hd := operatorFixedCodim_add_finrank (ρ a)
  have hq := ρ.invariants.finrank_quotient_add_finrank
  omega

/-- Apply the tensor estimate to the actual common invariant quotient via an intertwiner. -/
theorem wordDegree_le_three_invariants_quotient (ρ : Representation K G V) (a : G)
    (w : List Factor) (hn : naturalCount w = 0) (ha : 0 < adjointCount w)
    (e : V ≃ₗ[K] WordSpace K w)
    (he : ∀ v, e (ρ a v) = wordTranspose w (e v)) :
    wordDegree w ≤ 3 * finrank K (V ⧸ ρ.invariants) := by
  have hd := wordDegree_le_three_displacement (K := K) w hn ha
  rw [← operatorFixedCodim_eq_of_equiv (ρ a) (wordTranspose w) e he] at hd
  exact hd.trans (Nat.mul_le_mul_left 3 (operatorFixedCodim_le_invariants_quotient ρ a))
end Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement
