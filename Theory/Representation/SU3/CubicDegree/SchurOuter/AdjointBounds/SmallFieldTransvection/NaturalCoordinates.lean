module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.MatrixEquations
public import Theory.Representation.SU3.CubicDegree.SchurOuter.Models
public import Theory.Representation.TensorInvolutionDisplacement
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Natural involutions and literal adjoint transvections

A nonidentity involution in characteristic two on a three-dimensional space
has one exchanged pair and one fixed line. Coordinates on those summands put
it into the matrix `1 + E₀₁`. Conjugating trace-zero endomorphisms by the same
linear equivalence then gives precisely the published transvection equation.

The result applies to the literal matrices of any ternary Hermitian form;
no unitary change of basis or classification of forms is needed for this step.
The parent module applies it to a lift of an original binary normalizer actor.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.11,
author manuscript pp.31–32, the adjoint-module exclusion.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module Representation.SL3.BinaryDefiningFactors
namespace Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.SmallField
variable {K : Type*} [Field K] [CharP K 2]

private def pairCoordinates : ((K × K) × K) ≃ₗ[K] (Fin 3 → K) where
  toFun p := ![p.1.2, p.1.1 + p.1.2, p.2]
  invFun v := ((v 1 - v 0, v 0), v 2)
  left_inv p := by ext <;> simp
  right_inv v := by ext i; fin_cases i <;> simp
  map_add' p q := by ext i; fin_cases i <;> simp; ring
  map_smul' c p := by ext i; fin_cases i <;> simp [mul_add]

private theorem pairCoordinates_swap (x y z : K) :
    pairCoordinates ((y, x), z) =
      Matrix.toLin' transvectionMatrix (pairCoordinates ((x, y), z)) := by
  ext i
  fin_cases i <;> simp [pairCoordinates, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, transvectionMatrix, add_left_comm, add_comm, CharTwo.add_self_eq_zero]

/-- Every nonidentity involution in dimension three has the literal transvection coordinates. -/
private theorem exists_natural_coordinates (N : Module.End K (Fin 3 → K))
    (hN : N * N = 1) (hne : N ≠ 1) :
    ∃ e : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K), ∀ v,
      e (N v) = Matrix.toLin' transvectionMatrix (e v) := by
  obtain ⟨H, e, he⟩ := TensorInvolutionDisplacement.exists_swap_form (K := K) N hN
  let R := LinearMap.range (N - 1)
  let : Module.Free K H := Module.Free.of_divisionRing K H
  let : Module.Free K R := Module.Free.of_divisionRing K R
  have hp : 0 < finrank K R := by
    by_contra! hh
    have hz : LinearMap.range (N - 1) = ⊥ :=
      Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hh)
    exact hne (sub_eq_zero.mp (LinearMap.range_eq_bot.mp hz))
  have hd : (finrank K R + finrank K R) + finrank K H = 3 := by
    have h := e.finrank_eq
    simpa only [finrank_prod, finrank_pi, Fintype.card_fin] using h
  have hR : finrank K R = 1 := by omega
  have hH : finrank K H = 1 := by omega
  let r : R ≃ₗ[K] K := LinearEquiv.ofFinrankEq _ _ (by simpa using hR)
  let z : H ≃ₗ[K] K := LinearEquiv.ofFinrankEq _ _ (by simpa using hH)
  let c := (LinearEquiv.prodCongr (LinearEquiv.prodCongr r r) z).trans pairCoordinates
  refine ⟨e.symm.trans c, ?_⟩
  intro v
  obtain ⟨⟨⟨x, y⟩, w⟩, rfl⟩ := e.surjective v
  rw [he]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact pairCoordinates_swap (r x) (r y) (z w)

private def adjointCoordinates (e : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) :
    AdjointSpace K ≃ₗ[K] AdjointSpace K where
  toFun X := ⟨e.conj X.val, by rw [LinearMap.mem_ker, LinearMap.trace_conj']; exact X.property⟩
  invFun X := ⟨e.symm.conj X.val, by rw [LinearMap.mem_ker, LinearMap.trace_conj']; exact X.property⟩
  left_inv X := by apply Subtype.ext; ext v; simp [LinearEquiv.conj_apply]
  right_inv X := by apply Subtype.ext; ext v; simp [LinearEquiv.conj_apply]
  map_add' X Y := Subtype.ext (e.conj.map_add X.val Y.val)
  map_smul' c X := Subtype.ext (e.conj.map_smul c X.val)

open BenderSuzuki.MatrixGroups
variable {F : Type*} [Field F]

/-- Conjugation by an actual nonidentity natural involution has transvection coordinates
on the literal trace-zero adjoint space. -/
theorem adjoint_isTransvection (J : HermitianForm 3 F) (ι : F →+* K)
    (g : J.specialSubgroup) (hg : g ^ 2 = 1) (hne : g ≠ 1) :
    IsTransvectionOperator (K := K) (W := AdjointSpace K) (adjoint J ι g) := by
  let M := g.val.val.map ι
  let N := Matrix.toLin' M
  have hM : M * M = 1 := by
    change g.val.val.map ι * g.val.val.map ι = 1
    rw [← Matrix.map_mul]
    have hh := congrArg (fun x : J.specialSubgroup => x.val.val)
      (show g * g = 1 by simpa only [pow_two] using hg)
    change g.val.val * g.val.val = 1 at hh
    rw [hh]
    exact ι.mapMatrix.map_one
  have hN : N * N = 1 := by
    change Matrix.toLin' M ∘ₗ Matrix.toLin' M = 1
    rw [← Matrix.toLin'_mul, hM, Matrix.toLin'_one]
    rfl
  have hNne : N ≠ 1 := by
    intro h
    apply hne
    apply Subtype.ext
    apply Units.ext
    have hh := congrArg LinearMap.toMatrix' h
    have hm : M = 1 := by
      simpa only [N, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_one] using hh
    ext i j
    apply ι.injective
    have hi := congrFun (congrFun hm i) j
    simpa [M, Matrix.map_apply, Matrix.one_apply] using hi
  obtain ⟨e, he⟩ := exists_natural_coordinates N hN hNne
  refine ⟨adjointCoordinates e, ?_⟩
  intro X
  apply Matrix.toLin'.injective
  simp only [Matrix.toLin'_mul, adjointMatrix_apply, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := e.surjective v
  change (e.conj (adjoint J ι g X).val) (Matrix.toLin' transvectionMatrix (e w)) =
    Matrix.toLin' transvectionMatrix ((e.conj X.val) (e w))
  rw [← he w]
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [adjoint_apply]
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hg)
  rw [hgi]
  change e (N (X.val (N (N w)))) = Matrix.toLin' transvectionMatrix (e (X.val w))
  have hNN : N (N w) = w := LinearMap.congr_fun hN w
  rw [hNN, he]

end Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.SmallField
