module

public import Theory.SpecificGroups.PSL3Even.InvolutionResidualRows
public import Theory.SpecificGroups.PSL3.ExtensionBorel.Linear
public import Theory.LinearAlgebra.Hermitian.PrimeFrobeniusNormalization
public import Theory.FieldTheory.QuadraticFrobenius
public import Theory.SpecificGroups.PSL3Four.GraphFieldTransport
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

/-!
# Marking every graph-field involution of PSL₃(4)

For the literal actor `linearConj g * fieldAction σ * graph`, its square-one
identity makes `g * σ(g⁻ᵀ)` scalar. Scalar Hilbert 90 adjusts `g⁻¹` to a
Hermitian Gram matrix. An orthonormal basis then makes the conjugated actor's
linear coefficient scalar, so it acts trivially on PSL₃. Coefficient transport
gives the actual graph-field marking and hence its elementary-nine fixed
two-residual.

The scalar descent calculation follows the local Gram construction in
`PSL3Even.OuterElementaryRank.FixedRanks.GraphFieldDescent`; the public
linear-action kernel description supplies its scalar lifting step here.
Hermitian normalization is Huppert II.10.4, through
`Hermitian.PrimeFrobeniusNormalization`.

Source: Aschbacher–Smith, 15.3.38, printed pp.1136–1137, and the graph-field
row of 16.1.4(5), printed p.1171. The actual graph-field transport and its
GF(4) residual calculation are retained, including their scalar quotients.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.OuterSolvable BenderSuzuki.MatrixGroups
open Matrix.PSL3Even.OuterElementaryRank.FixedRanks
namespace Matrix.PSL3Four.GraphFieldMarking
variable {K : Type*} [Field K]

private def twist (σ : K ≃+* K) : GL (Fin 3) K →* GL (Fin 3) K :=
  (GeneralLinearGroup.map σ.toRingHom).comp (inverseTransposeGL K)

private theorem twist_twice (σ : K ≃+* K) (hs : σ ^ 2 = 1) (g : GL (Fin 3) K) :
    twist σ (twist σ g) = g := by
  apply Units.ext
  ext i j
  exact DFunLike.congr_fun hs (g.val i j)

private theorem twist_scalar (σ : K ≃+* K) (u : Kˣ) :
    twist σ (GeneralLinearGroup.scalar (Fin 3) u) =
      GeneralLinearGroup.scalar (Fin 3) (Units.map σ.toMonoidHom u)⁻¹ := by
  apply Units.ext
  ext i j
  change σ ((GeneralLinearGroup.scalar (Fin 3) u).inv j i) = _
  by_cases hij : i = j <;> simp [GeneralLinearGroup.scalar, Matrix.scalar_apply,
    hij, eq_comm]

private theorem scalar_parameter (σ : K ≃+* K) (hi : Function.Involutive σ)
    (hne : σ ≠ 1) (k : K) (hk : σ k * k = 1) :
    ∃ t : K, t ≠ 0 ∧ σ t * k = t := by
  have hn : ∃ s : K, σ s ≠ s := by
    by_contra! h
    exact hne (RingEquiv.ext h)
  by_cases hkneg : k = -1
  · obtain ⟨s, hs⟩ := hn
    refine ⟨s - σ s, sub_ne_zero.mpr (Ne.symm hs), ?_⟩
    rw [hkneg, map_sub, hi]
    ring
  · refine ⟨1 + k, ?_, ?_⟩
    · intro h
      apply hkneg
      linear_combination h
    · rw [map_add, map_one, add_mul, one_mul, hk, add_comm]

private theorem exists_hermitian (g : GL (Fin 3) K) (σ : K ≃+* K) (hne : σ ≠ 1)
    (h : (linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ * graph K) ^ 2 = 1) :
    ∃ (J : HermitianForm 3 K) (t : K), J.conj = σ ∧ t ≠ 0 ∧ J.form = t • g.inv := by
  have hs := graphField_part_sq g σ h
  have hi : Function.Involutive σ := fun x => DFunLike.congr_fun hs x
  have hlin : linearConj K (g * twist σ g) = 1 := by
    rw [graphField_sq, hs, map_one, mul_one] at h
    exact h
  have hcentral : g * twist σ g ∈ center (GL (Fin 3) K) := by
    rw [← Matrix.PSL3.ExtensionBorel.linearConj_ker]
    exact hlin
  rw [GeneralLinearGroup.center_eq_range_scalar] at hcentral
  obtain ⟨u, hu⟩ := hcentral
  have hnorm : σ (u : K) * (u : K) = 1 := by
    have ht := congrArg (twist σ) hu
    rw [twist_scalar, map_mul, twist_twice σ hs] at ht
    have hc : twist σ g * g = GeneralLinearGroup.scalar (Fin 3) u := by
      apply mul_left_cancel (a := g)
      rw [← mul_assoc, ← hu, GeneralLinearGroup.scalar_commute]
    rw [hc] at ht
    have he : (Units.map σ.toMonoidHom u)⁻¹ = u := by
      apply Units.ext
      exact congrArg (fun a : GL (Fin 3) K => a.val 0 0) ht
    have he' : Units.map σ.toMonoidHom u * u = 1 := by
      calc
        _ = Units.map σ.toMonoidHom u * (Units.map σ.toMonoidHom u)⁻¹ :=
          congrArg (fun z => Units.map σ.toMonoidHom u * z) he.symm
        _ = 1 := mul_inv_cancel _
    exact congrArg Units.val he'
  obtain ⟨t, ht, htu⟩ := scalar_parameter σ hi hne u hnorm
  have hadj : twist σ g = g⁻¹ * GeneralLinearGroup.scalar (Fin 3) u := by
    rw [hu, inv_mul_cancel_left]
  have he (i j : Fin 3) : σ (g.inv j i) = g.inv i j * (u : K) := by
    have hh := congrArg (fun z : GL (Fin 3) K => z.val i j) hadj
    change σ (g.inv j i) = (g.inv * Matrix.scalar (Fin 3) (u : K)) i j at hh
    simpa [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply] using hh
  refine ⟨⟨σ, hi, t • g.inv, ?_, ?_⟩, t, rfl, ht, rfl⟩
  · intro i j
    change σ (t * g.inv j i) = t * g.inv i j
    rw [map_mul, he]
    calc σ t * (g.inv i j * ↑u) = (σ t * ↑u) * g.inv i j := by ring
         _ = t * g.inv i j := by rw [htu]
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ ht) (GeneralLinearGroup.det_ne_zero g⁻¹)

private theorem conjugate_coefficient (g C : GL (Fin 3) K) (σ : K ≃+* K) :
    MulAut.congr (linearConj K C⁻¹) (linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ * graph K) =
      linearConj K (C⁻¹ * g * twist σ C) * Matrix.PSL3.OuterSolvable.fieldAction K σ * graph K := by
  change linearConj K C⁻¹ * (linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ * graph K) *
    (linearConj K C⁻¹)⁻¹ = _
  rw [← map_inv, inv_inv]
  calc
    _ = linearConj K C⁻¹ * linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ *
      (graph K * linearConj K C) := by group
    _ = linearConj K C⁻¹ * linearConj K g *
      (Matrix.PSL3.OuterSolvable.fieldAction K σ * linearConj K (inverseTransposeGL K C)) * graph K := by
        rw [graph_linearConj]; group
    _ = _ := by
      rw [field_linearConj]
      simp only [← mul_assoc, ← map_mul]
      rfl

private theorem gram_coefficient (g C : GL (Fin 3) K) (σ : K ≃+* K)
    (J : HermitianForm 3 K) (t : K) (hJ : J.conj = σ) (ht : t ≠ 0)
    (hform : J.form = t • g.inv)
    (hC : J.conjTranspose C.val * J.form * C.val = 1) :
    C⁻¹ * g * twist σ C = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 t ht) := by
  let k := GeneralLinearGroup.scalar (Fin 3) (Units.mk0 t ht)
  have hunit : (twist σ C)⁻¹ * k * g⁻¹ * C = 1 := by
    apply Units.ext
    have hadj : ((twist σ C)⁻¹).val = J.conjTranspose C.val := by
      ext i j
      change σ (C.val j i) = J.conj (C.val j i)
      rw [hJ]
    change ((twist σ C)⁻¹).val * k.val * g.inv * C.val = 1
    rw [hadj]
    have hk : k.val * g.inv = t • g.inv := by
      change Matrix.diagonal (fun _ : Fin 3 => t) * g.inv = t • g.inv
      exact (Matrix.smul_eq_diagonal_mul g.inv t).symm
    rw [mul_assoc (J.conjTranspose C.val), hk, ← hform]
    exact hC
  have he : k * g⁻¹ * C = twist σ C := by
    calc
      k * g⁻¹ * C = twist σ C * ((twist σ C)⁻¹ * k * g⁻¹ * C) := by group
      _ = twist σ C := by rw [hunit, mul_one]
  rw [← he]
  have hk := GeneralLinearGroup.scalar_commute (Units.mk0 t ht) g
  change C⁻¹ * g * (k * g⁻¹ * C) = k
  calc
    _ = C⁻¹ * (g * k) * g⁻¹ * C := by group
    _ = C⁻¹ * (k * g) * g⁻¹ * C := by rw [← hk]
    _ = C⁻¹ * k * C := by group
    _ = k := by
      rw [← (GeneralLinearGroup.scalar_commute (Units.mk0 t ht) C⁻¹)]
      group
      rfl

/-- Every involution with nontrivial field part in the graph coset is
linearly conjugate to its literal field-graph action. -/
theorem linear_conjugate [Finite K] (hK : Nat.card K = 4)
    (g : GL (Fin 3) K) (σ : K ≃+* K) (hne : σ ≠ 1)
    (hs : (linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ * graph K) ^ 2 = 1) :
    ∃ C : GL (Fin 3) K,
      MulAut.congr (linearConj K C)
        (linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ * graph K) = Matrix.PSL3.OuterSolvable.fieldAction K σ * graph K := by
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa [Nat.card_eq_fintype_card] using hK)
  have hσ : ∀ x : K, σ x = x ^ 2 := by
    have he := FiniteField.involution_eq_frobenius_of_card_square
      (p := 2) hK σ (orderOf_eq_prime (graphField_part_sq g σ hs) hne)
    intro x
    rw [he]
    rfl
  obtain ⟨J, t, hJ, ht, hform⟩ := exists_hermitian g σ hne hs
  obtain ⟨C, hC⟩ := J.exists_orthonormal_basis_of_prime_frobenius
    (p := 2) (fun x => by rw [hJ, hσ]) hK
  refine ⟨C⁻¹, ?_⟩
  rw [conjugate_coefficient, gram_coefficient g C σ J t hJ ht hform hC]
  have hscalar : linearConj K (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 t ht)) = 1 := by
    have hc : GeneralLinearGroup.scalar (Fin 3) (Units.mk0 t ht) ∈
        center (GL (Fin 3) K) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    rw [← Matrix.PSL3.ExtensionBorel.linearConj_ker] at hc
    exact hc
  rw [hscalar, one_mul]

/-- A compatible marking in the fixed four-element-field projective model. -/
theorem marking [Finite K] (hK : Nat.card K = 4)
    (g : GL (Fin 3) K) (σ : K ≃+* K) (hne : σ ≠ 1)
    (hs : (linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ * graph K) ^ 2 = 1) :
    ∃ e : PSL(3,K) ≃* Matrix.PSL3Four.PSL, ∀ x,
      e ((linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ * graph K) x) =
        (graph Matrix.PSL3Four.F * Matrix.PSL3Four.pslFrobenius) (e x) := by
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa [Nat.card_eq_fintype_card] using hK)
  have hσ : ∀ x : K, σ x = x ^ 2 := by
    have he := FiniteField.involution_eq_frobenius_of_card_square
      (p := 2) hK σ (orderOf_eq_prime (graphField_part_sq g σ hs) hne)
    intro x
    rw [he]
    rfl
  obtain ⟨C, hC⟩ := linear_conjugate hK g σ hne hs
  apply Matrix.PSL3Four.exists_graphField_marking hK σ hσ _
  apply isConj_iff.mpr
  refine ⟨linearConj K C, ?_⟩
  exact hC.trans (field_commute_graph σ).eq

/-- The exact marking input of the binary fixed-residual row. -/
theorem fourGraphFieldMarking [Finite K] :
    Matrix.PSL3Even.InvolutionResidualRows.FourGraphFieldMarking K :=
  fun hK g σ hne hs => marking hK g σ hne hs

/-- The literal fixed two-residual of every twisted graph-field involution
over the four-element field is elementary abelian of order nine. -/
theorem fixedResidual [Finite K] (hK : Nat.card K = 4)
    (g : GL (Fin 3) K) (σ : K ≃+* K) (hne : σ ≠ 1)
    (hs : (linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ * graph K) ^ 2 = 1) :
    Nonempty (pResidual 2 (linearConj K g * Matrix.PSL3.OuterSolvable.fieldAction K σ * graph K).fixedSubgroup ≃*
      Multiplicative (Fin 2 → ZMod 3)) :=
  Matrix.PSL3Even.InvolutionResidualRows.graphField_four_row fourGraphFieldMarking hK g σ hne hs

end Matrix.PSL3Four.GraphFieldMarking
end
