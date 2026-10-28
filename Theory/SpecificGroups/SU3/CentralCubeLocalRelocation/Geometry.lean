module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.NormalizerAction.Permutations
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.InvolutionCalculus
public import Mathlib.GroupTheory.PGroup

/-!
# A central cubic scalar in a genuine cyclic-nine two-local subgroup

In an orthonormal frame the diagonal matrices diag(a,a,a⁻²) commute with
the first-coordinate transposition. When a has order nine, their cyclic
subgroup has order nine and contains the scalar at a³. The transposition
is an actual special-unitary involution in characteristic two.

This is the geometric step in the central cube relocation used for
Aschbacher--Smith A.2.12(II), printed p.37. Existence of a norm-one scalar
cube root is established separately from the original matrix cube equation.
-/

@[expose] public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.EvenInner
namespace BenderSuzuki.MatrixGroups.HermitianForm.CentralCubeLocalRelocation
open UnitaryThree.OddTorusNormalizer
variable {F : Type*} [Field F]

/-- The one-dimensional diagonal subgroup fixed by the coordinate swap. -/
def diagonal (J : HermitianForm 3 F) (P : OrthogonalFrame J) :
    normOne J →* J.specialSubgroup :=
  InvolutionCalculus.diagonalMap (specialPairHom J P)

theorem diagonal_injective (J : HermitianForm 3 F) (P : OrthogonalFrame J) :
    Function.Injective (diagonal J P) := by
  intro a b h
  exact congrArg Prod.fst ((specialPairHom_injective J P) h)

/-- Cubic elements of the diagonal subgroup are the original scalar matrices. -/
theorem diagonal_scalar (J : HermitianForm 3 F) (P : OrthogonalFrame J)
    (a : normOne J) (ha : a ^ 3 = 1) :
    (diagonal J P a).val = GeneralLinearGroup.scalar (Fin 3) a.val := by
  have hc : (a.val * a.val)⁻¹ = a.val := by
    have h : a.val * (a.val * a.val) = 1 := by
      have he := congrArg Subtype.val ha
      simpa [pow_succ, pow_two, mul_assoc] using he
    exact (eq_inv_of_mul_eq_one_left h).symm
  have hd : diagonalHom (pairDiagonal J (a, a)) =
      GeneralLinearGroup.scalar (Fin 3) a.val := by
    apply Units.ext
    change Matrix.diagonal (fun k => ((pairDiagonal J (a, a) k : Fˣ) : F)) =
      Matrix.diagonal (fun _ => (a.val : F))
    congr 1
    funext k
    fin_cases k
    · rfl
    · rfl
    · exact congrArg Units.val hc
  change P.val * diagonalHom (pairDiagonal J (a, a)) * P.val⁻¹ = _
  rw [hd]
  have hz : GeneralLinearGroup.scalar (Fin 3) a.val ∈ center (GL (Fin 3) F) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨a.val, rfl⟩
  rw [mem_center_iff.mp hz, mul_inv_cancel_right]

/-- The transposition is an actual order-two special-unitary matrix. -/
theorem swap_order [CharP F 2] (J : HermitianForm 3 F) (P : OrthogonalFrame J) :
    orderOf (specialPermutation J P (Equiv.swap 0 1)) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, pow_two, Equiv.swap_mul_self, map_one]
  · intro he
    have hco := congrArg (frameCoordinateHom J P) he
    rw [specialPermutation_coordinates, map_one] at hco
    have hh := congrArg (fun A : GL (Fin 3) F => A.val 0 1) hco
    norm_num [permutationGL_apply] at hh

/-- The diagonal subgroup centralizes the actual involution. -/
theorem diagonal_centralizes_swap [CharP F 2] (J : HermitianForm 3 F)
    (P : OrthogonalFrame J) (a : normOne J) :
    Commute (diagonal J P a) (specialPermutation J P (Equiv.swap 0 1)) := by
  have ha := specialMonomialAction_action J P (monomialPermutation J P (Equiv.swap 0 1))
  rw [specialMonomialAction_permutation] at ha
  have he := ha (a, a)
  have hp : permuteFramePair J (Equiv.swap 0 1) (a, a) = (a, a) := by
    simp [permuteFramePair, frameTriple]
  rw [hp] at he
  change specialPermutation J P (Equiv.swap 0 1) * diagonal J P a *
    (specialPermutation J P (Equiv.swap 0 1))⁻¹ = diagonal J P a at he
  have he' := congrArg (fun g : J.specialSubgroup => g *
    specialPermutation J P (Equiv.swap 0 1)) he
  have hcomm : specialPermutation J P (Equiv.swap 0 1) * diagonal J P a =
      diagonal J P a * specialPermutation J P (Equiv.swap 0 1) := by
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using he'
  exact hcomm.symm

/-- A norm-one ninth root gives a genuine cyclic-nine two-local witness,
containing its prescribed central scalar cube. -/
theorem local_witness_of_norm_root [CharP F 2] (J : HermitianForm 3 F)
    (P : OrthogonalFrame J) (a : normOne J) (ha : orderOf a = 9)
    (z : J.specialSubgroup)
    (hz : z.val = GeneralLinearGroup.scalar (Fin 3) (a.val ^ 3)) :
    ∃ Q C : Subgroup J.specialSubgroup, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
      IsCyclic C ∧ Nat.card C = 9 ∧ z ∈ C ∧ C ≤ normalizer (Q : Set J.specialSubgroup) := by
  let t := specialPermutation J P (Equiv.swap 0 1)
  let y := diagonal J P a
  have ht : orderOf t = 2 := swap_order J P
  have hy : orderOf y = 9 := by
    exact (orderOf_injective (diagonal J P) (diagonal_injective J P) a).trans ha
  have hy3 : y ^ 3 = z := by
    apply Subtype.ext
    change ((diagonal J P a) ^ 3).val = _
    rw [← map_pow, diagonal_scalar J P (a ^ 3) (by
      rw [← pow_mul, show 3 * 3 = 9 from rfl, ← ha, pow_orderOf_eq_one])]
    exact hz.symm
  refine ⟨zpowers t, zpowers y, ?_, ?_, inferInstance, ?_, ?_, ?_⟩
  · apply zpowers_ne_bot.mpr
    intro he
    rw [he, orderOf_one] at ht
    norm_num at ht
  · exact IsPGroup.of_card (n := 1) (by simp only [Nat.card_zpowers, ht, pow_one])
  · simpa only [Nat.card_zpowers] using hy
  · rw [← hy3]
    exact (zpowers y).pow_mem (mem_zpowers y) 3
  · apply le_trans ?_ (centralizer_le_normalizer _)
    rw [le_centralizer_iff, zpowers_le]
    apply mem_centralizer_iff.mpr
    intro g hg
    obtain ⟨k, rfl⟩ := hg
    exact (diagonal_centralizes_swap J P a).zpow_left k

end BenderSuzuki.MatrixGroups.HermitianForm.CentralCubeLocalRelocation
