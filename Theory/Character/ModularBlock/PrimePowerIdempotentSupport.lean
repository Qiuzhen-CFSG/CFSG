module

public import Theory.Character.ModularBlock.IdempotentTrace
public import Theory.Representation.IntegralPermutationTrace
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Central idempotent coefficients at prime-power elements

Over a characteristic-zero local domain with residue characteristic `p`,
a central idempotent has zero coefficient at every nonidentity element of
prime-power order. Translation by the element has no fixed group-basis
vectors. The integral permutation-summand trace formula therefore gives
zero trace; the central coefficient formula cancels the group order.

Unlike the support theorem for arbitrary prime-singular elements, this
prime-power case requires no roots of unity in the coefficient ring.
The argument specializes `PrimeSingularIdempotentSupport` and uses the
Brauer--Suzuki trace theorem from `IntegralPermutationTrace`.
-/

public section

noncomputable section
attribute [local instance] Fintype.ofFinite
namespace ModularBlock.CentralIdempotentSupport

private theorem permMatrix_mulLeft {R G : Type*} [CommRing R] [Group G]
    [Finite G] [DecidableEq G] (g : G) :
    (Equiv.mulLeft g⁻¹).permMatrix R =
      LinearMap.toMatrix (MonoidAlgebra.basis G R) (MonoidAlgebra.basis G R)
        (LinearMap.mulLeft R (MonoidAlgebra.of R G g)) := by
  classical
  ext i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, LinearMap.toMatrix_apply,
    MonoidAlgebra.of_apply]
  change (if g⁻¹ * i = j then 1 else 0) =
    (MonoidAlgebra.single (g * j) 1 : MonoidAlgebra R G).coeff i
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  congr 1
  exact propext (inv_mul_eq_iff_eq_mul.trans eq_comm)

/-- A central idempotent has no coefficient at a nontrivial prime-power element. -/
theorem coeff_inv_eq_zero_of_prime_power
    {R G : Type*} [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R]
    [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (hp : ¬ IsUnit (p : R))
    (e : MonoidAlgebra R G) (he : IsIdempotentElem e)
    (hc : e ∈ Set.center (MonoidAlgebra R G))
    (g : G) (hg : g ≠ 1) {a : ℕ} (hga : g ^ (p ^ a) = 1) :
    e.coeff g⁻¹ = 0 := by
  classical
  let : CharP (IsLocalRing.ResidueField R) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      rw [← map_natCast (IsLocalRing.residue R)]
      exact not_ne_iff.mp (fun h => hp ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h)))
  let b := MonoidAlgebra.basis G R
  let P := LinearMap.toMatrix b b (LinearMap.mulRight R e)
  let σ := Equiv.mulLeft g⁻¹
  have hσ : σ ^ (p ^ a) = 1 := by
    change (MulAction.toPermHom G G g⁻¹) ^ (p ^ a) = 1
    rw [← map_pow, inv_pow, hga, inv_one, map_one]
  have hfix : ∀ x, σ x ≠ x := by
    intro x hx
    exact hg (inv_eq_one.mp (mul_right_cancel (b := x) (by simpa [σ] using hx)))
  have hP : IsIdempotentElem P := by
    have he' : IsIdempotentElem (LinearMap.mulRight R e) := by
      change (LinearMap.mulRight R e).comp (LinearMap.mulRight R e) = _
      rw [← LinearMap.mulRight_mul, he]
    exact he'.map (LinearMap.toMatrixAlgEquiv b)
  have hcomm : Commute (σ.permMatrix R) P := by
    rw [show σ = Equiv.mulLeft g⁻¹ from rfl, permMatrix_mulLeft]
    change LinearMap.toMatrix b b _ * LinearMap.toMatrix b b _ =
      LinearMap.toMatrix b b _ * LinearMap.toMatrix b b _
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
    apply congrArg (LinearMap.toMatrix b b)
    apply LinearMap.ext
    intro y
    exact (mul_assoc _ _ _).symm
  have hz := Matrix.trace_permMatrix_mul_eq_trace_fixed_lift_of_prime
    (IsLocalRing.residue R) IsLocalRing.residue_surjective
    (fun r hr => (IsLocalRing.residue_ne_zero_iff_isUnit r).mp hr)
    σ hσ P hP hcomm (0 : Matrix {x // σ x = x} {x // σ x = x} R)
    (by simp [IsIdempotentElem]) (by ext x; exact (hfix x.val x.property).elim)
  have ht : LinearMap.trace R (MonoidAlgebra R G)
      ((LinearMap.mulLeft R (MonoidAlgebra.of R G g)).comp
        (LinearMap.mulRight R e)) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace R b]
    change Matrix.trace (LinearMap.toMatrix b b
      (LinearMap.mulLeft R (MonoidAlgebra.of R G g) * LinearMap.mulRight R e)) = 0
    rw [LinearMap.toMatrix_mul]
    simpa only [σ, P, permMatrix_mulLeft, Matrix.trace_zero] using hz
  rw [trace_mulLeft_comp_mulRight e hc g] at ht
  exact (mul_eq_zero.mp ht).resolve_left (Nat.cast_ne_zero.mpr (Nat.card_pos.ne'))
end ModularBlock.CentralIdempotentSupport
