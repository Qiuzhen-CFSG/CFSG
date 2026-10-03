module

public import Theory.Character.ModularBlock.IdempotentTrace
public import Theory.Representation.IntegralSpectralTrace
public import Theory.GroupTheory.PrimeRegularDecomposition
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Prime-singular support of central idempotents

A central idempotent in a finite group algebra over a characteristic-zero local
domain has zero coefficient at every element whose order is divisible by the
residue characteristic, provided the ring contains primitive roots of all
prime-to-characteristic orders.

Split the group element into commuting prime-power and prime-regular parts.
Left translation by the nonidentity prime part is fixed-point-free, and right
multiplication by the idempotent commutes with both translations. The integral
spectral trace theorem gives trace zero. The central coefficient trace formula
and characteristic-zero cancellation then recover the desired coefficient.

The underlying integral trace argument and its source (the Brauer--Suzuki
argument cited in Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)*, J. Algebra 6 (1967), p. 71, equation (6)) are documented in
`Theory.Representation.IntegralSpectralTrace`. The regular-module coefficient
formula is proved in `Theory.Character.ModularBlock.IdempotentTrace`.
-/

public section

noncomputable section
attribute [local instance] Fintype.ofFinite
namespace ModularBlock.CentralIdempotentSupport

private theorem residue_charP {R : Type*} [CommRing R] [IsLocalRing R]
    (p : ℕ) [Fact p.Prime] (hp : ¬ IsUnit (p : R)) :
    CharP (IsLocalRing.ResidueField R) p := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  rw [← map_natCast (IsLocalRing.residue R)]
  exact not_ne_iff.mp (fun h => hp ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h))

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

private theorem trace_mulLeft_mulRight_eq_zero_of_prime_dvd_orderOf
    {R G : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (hp : ¬ IsUnit (p : R))
    (hroots : ∀ n : ℕ, n ≠ 0 → ¬ p ∣ n → ∃ ζ : R, IsPrimitiveRoot ζ n)
    (e : MonoidAlgebra R G) (he : IsIdempotentElem e)
    (g : G) (hg : p ∣ orderOf g) :
    LinearMap.trace R (MonoidAlgebra R G)
      ((LinearMap.mulLeft R (MonoidAlgebra.of R G g)).comp
        (LinearMap.mulRight R e)) = 0 := by
  classical
  let : CharP (IsLocalRing.ResidueField R) p := residue_charP p hp
  obtain ⟨t, v, ⟨a, hta⟩, hv, hcomm, htv⟩ :=
    exists_commuting_prime_parts p Fact.out g
  have ht : t ≠ 1 := by
    intro ht
    apply hv
    rw [ht, one_mul] at htv
    exact htv.symm ▸ hg
  let b := MonoidAlgebra.basis G R
  let L : G →* Matrix G G R := (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp
    ((Algebra.lmul R (MonoidAlgebra R G)).toMonoidHom.comp (MonoidAlgebra.of R G))
  let P := LinearMap.toMatrix b b (LinearMap.mulRight R e)
  let σ := Equiv.mulLeft t⁻¹
  have hσ : σ ^ (p ^ a) = 1 := by
    change (MulAction.toPermHom G G t⁻¹) ^ (p ^ a) = 1
    rw [← map_pow, inv_pow, hta, inv_one, map_one]
  have hfix : ∀ x, σ x ≠ x := by
    intro x hx
    exact ht (inv_eq_one.mp (mul_right_cancel (b := x) (by simpa [σ] using hx)))
  have hmatrix (x : G) : (Equiv.mulLeft x⁻¹).permMatrix R = L x :=
    permMatrix_mulLeft x
  have hP : IsIdempotentElem P := by
    have he' : IsIdempotentElem (LinearMap.mulRight R e) := by
      change (LinearMap.mulRight R e).comp (LinearMap.mulRight R e) = _
      rw [← LinearMap.mulRight_mul, he]
    exact he'.map (LinearMap.toMatrixAlgEquiv b)
  have hLP (x : G) : Commute (L x) P := by
    change LinearMap.toMatrix b b _ * LinearMap.toMatrix b b _ =
      LinearMap.toMatrix b b _ * LinearMap.toMatrix b b _
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
    apply congrArg (LinearMap.toMatrix b b)
    apply LinearMap.ext
    intro y
    exact (mul_assoc _ _ _).symm
  have hvunit : IsUnit (orderOf v : R) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [map_natCast]
    exact fun hz => hv ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField R) p _).mp hz)
  obtain ⟨ζ, hζ⟩ := hroots (orderOf v) (orderOf_pos v).ne' hv
  have hvpow : L v ^ orderOf v = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hz := Matrix.trace_permMatrix_mul_mul_eq_zero_of_prime
    (IsLocalRing.residue R) IsLocalRing.residue_surjective
    (fun r hr => (IsLocalRing.residue_ne_zero_iff_isUnit r).mp hr)
    σ hσ hfix (L v) P hP (by simpa only [σ, hmatrix] using hLP t)
    (hLP v) (by simpa only [σ, hmatrix] using hcomm.map L)
    (orderOf_pos v).ne' hvpow hvunit ζ hζ
  rw [show σ.permMatrix R = L t from hmatrix t, ← map_mul, htv] at hz
  rw [LinearMap.trace_eq_matrix_trace R b]
  change Matrix.trace (LinearMap.toMatrix b b
    (LinearMap.mulLeft R (MonoidAlgebra.of R G g) * LinearMap.mulRight R e)) = 0
  rw [LinearMap.toMatrix_mul]
  exact hz

/-- Central idempotents over a split characteristic-zero local domain are supported
on the elements of order prime to the residue characteristic. -/
theorem coeff_eq_zero_of_prime_dvd_orderOf
    {R G : Type*} [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R]
    [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (hp : ¬ IsUnit (p : R))
    (hroots : ∀ n : ℕ, n ≠ 0 → ¬ p ∣ n → ∃ ζ : R, IsPrimitiveRoot ζ n)
    (e : MonoidAlgebra R G) (he : IsIdempotentElem e)
    (hc : e ∈ Set.center (MonoidAlgebra R G)) :
    ∀ g : G, p ∣ orderOf g → e.coeff g = 0 := by
  intro g hg
  have hz := trace_mulLeft_mulRight_eq_zero_of_prime_dvd_orderOf p hp hroots e he g⁻¹
    (by simpa using hg)
  rw [trace_mulLeft_comp_mulRight e hc, inv_inv] at hz
  exact (mul_eq_zero.mp hz).resolve_left (Nat.cast_ne_zero.mpr (Nat.card_pos.ne'))

end ModularBlock.CentralIdempotentSupport
