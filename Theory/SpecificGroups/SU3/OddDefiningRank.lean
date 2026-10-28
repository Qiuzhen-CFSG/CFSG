module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.Roots
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Odd defining-characteristic rank in projective SU₃

For a quadratic field involution in odd characteristic, write
`a = x + conj x` and `b = x - conj x`. The root coordinate
`(a, b - a²/2)` is additive in `x` under the Hermitian root-group law
`(a,c)(a',c') = (a+a', c+c'-a*conj a')`. Here `a` is fixed by conjugation
and `b` has trace zero. Recovering `2*x` from these
coordinates proves injectivity, including in characteristic three.

The existing root injection into the literal PGL quotient and Hermitian
basis transport give an elementary abelian subgroup of order `|F|` for
any nondegenerate ternary Hermitian form. Thus `|F| = (p^e)^2` gives
ordinary defining-prime rank at least `2e`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.2.17, printed p.39 (PDF p.50); Hermitian coordinates and form transport
use Huppert II.10.4 and II.10.12.
-/

noncomputable section

public section

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddDefiningRank
variable {F : Type*} [Field F] (J : HermitianForm 3 F)

/-- An additive field parametrization of a commuting Hermitian root plane.
The quadratic correction compensates for the root multiplication term. -/
@[expose] def additiveCoordinates (h2 : (2 : F) ≠ 0) :
    Multiplicative F →* hermitianUnipotentCoord J where
  toFun x := ⟨(x.toAdd + J.conj x.toAdd,
    x.toAdd - J.conj x.toAdd - (x.toAdd + J.conj x.toAdd) ^ 2 / 2), by
      dsimp only
      simp only [map_sub, map_add, map_div₀, map_pow, map_ofNat]
      rw [J.conj_involutive]
      field_simp
      ring⟩
  map_one' := by
    apply Subtype.ext
    change (0 + J.conj 0, 0 - J.conj 0 - (0 + J.conj 0) ^ 2 / 2) = (0, 0)
    simp
  map_mul' x y := by
    apply Subtype.ext
    apply Prod.ext
    · change x.toAdd + y.toAdd + J.conj (x.toAdd + y.toAdd) =
        (x.toAdd + J.conj x.toAdd) + (y.toAdd + J.conj y.toAdd)
      rw [map_add]
      ring
    · change (x.toAdd + y.toAdd) - J.conj (x.toAdd + y.toAdd) -
          ((x.toAdd + y.toAdd) + J.conj (x.toAdd + y.toAdd)) ^ 2 / 2 =
        (x.toAdd - J.conj x.toAdd - (x.toAdd + J.conj x.toAdd) ^ 2 / 2) +
        (y.toAdd - J.conj y.toAdd - (y.toAdd + J.conj y.toAdd) ^ 2 / 2) -
        (x.toAdd + J.conj x.toAdd) * J.conj (y.toAdd + J.conj y.toAdd)
      simp only [map_add]
      rw [J.conj_involutive]
      field_simp
      ring

/-- Both corrected coordinates recover `2*x`, so the parametrization is faithful. -/
theorem additiveCoordinates_injective (h2 : (2 : F) ≠ 0) :
    Function.Injective (additiveCoordinates J h2) := by
  intro x y h
  have ha := congrArg (fun z : hermitianUnipotentCoord J => z.val.1) h
  have hb := congrArg (fun z : hermitianUnipotentCoord J => z.val.2) h
  change x.toAdd + J.conj x.toAdd = y.toAdd + J.conj y.toAdd at ha
  change x.toAdd - J.conj x.toAdd - (x.toAdd + J.conj x.toAdd) ^ 2 / 2 =
    y.toAdd - J.conj y.toAdd - (y.toAdd + J.conj y.toAdd) ^ 2 / 2 at hb
  rw [ha] at hb
  apply Multiplicative.toAdd.injective
  apply mul_left_cancel₀ h2
  linear_combination ha + hb

open OddPrimeSylow.NormalizedOuter.Coverage
open OddPrimeSylow.NormalizedOuter.FormTransport

/-- The additive root plane in the actual projective group of the standard form. -/
@[expose] def standardEmbedding
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (h2 : (2 : F) ≠ 0) :
    Multiplicative F →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (root J hJ).comp (additiveCoordinates J h2)

/-- Faithfulness survives the literal projection into PGL: a scalar identifying
upper unipotent matrices is one, by comparison of their diagonal entries. -/
theorem standardEmbedding_injective
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (h2 : (2 : F) ≠ 0) :
    Function.Injective (standardEmbedding J hJ h2) :=
  (root_injective J hJ).comp (additiveCoordinates_injective J h2)

/-- Hermitian basis transport embeds the additive coefficient field into the
projective group of an arbitrary ternary form. -/
theorem exists_additive_embedding [Finite F] (h2 : (2 : F) ≠ 0)
    (q : ℕ) (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    ∃ f : Multiplicative F →* ProjectiveSpecialUnitaryMatrixGroup J,
      Function.Injective f := by
  obtain ⟨e⟩ := exists_projectiveEquiv J q hcard hfixed
  exact ⟨e.symm.toMonoidHom.comp (standardEmbedding (standardForm J) rfl h2),
    e.symm.injective.comp (standardEmbedding_injective (standardForm J) rfl h2)⟩

/-- The transported root plane is elementary abelian and has order `q²`. -/
theorem exists_elementary_subgroup [Finite F] {p : ℕ} [CharP F p]
    (h2 : (2 : F) ≠ 0) (q : ℕ) (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    ∃ A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      IsElementaryAbelian p A ∧ Nat.card A = q ^ 2 := by
  obtain ⟨f, hf⟩ := exists_additive_embedding J h2 q hcard hfixed
  refine ⟨f.range, ?_, ?_⟩
  · refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨x, y, rfl⟩
    apply Subtype.ext
    change f y ^ p = 1
    rw [← map_pow]
    have hy : y ^ p = 1 := by
      change p • y.toAdd = 0
      simp [nsmul_eq_mul]
    rw [hy, map_one]
  · exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hcard

private instance [Finite F] : Finite (ProjGenLinGroup (Fin 3) F) :=
  Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective

/-- Ordinary defining-prime rank is at least twice the fixed-field exponent,
with the fixed field derived from the prescribed Frobenius involution. -/
theorem two_mul_fieldExponent_le_primeRank [Finite F] {p e : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (he : 0 < e) (hcard : Nat.card F = (p ^ e) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (p ^ e)) :
    2 * e ≤ primeRank p (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := e * 2) (by
    simpa only [← Nat.card_eq_fintype_card, pow_mul] using hcard)
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hdiv := (CharP.cast_eq_zero_iff F p 2).mp h
    have := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    have := (Fact.out : p.Prime).two_le
    omega
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj p e he hcard hconj
  obtain ⟨A, hA, hAcard⟩ := exists_elementary_subgroup J (p := p) h2 (p ^ e) hcard hfixed
  let : IsElementaryAbelian p A := hA
  let : CommGroup A := IsMulCommutative.instCommGroup
  apply primeRank_ge_of_elementary_embedding (A := A) ?_ ?_ A.subtype Subtype.val_injective
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p A)
  · rw [hAcard, ← pow_mul, Nat.mul_comm e 2]

end BenderSuzuki.MatrixGroups.HermitianForm.OddDefiningRank
