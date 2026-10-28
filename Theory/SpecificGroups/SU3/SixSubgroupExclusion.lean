module

public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.SpecificGroups.Alternating.SixSubgroupObstructions

/-!
# No alternating-six subgroup in binary projective unitary groups

In the actual Hermitian root coordinates, squaring sends (a,b) to
(0,a·conj(a)). Thus every involution has first coordinate zero, and any
two involutions in the root Sylow subgroup commute. The explicit
noncommuting involutions in an A₆ two-subgroup exclude a faithful embedding.
An actual projective equivalence transports the argument to every
nondegenerate Gram matrix, retaining the stored field involution and its
fixed-field order 2ⁿ.

Source: Huppert II.10.4 and II.10.12; the Bender branch in
Aschbacher–Smith, Theorem C, printed p.33, and E.6.23, p.254.
-/

public section

open BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank
open OddPrimeSylow.NormalizedOuter.Coverage
open OddPrimeSylow.NormalizedOuter.FormTransport
variable {E : Type*} [Field E] [Finite E]

omit [Finite E] in
private theorem coordinates_commute [CharP E 2] (J : HermitianForm 3 E)
    (a b : hermitianUnipotentCoord J) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    Commute a b := by
  have first_zero (z : hermitianUnipotentCoord J) (hz : z ^ 2 = 1) : z.val.1 = 0 := by
    have h := congrArg (fun w : hermitianUnipotentCoord J => w.val.2) hz
    rw [EvenInner.square_coordinates] at h
    change z.val.1 * J.conj z.val.1 = 0 at h
    exact (mul_eq_zero.mp h).elim id ((map_eq_zero J.conj).mp)
  have hza := first_zero a ha
  have hzb := first_zero b hb
  apply Subtype.ext
  apply Prod.ext
  · exact add_comm _ _
  · change a.val.2 + b.val.2 - a.val.1 * J.conj b.val.1 =
      b.val.2 + a.val.2 - b.val.1 * J.conj a.val.1
    simp [hza, hzb, add_comm]

/-- Every pair of involutions in the actual binary unitary root Sylow commutes. -/
theorem rootSylow_involutions_commute (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (a b : rootSylow J hJ hn hcard hfixed)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) : Commute a b := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  let e0 : hermitianUnipotentCoord J ≃* rootGroup J hJ :=
    MulEquiv.ofBijective (root J hJ).rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr (root_injective J hJ),
        (root J hJ).rangeRestrict_surjective⟩
  let e : hermitianUnipotentCoord J ≃* rootSylow J hJ hn hcard hfixed :=
    e0.trans (MulEquiv.subgroupCongr (rootSylow_coe J hJ hn hcard hfixed).symm)
  have h := coordinates_commute J (e.symm a) (e.symm b)
    (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one])
  change a * b = b * a
  apply e.symm.injective
  simpa only [map_mul] using h.eq

/-- A₆ has no faithful embedding in binary PSU₃, for every actual Hermitian form. -/
theorem not_injective_alternating_six (J : HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (f : alternatingGroup (Fin 6) →* ProjectiveSpecialUnitaryMatrixGroup J) :
    ¬ Function.Injective f := by
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  obtain ⟨e⟩ := exists_projectiveEquiv J (2 ^ n) hcard hfixed
  let K := standardForm J
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup K) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  intro hf
  exact alternatingGroup.SixSubgroupObstructions.not_injective_of_sylow_involutions_commute
    (rootSylow K rfl hn hcard hfixed)
    (rootSylow_involutions_commute K rfl hn hcard hfixed)
    (e.toMonoidHom.comp f) (e.injective.comp hf)
end BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank
