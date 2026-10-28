module

public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.RootGeneration
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.Roots
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankSylow
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Binary two-rank of the actual projective unitary group

For a ternary Hermitian form over a field of order `(2^n)^2`, the explicit
Hermitian root group is a Sylow two-subgroup.  Its first-coordinate kernel is
elementary abelian of order `2^n`; the square formula shows that every
involution lies in this kernel.  This proves the exact rank on the actual
projective carrier, after transporting an arbitrary form to the standard
antidiagonal form.

The automorphism estimate is treated in the `Automorphisms` descendant;
this module does not assume or assert automorphism coverage.

Source: Aschbacher–Smith 16.1.7(3b), printed p.1172, and the automorphism-rank
table on printed p.356.
-/

noncomputable section

public section

open scoped MatrixGroups commutatorElement
open Subgroup Theory.GroupTheory
open BenderSuzuki.External

namespace BenderSuzuki.MatrixGroups.HermitianForm

namespace EvenTwoRank
open OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
  {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)

private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

include hn hcard hfixed in
/-- The root image has odd index for every binary prime-power fixed field. -/
public theorem rootGroup_index_not_two_dvd : ¬ 2 ∣ (rootGroup J hJ).index := by
  let q := 2 ^ n
  have hq : 0 < q := by positivity
  have hqe : 2 ∣ q := dvd_pow_self 2 (by omega)
  obtain ⟨_, _, _, _, _, _, _, _, hGcard, _⟩ :=
    huppert_II_10_12 J q hcard hfixed hJ
  have hgcd : Nat.gcd 3 (q + 1) ∣ q ^ 2 - 1 := by
    have hf : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq q 1
    rw [hf]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 (q + 1)) _
  have hdiv : Nat.gcd 3 (q + 1) ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) :=
    dvd_mul_of_dvd_right hgcd _
  have hi := (rootGroup J hJ).card_mul_index
  rw [rootGroup_card J hJ q hcard hfixed] at hi
  have hprod : (rootGroup J hJ).index * Nat.gcd 3 (q + 1) =
      (q ^ 3 + 1) * (q ^ 2 - 1) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hq 3)
    calc
      q ^ 3 * ((rootGroup J hJ).index * Nat.gcd 3 (q + 1)) =
          Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) * Nat.gcd 3 (q + 1) := by
            rw [← mul_assoc, hi]
      _ = (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
        rw [hGcard, Nat.div_mul_cancel hdiv]
      _ = q ^ 3 * ((q ^ 3 + 1) * (q ^ 2 - 1)) := by ring
  intro hbad
  have hd : 2 ∣ (q ^ 3 + 1) * (q ^ 2 - 1) :=
    hprod ▸ dvd_mul_of_dvd_left hbad _
  rcases Nat.prime_two.dvd_mul.mp hd with h | h
  · exact Nat.prime_two.not_dvd_one
      ((Nat.dvd_add_iff_right (hqe.trans (dvd_pow_self q (by decide : 3 ≠ 0)))).mpr h)
  · have hsq : 1 ≤ q ^ 2 := one_le_pow₀ (by omega)
    have hp2 : 2 ∣ q ^ 2 := hqe.trans (dvd_pow_self q (by decide : 2 ≠ 0))
    rw [← Nat.sub_add_cancel hsq] at hp2
    exact Nat.prime_two.not_dvd_one ((Nat.dvd_add_iff_right h).mpr hp2)

/-- The actual upper Hermitian root image as a Sylow two-subgroup. -/
@[expose] public def rootSylow : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (IsPGroup.of_card (show Nat.card (rootGroup J hJ) = 2 ^ (n * 3) by
    rw [rootGroup_card J hJ (2 ^ n) hcard hfixed, pow_mul])).toSylow
    (rootGroup_index_not_two_dvd J hJ hn hcard hfixed)

@[simp] public theorem rootSylow_coe :
    (rootSylow J hJ hn hcard hfixed : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
      rootGroup J hJ := rfl

end EvenTwoRank

namespace EvenInner

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

private def coordFirst : hermitianUnipotentCoord J →* Multiplicative E where
  toFun z := Multiplicative.ofAdd z.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem coordFirst_surjective {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    Function.Surjective (coordFirst J) := by
  intro a
  obtain ⟨b, hb⟩ := huppert_II_10_4_trace_surjective J q hcard hfixed
    (-(a.toAdd * J.conj a.toAdd)) (by
      rw [map_neg, map_mul, J.conj_involutive, mul_comm])
  exact ⟨⟨(a.toAdd, b), by dsimp only; rw [hb]; ring⟩, rfl⟩

private theorem two_rank_coord [CharP E 2]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    primeRank 2 (hermitianUnipotentCoord J) = n := by
  let q := 2 ^ n
  have hq : 0 < q := by positivity
  have hcard' : Nat.card E = q ^ 2 := by simpa [q] using hcard
  have hfixed' : Nat.card {x : E // J.conj x = x} = q := by simpa [q] using hfixed
  let H := hermitianUnipotentCoord J
  let f := coordFirst J
  have hsurj : Function.Surjective f := coordFirst_surjective J hcard' hfixed'
  have hHcard : Nat.card H = q ^ 3 := by
    let er : H ≃* (OddPrimeSylow.NormalizedOuter.Coverage.rootGroup J hJ) :=
      MulEquiv.ofBijective (OddPrimeSylow.NormalizedOuter.Coverage.root J hJ).rangeRestrict
        ⟨MonoidHom.rangeRestrict_injective_iff.mpr
            (OddPrimeSylow.NormalizedOuter.Coverage.root_injective J hJ),
          (OddPrimeSylow.NormalizedOuter.Coverage.root J hJ).rangeRestrict_surjective⟩
    exact (Nat.card_congr er.toEquiv).trans
      (OddPrimeSylow.NormalizedOuter.Coverage.rootGroup_card J hJ q hcard' hfixed')
  have hker : Nat.card f.ker = q := by
    have hh := f.ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
      Subgroup.card_top] at hh
    simp only [Nat.card_congr Multiplicative.toAdd] at hh
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hq 2)
    calc
      Nat.card f.ker * q ^ 2 = Nat.card H := by simpa [H, hcard'] using hh
      _ = q ^ 3 := hHcard
      _ = q * q ^ 2 := by ring
  have hcomm : ∀ x y : f.ker, Commute (x : H) y := by
    intro x y
    rw [← commutatorElement_eq_one_iff_commute]
    rw [hermitianUnipotent_commutator]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hx := congrArg Multiplicative.toAdd x.property
      have hy := congrArg Multiplicative.toAdd y.property
      change x.val.val.1 = 0 at hx
      change y.val.val.1 = 0 at hy
      change y.val.val.1 * J.conj x.val.val.1 - x.val.val.1 * J.conj y.val.val.1 = 0
      rw [hx, hy]
      simp
  let : IsElementaryAbelian 2 f.ker :=
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (hcomm x y).eq⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        change ((x : H) ^ 2).val = (1 : H).val
        rw [EvenInner.square_coordinates]
        have hx := congrArg Multiplicative.toAdd x.property
        change x.val.val.1 = 0 at hx
        change (0, x.val.val.1 * J.conj x.val.val.1) = (0, 0)
        simp only [hx, zero_mul]) }
  have hpow (x : H) (hx : x ^ 2 = 1) : x ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    have hs := congrArg (fun z : H => z.val.2) hx
    rw [EvenInner.square_coordinates] at hs
    have hmul : x.val.1 * J.conj x.val.1 = 0 := by
      exact hs
    have hxfirst : x.val.1 = 0 := (mul_eq_zero.mp hmul).elim id
      ((map_eq_zero J.conj).mp)
    change Multiplicative.ofAdd x.val.1 = 1
    exact congrArg Multiplicative.ofAdd hxfirst
  apply le_antisymm
  · apply primeRank_le_of_pow_eq_one_subset f.ker
    · simpa [q] using hker.le
    · exact hpow
  · exact IsElementaryAbelian.primeRank_ge_of_card f.ker (by simpa [q] using hker)

end EvenInner

namespace EvenTwoRank

open OddPrimeSylow.NormalizedOuter.FormTransport

variable {E : Type*} [Field E] [Finite E]

/-- Exact two-rank for the standard antidiagonal ternary unitary model. -/
public theorem standard_two_rank (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    primeRank 2 (ProjectiveSpecialUnitaryMatrixGroup J) = n := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  rw [(rootSylow J hJ hn hcard hfixed).primeRank_eq]
  change primeRank 2 (OddPrimeSylow.NormalizedOuter.Coverage.rootGroup J hJ) = n
  let er := MonoidHom.ofInjective (OddPrimeSylow.NormalizedOuter.Coverage.root_injective J hJ)
  change primeRank 2 (OddPrimeSylow.NormalizedOuter.Coverage.root J hJ).range = n
  rw [← primeRank_equiv 2 er]
  exact EvenInner.two_rank_coord J hJ hcard hfixed

/-- Exact two-rank for an arbitrary genuine Hermitian form with the prescribed
stored Frobenius.  The equivalence is between the actual projective carriers. -/
public theorem two_rank
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) :
    primeRank 2 (ProjectiveSpecialUnitaryMatrixGroup J) = n := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  obtain ⟨e⟩ := exists_projectiveEquiv J (2 ^ n) (by simpa using hcard) hfixed
  rw [primeRank_equiv 2 e]
  exact standard_two_rank (standardForm J) rfl hn hcard hfixed

end EvenTwoRank

end BenderSuzuki.MatrixGroups.HermitianForm
