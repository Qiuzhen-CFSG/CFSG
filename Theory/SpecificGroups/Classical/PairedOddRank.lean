module
public import Theory.SpecificGroups.Classical.ThreeCoverLocalRanks
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Odd rank witnesses for paired classical components

Two diagonal torus coordinates supply rank two in PSL₃ away from the cubic
scalar kernel.  The norm-one frame torus gives the same witness in PSU₃.
The existing diagonal/cycle cubic witnesses cover the remaining binary
parities.  Thus every binary PSU₃ and every PSL₃ with field degree greater
than one has odd rank at least two.  The embedded binary derived symplectic
group supplies the PSp₄ witness, including the separate actual derived
PSp₄(2) carrier.

Source application: Aschbacher–Smith E.2.2 and E.2.7, printed pp.215–218.
A pair of commuting disjoint conjugate components forces each factor to
have odd rank at most one; these concrete witnesses eliminate these rows.
-/

public section
open Subgroup Matrix Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Theory.SpecificGroups.Classical.PairedOddRank
variable {F : Type*} [Field F] [Finite F]

/-- The two split torus coordinates give prime rank at least two. -/
theorem linear_special_of_dvd {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card F - 1) :
    2 ≤ primeRank p SL(3,F) := by
  let : Fact p.Prime := ⟨hp⟩
  have h1 : 1 ≤ primeRank p Fˣ := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hz
    exact (PrimeRank.eq_zero_iff_not_dvd_card.mp hz) (by rwa [Nat.card_units])
  have hr : 2 ≤ primeRank p (Fˣ × Fˣ) := by
    rw [primeRank_prod_eq_add]
    omega
  exact hr.trans (Theory.GroupTheory.primeRank_le_of_injective p (PSL3.CartanActions.torusSL F)
    (PSL3.CartanActions.BorelQuotient.torusSL_injective F))

/-- The split witness survives the projective quotient away from three. -/
theorem linear_projective_of_dvd {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3)
    (hd : p ∣ Nat.card F - 1) : 2 ≤ primeRank p PSL(3,F) := by
  let : Fact p.Prime := ⟨hp⟩
  apply (linear_special_of_dvd hp hd).trans
  apply _root_.primeRank_le_of_coprime_ker p (PSL3.projection F)
  rw [PSL3.card_projectionKernel]
  exact (hp.coprime_iff_not_dvd.mpr (fun h => h3
    ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h))).of_dvd_right (Nat.gcd_dvd_left _ _)

/-- The norm-one torus witness survives projectivization away from three. -/
theorem unitary_projective_of_dvd (J : HermitianForm 3 F) {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (h3 : p ≠ 3) (hd : p ∣ 2^n+1)
    (hc : Nat.card F = (2^n)^2) (hconj : ∀x, J.conj x = x^(2^n)) :
    2 ≤ primeRank p (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  apply (ThreeCoverLocalRanks.binary_unitary_special_primeRank_ge_two J hn hp hd hc hconj).trans
  apply _root_.primeRank_le_of_coprime_ker p J.specialToProjective
  have hP : IsPGroup 3 J.specialToProjective.ker := fun x => ⟨1, by
    simpa using J.specialToProjective_ker_cube x⟩
  obtain ⟨k,hk⟩ := hP.exists_card_eq
  rw [hk]
  exact (hp.coprime_iff_not_dvd.mpr (fun h => h3
    ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h))).pow_right k

/-- Every binary PSL₃ over more than two elements has odd rank at least two. -/
theorem linear_binary_exists {n : ℕ} (hn : 1<n) (hc : Nat.card F = 2^n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 2 ≤ primeRank p PSL(3,F) := by
  by_cases he : Even n
  · exact ⟨3,by decide,by decide,SignedThreeCubicRank.linear_projective hc he⟩
  have ho : Odd (2^n-1) := Nat.odd_iff.mpr (by
    have hh : Even (2^n) := (even_two).pow_of_ne_zero (by omega : n≠0)
    have hh' := Nat.even_iff.mp hh
    have hpos : 0 < 2^n := pow_pos (by decide) _
    omega)
  have hgt : 1<2^n-1 := by
    have hh := Nat.pow_lt_pow_right (a:=2) (by decide) hn
    norm_num at hh
    omega
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : 2^n-1 ≠ 1)
  have hpodd : Odd p := Odd.of_dvd_nat ho hd
  have h3 : p ≠ 3 := by
    intro h
    subst p
    exact he ((Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mp hd)
  exact ⟨p,hp,hpodd,linear_projective_of_dvd hp h3 (hc ▸ hd)⟩

/-- Every positive binary PSU₃ parameter has odd rank at least two. -/
theorem unitary_binary_exists (J : HermitianForm 3 F) {n : ℕ}
    (hn : 0<n) (hc : Nat.card F = (2^n)^2) (hconj : ∀x, J.conj x = x^(2^n)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 2 ≤ primeRank p (ProjectiveSpecialUnitaryMatrixGroup J) := by
  by_cases ho : Odd n
  · exact ⟨3,by decide,by decide,SignedThreeCubicRank.unitary_projective J hn hc hconj ho⟩
  have he : Even n := Nat.not_odd_iff_even.mp ho
  have hodd : Odd (2^n+1) := (even_two.pow_of_ne_zero (by omega : n≠0)).add_odd odd_one
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by have := pow_pos (by decide : 0<2) n; omega : 2^n+1 ≠ 1)
  have hpodd : Odd p := Odd.of_dvd_nat hodd hd
  have h3 : p ≠ 3 := by
    intro h
    subst p
    have hh := (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr he
    have hpos : 0 < 2^n := pow_pos (by decide) _
    have h1 := Nat.mod_eq_zero_of_dvd hh
    have h2 := Nat.mod_eq_zero_of_dvd hd
    omega
  exact ⟨p,hp,hpodd,unitary_projective_of_dvd J hn hp h3 hd hc hconj⟩
end Theory.SpecificGroups.Classical.PairedOddRank

namespace Theory.SpecificGroups.Classical.PairedOddRank
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.Binary
open Theory.SpecificGroups.SymplecticFour.EvenProjective

/-- The binary derived symplectic witness embeds into the full projective group. -/
theorem psp_binary_three_rank {F : Type*} [Field F] [Finite F] {f : ℕ}
    (hcard : Nat.card F = 2^f) :
    2 ≤ primeRank 3 (Sp F ⧸ center (Sp F)) := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hcard
  have hr : 2 ≤ primeRank 3 (commutator (Sp F)) :=
    BinaryDerivedCubicRank.symplectic
  rw [← primeRank_equiv 3 (EvenProjective.equiv (F := F))]
  exact hr.trans (primeRank_subgroup_le 3 (commutator (Sp F)))

/-- The actual commutator of PSp₄(2) contains two independent three-cycles. -/
theorem derived_psp_binary_three_rank :
    2 ≤ primeRank 3 (commutator (Sp (ZMod 2) ⧸ center (Sp (ZMod 2)))) := by
  rw [primeRank_equiv 3
    SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix]
  exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by norm_num)
end Theory.SpecificGroups.Classical.PairedOddRank
