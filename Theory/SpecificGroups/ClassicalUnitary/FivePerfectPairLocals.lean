module
public import Theory.SpecificGroups.ClassicalUnitary.FivePerfectLocals
public import Theory.GroupTheory.PerfectPairPrimeRank

/-!
# Perfect pairs in the actual PSU₅(4) two-locals

In the line parabolic, a perfect subgroup has odd rank at most one away
from five: its scalar character is trivial, and the SU₃ Levi has three-rank
one. The plane parabolic has odd rank at most one away from three by its
exact order. Burnside's two-prime theorem then excludes two copies of the
odd ranks of any nontrivial perfect group from either local subgroup.
The isotropic-subspace theorem and actual unitary conjugation give the
conclusion for every two-local, without a prescribed component prime set.

Source: Aschbacher--Smith 4.4.12 and F.1.12(7), printed pp.622,263--264.
-/

public section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.PerfectLocals
variable {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 5 F)

local instance : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := finite_projective J

private theorem line_primes {p : ℕ} (hp : p.Prime)
    (hd : p ∣ 2 ^ 20 * (3 ^ 2 * 5 ^ 2 * 13)) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 13 := by
  rcases hp.dvd_mul.mp hd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  rcases hp.dvd_mul.mp h with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
        (hp.dvd_of_dvd_pow h))))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)))

private theorem plane_primes {p : ℕ} (hp : p.Prime)
    (hd : p ∣ 2 ^ 20 * (3 ^ 2 * 5 * 17)) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 17 := by
  rcases hp.dvd_mul.mp hd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  rcases hp.dvd_mul.mp h with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)))

/-- Away from five, every perfect subgroup of the full line parabolic
has odd prime rank at most one. -/
theorem perfect_line_odd_rank_le_one_away_five
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (f : H →* lineParabolic J) (hf : Function.Injective f)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hne : p ≠ 5) : primeRank p H ≤ 1 := by
  by_cases h3 : p = 3
  · subst p
    exact perfect_line_threeRank_le_one J hcard hconj hJ f hf
  apply (primeRank_le_of_injective p f hf).trans
  apply primeRank_le_one_of_square_not_dvd
  rw [card_lineParabolic_four J hcard hconj hJ]
  intro hd
  have hp : p.Prime := Fact.out
  have hd' := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hd
  rcases line_primes hp hd' with rfl | he | he | rfl
  · norm_num at ho
  · exact h3 he
  · exact hne he
  · norm_num at hd

/-- Away from three, the full plane parabolic has odd prime rank at most one. -/
theorem plane_odd_rank_le_one_away_three
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hne : p ≠ 3) :
    primeRank p (planeParabolic J) ≤ 1 := by
  apply primeRank_le_one_of_square_not_dvd
  rw [card_planeParabolic_four J hcard hconj hJ]
  intro hd
  have hp : p.Prime := Fact.out
  have hd' := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hd
  rcases plane_primes hp hd' with rfl | he | rfl | rfl
  · norm_num at ho
  · exact hne he
  · norm_num at hd
  · norm_num at hd

/-- No perfect subgroup of an actual PSU₅(4) two-local carries both
copies of every odd rank of a nontrivial perfect finite group. -/
theorem no_perfect_doubled_odd_ranks_in_twoLocal
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (S : Type*) [Group S] [Finite S] [Nontrivial S] [Group.IsPerfect S]
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (f : H →* ProjectiveSpecialUnitaryMatrixGroup J) (hf : Function.Injective f)
    (hd : ∀ p : ℕ, p.Prime → Odd p → 2 * primeRank p S ≤ primeRank p H)
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hM : IsTwoLocal M) (hle : f.range ≤ M) : False := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := finite_projective J
  obtain ⟨W,hn,hi,_,hMW⟩ := IsotropicGeometry.projective_twoLocal_stabilizes_isotropic J hJ M hM
  obtain ⟨b,g,hg⟩ := IsotropicTransitivity.transitive J hcard hconj hJ W hn hi
  have he : parabolic J W = (if b then planeParabolic J else lineParabolic J).map
      (MulAut.conj (project J g)).toMonoidHom := by
    rw [hg, IsotropicGeometry.parabolic_map_action]
    cases b <;> rfl
  rw [he] at hMW
  let j := (MulAut.conj (project J g)⁻¹).toMonoidHom.comp f
  have hj : Function.Injective j := (MulAut.conj (project J g)⁻¹).injective.comp hf
  have hc : j.range ≤ (if b then planeParabolic J else lineParabolic J) := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy,he⟩ := hMW (hle ⟨x,rfl⟩)
    change (project J g)⁻¹ * f x * ((project J g)⁻¹)⁻¹ ∈ _
    rw [← he]
    simpa [MulAut.conj_apply, mul_assoc] using hy
  cases b
  · let k := j.codRestrict _ (fun x => hc ⟨x,rfl⟩)
    have hk : Function.Injective k := fun _ _ h => hj (congrArg Subtype.val h)
    apply Perfect.no_doubled_odd_ranks S H (q := 5) (by decide) hd
    intro p hp ho hne
    let : Fact p.Prime := ⟨hp⟩
    exact perfect_line_odd_rank_le_one_away_five J hcard hconj hJ k hk ho hne
  · let k := j.codRestrict _ (fun x => hc ⟨x,rfl⟩)
    have hk : Function.Injective k := fun _ _ h => hj (congrArg Subtype.val h)
    apply Perfect.no_doubled_odd_ranks S H Nat.prime_three hd
    intro p hp ho hne
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_le_of_injective p k hk).trans
      (plane_odd_rank_le_one_away_three J hcard hconj hJ ho hne)

end Theory.SpecificGroups.UnitaryFive.PerfectLocals
