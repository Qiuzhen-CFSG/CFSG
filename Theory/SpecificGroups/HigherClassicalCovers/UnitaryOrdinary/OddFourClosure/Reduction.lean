module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.Basic
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.Perfectness
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.Universality
public import Theory.GroupTheory.PerfectCentralCoverPrimeReduction

/-!
# Prime-degree reductions for central closure of SU₄(q)

Compose a perfect central cover of the actual special unitary group with
its literal projective map. Perfectness makes the preimage of the scalar
center central, so this is a perfect central cover of the actual PSU₄.
In the Mersenne range its kernel has exactly four times the original order.
Consequently the independent nondefining-prime exclusion for PSU₄ excludes
those primes from every SU₄ covering kernel as well.

Quotienting a finite central kernel isolates any prime divisor as a kernel
of that prime order. Thus only covers of SU₄ with kernel of order q or two
remain. This file supplies the reduction and the literal-map application;
it does not assert either of those two local calculations.

Source: Aschbacher--Smith I.1.1 and I.1.4(3), printed pp.407--408, and
GLS3 §6.1, the canonical C₄ multiplier and absence of an exceptional part
for unitary degree four at Mersenne primes greater than three.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure

universe u
variable {F : Type u} [Field F] [Finite F]

/-- The permitted independent hypothesis concerns the actual projective group,
and every finite perfect central cover in the coefficient-field universe. -/
def NondefiningKernelExclusion (J : HermitianForm 4 F) (q : ℕ) : Prop :=
  ∀ (M : Type u) [Group M] [Finite M]
    (g : PerfectCentralCovering.Cover M (ProjectiveSpecialUnitaryMatrixGroup J))
    (r : ℕ), r.Prime → r ≠ 2 → r ≠ q → ¬ r ∣ Nat.card g.toMonoidHom.ker

/-- A local calculation must rule out covers of this exact prime degree.
This is an explicit intermediate contract, not an established source result. -/
def NoPrimeKernel (J : HermitianForm 4 F) (p : ℕ) : Prop :=
  ∀ (E : Type u) [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E J.specialSubgroup),
    Nat.card f.toMonoidHom.ker ≠ p

variable (J : HermitianForm 4 F) [Group.IsPerfect J.specialSubgroup]

/-- The literal composite E → SU₄ → PSU₄ is again a perfect central cover. -/
def projectiveCover {E : Type u} [Group E]
    (f : PerfectCentralCovering.Cover E J.specialSubgroup) :
    PerfectCentralCovering.Cover E (ProjectiveSpecialUnitaryMatrixGroup J) where
  toMonoidHom := (naturalCentralCover J).toMonoidHom.comp f.toMonoidHom
  surjective := (naturalCentralCover J).surjective.comp f.surjective
  isPerfect := f.isPerfect
  ker_le_center := by
    intro x hx
    have hz : x ∈ (Subgroup.center J.specialSubgroup).comap f.toMonoidHom :=
      (naturalCentralCover J).ker_le_center hx
    rwa [f.comap_center] at hz

omit [Finite F] in
/-- The composed cover preserves precisely the canonical projective map. -/
theorem projectiveCover_toMonoidHom {E : Type u} [Group E]
    (f : PerfectCentralCovering.Cover E J.specialSubgroup) :
    (projectiveCover J f).toMonoidHom = (project J).comp f.toMonoidHom := rfl

/-- Kernel orders in the actual covering triangle, before specializing q. -/
theorem card_projectiveCover_kernel {E : Type u} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E J.specialSubgroup) :
    Nat.card (projectiveCover J f).toMonoidHom.ker =
      Nat.card f.toMonoidHom.ker * Nat.card (project J).ker :=
  kernel_card_eq_mul_of_surjective_factor
    (projectiveCover J f).toMonoidHom (project J) f.toMonoidHom
    (project_surjective J) f.surjective rfl

/-- The scalar C₄ kernel contributes exactly a factor four, not an upper bound
on the kernel of an arbitrary projective cover. -/
theorem card_projectiveCover_kernel_mersenne {q : ℕ}
    (hq : 3 < q) (hm : ∃ k : ℕ, q + 1 = 2 ^ k)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    {E : Type u} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E J.specialSubgroup) :
    Nat.card (projectiveCover J f).toMonoidHom.ker =
      Nat.card f.toMonoidHom.ker * 4 := by
  rw [card_projectiveCover_kernel, card_project_kernel J hconj hcard,
    gcd_four_mersenne hq hm]

/-- Apply the projective nondefining-prime theorem to the literal composite. -/
theorem not_dvd_card_kernel_of_nondefining {q r : ℕ}
    (hnondef : NondefiningKernelExclusion J q)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ≠ q)
    {E : Type u} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E J.specialSubgroup) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  intro hd
  apply hnondef E (projectiveCover J f) r hr hr2 hrq
  rw [card_projectiveCover_kernel]
  exact dvd_mul_of_dvd_left hd _

/-- Two independent prime-degree exclusions finish the arbitrary-kernel
calculation. Neither local exclusion is silently inferred from the scalar
kernel of the natural projection. -/
theorem injective_of_prime_kernel_exclusions {q : ℕ} (hp : q.Prime)
    (hnondef : NondefiningKernelExclusion J q)
    (hdef : NoPrimeKernel J q) (htwo : NoPrimeKernel J 2)
    {E : Type u} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E J.specialSubgroup) :
    Function.Injective f.toMonoidHom := by
  let : Fact q.Prime := ⟨hp⟩
  have hq := f.not_dvd_card_kernel_of_no_prime_kernel hdef
  have h2 := f.not_dvd_card_kernel_of_no_prime_kernel (p := 2) htwo
  apply f.toMonoidHom.ker_eq_bot_iff.mp
  apply Subgroup.eq_bot_of_card_eq
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro r hr hd
  by_cases hrq : r = q
  · exact hq (hrq ▸ hd)
  by_cases hr2 : r = 2
  · exact h2 (hr2 ▸ hd)
  exact not_dvd_card_kernel_of_nondefining J hnondef hr hr2 hrq f hd

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure
