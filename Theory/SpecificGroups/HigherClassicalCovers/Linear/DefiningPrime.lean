module

public import Theory.SpecificGroups.HigherClassicalCovers.Linear.PrimaryBounds
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime.LocalSection
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime.RootLiftsThree
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime.RootLiftsFermat

/-!
# Defining-prime reduction for the canonical degree-four linear cover

Positive-root collection and transfer supply the defining-prime kernel
exclusion from compatible elementary root lifts in covers of prime degree.
Here it is applied to the literal canonical universal projection and then
to the ordinary-cover assembly in `PrimaryBounds`.

The general transfer application retains its root-lifting premise. The
ternary and larger Fermat-prime branches below discharge it for the source
parameter in Aschbacher–Smith I.1.4(1),(3), printed pp.407–408 of
`refs/quasithin.pdf`. The other-prime and two-primary calculations retain
their independent owners.
-/

@[expose] public section

open scoped MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime

universe u v
variable {F : Type u} [Field F]

/-- Application to the canonical constructed universal projection. The root
relations remain an explicit premise; this is not yet the source exclusion. -/
theorem universalKernel_not_dvd_of_primeKernelRootLifts [Finite F] {p : ℕ}
    (hp : p.Prime) (hF : Nat.card F = p) (hlifts : PrimeKernelRootLifts F p) :
    ¬ p ∣ Nat.card (UniversalKernel F) :=
  not_dvd_kernel_of_primeKernelRootLifts hp hF hlifts
    (PerfectCentralCovering.universalCover PSL(4,F))

/-- The source parameter is a Fermat prime, so the two completed local
branches discharge the root-lifting premise without any presentation or
universal-property assumption. -/
theorem universalKernel_not_dvd_of_fermat [Finite F] {p : ℕ}
    (hp : p.Prime) (hF : Nat.card F = p)
    (hfermat : ∃ m : ℕ, p = 2 ^ (2 ^ m) + 1) :
    ¬ p ∣ Nat.card (UniversalKernel F) := by
  have hp_ge : 3 ≤ p := by
    obtain ⟨m, hm⟩ := hfermat
    rw [hm]
    have he : 2 ≤ 2 ^ (2 ^ m) := by
      have he' : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by decide)
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) he'
    omega
  by_cases hp3 : p = 3
  · have hF3 : Nat.card F = 3 := hF.trans hp3
    simpa [hp3] using
      (universalKernel_not_dvd_of_primeKernelRootLifts (p := 3)
        (by decide) hF3 (primeKernelRootLifts_three hF3))
  · have hpgt : 3 < p := by omega
    exact universalKernel_not_dvd_of_primeKernelRootLifts hp hF
      (primeKernelRootLifts_of_three_lt hF hpgt)

/-- The precise ordinary-cover consumer, retaining the independent
nondefining and two-primary inputs of `PrimaryBounds`. -/
theorem projection_isUniversal_of_rootLifts_and_two_bound [Finite F] {p : ℕ}
    (hp : p.Prime) (hF : Nat.card F = p) (hlifts : PrimeKernelRootLifts F p)
    (hnondef : NondefiningKernelExclusion F p)
    (htwo : ∀ P : Sylow 2 (UniversalKernel F),
      Nat.card P ≤ Nat.gcd 4 (Nat.card F - 1)) :
    Theory.GroupTheory.Covering.IsUniversal.{u,u,v} (projectionCovering F) :=
  projection_isUniversal_of_primary_bounds F hnondef
    (universalKernel_not_dvd_of_primeKernelRootLifts hp hF hlifts) htwo

end Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime
