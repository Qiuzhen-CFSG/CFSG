module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.Arithmetic
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve.Descent
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve.Placement

/-!
# Cyclic Sylow subgroups at twelfth-cyclotomic triality primes

For every positive binary exponent, the actual carrier contains the cyclic
torus of order q⁴−q²+1 constructed in `Descent`. Its index is prime to every
odd prime dividing that factor, so every corresponding Sylow subgroup is
cyclic, with arbitrary prime multiplicity. The repeated-prime specialization
is exactly the remaining `htwelve` input of `geometry_of_remaining_tori`.

Cyclic central transfer gives the kernel exclusion for every finite perfect
central cover, including the literal projection R → R/Z(R).
Source: GLS3 §6.1, Theorem 6.1.4, with the graph-field and central-quotient
conventions of §2.2. Final assembly with the other cyclotomic factors remains
in `CyclotomicTori`.
-/

public section

noncomputable section
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve
open PerfectCentralCovering PerfectCentralCovering.OddSylow

/-- Every Sylow subgroup at an odd prime dividing the twelfth factor is cyclic. -/
theorem isCyclic_sylow (n : ℕ) (hn : 0 < n) {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (h12 : p ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1)
    (Q : Sylow p (Standard.BinaryCarrier n hn)) : IsCyclic Q :=
  cyclic_sylow_of_embedding (AlgebraicClosure (ZMod 2)) n hn hp h12
    (embedding _ n hn) (embedding_injective _ n hn) Q

/-- The exact repeated-prime input of `CyclotomicTori.geometry_of_remaining_tori`. -/
theorem isCyclic_sylow_of_square_dvd (n : ℕ) (hn : 0 < n) (_hlarge : 1 < n)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hsq : p ^ 2 ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1) :
    ∀ Q : Sylow p (Standard.BinaryCarrier n hn), IsCyclic Q := by
  apply isCyclic_sylow n hn (by omega)
  exact dvd_trans (by exact ⟨p, by ring⟩ : p ∣ p ^ 2) hsq

/-- The constructed cyclic torus supplies the local geometry used by central transfer. -/
theorem geometry (n : ℕ) (hn : 0 < n) {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (h12 : p ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1) :
    Geometry p (Standard.BinaryCarrier n hn) := .cyclic (isCyclic_sylow n hn hp h12)

/-- Twelfth-factor primes are excluded from every finite perfect central kernel. -/
theorem not_dvd_card_kernel {E : Type*} [Group E] [Finite E]
    (n : ℕ) (hn : 0 < n) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (h12 : p ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1)
    (f : Cover E (Standard.BinaryCarrier n hn)) : ¬ p ∣ Nat.card f.toMonoidHom.ker :=
  (geometry n hn hp h12).not_dvd_card_kernel hp f

/-- The same exclusion for the literal quotient by a finite perfect group's own center. -/
theorem not_dvd_card_center {R : Type*} [Group R] [Finite R] [Group.IsPerfect R]
    (n : ℕ) (hn : 0 < n)
    (hmodel : Standard.IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (h12 : p ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1) :
    ¬ p ∣ Nat.card (Subgroup.center R) := by
  obtain ⟨e⟩ := (Standard.isTrialityGroupAt_binary_iff _ n hn).mp hmodel
  rw [← centralQuotientCover_ker e]
  exact not_dvd_card_kernel n hn hp h12 (centralQuotientCover e)

end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve
