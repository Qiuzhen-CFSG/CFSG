module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary.Split
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary.Nonsplit
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary.Quartic
public import Theory.SpecificGroups.SymplecticFour.CentralRootLifts

/-!
# Odd-primary kernels of even symplectic four-space covers

Every finite perfect central cover of the actual matrix group Sp₄(F) in
characteristic two has kernel of order prime to every odd prime p.
For p dividing q−1, apply transfer to the full Borel preimage, whose
quotient by its two-core is abelian. For p dividing q+1, embed two
norm-one cyclic groups on the two hyperbolic planes. An independent
Frobenius inversion kills their lifted commutator, and transfer applies
again. Otherwise the Sylow order divides q²+1 and the faithful
four-dimensional representation makes that Sylow subgroup cyclic.

Specialize to the constructed universal perfect central projection using
root-torus perfectness. This supplies precisely the odd-primary premise
of `even_universalCover_of_prime_exclusions` in the Chapter I symplectic
multiplier assembly. It includes q=4 and uses no two-primary calculation.

Source: Aschbacher–Smith, I.1.2–I.1.3, printed p.407 (PDF p.418),
citing GLS98 §6.1. The omission of Sp₄(2ⁿ) from the multiplier table is
not used as a proof input.
-/

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary

open Subgroup PerfectCentralCovering
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- No odd prime divides the kernel of a finite perfect central cover of Sp₄(F). -/
public theorem not_dvd_card_kernel
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (f : E →* Sp F) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬ p ∣ Nat.card f.ker := by
  by_cases hd : p ∣ (Nat.card F)^2 - 1
  · have hfactor : (Nat.card F)^2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
    rw [hfactor] at hd
    rcases (Fact.out : p.Prime).dvd_mul.mp hd with hd | hd
    · exact not_dvd_card_kernel_of_dvd_sub_one hp2 hd f hf hk
    · exact not_dvd_card_kernel_of_dvd_add_one hp2 hd f hf hk
  · exact not_dvd_card_kernel_of_not_dvd_sq_sub_one hp2 hd f hf hk

/-- The odd-primary exclusion for the literal universal projection, including F₄. -/
public theorem not_dvd_card_universal_kernel (hF : 3 < Nat.card F)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (universalProjection (Sp F)).ker := by
  let : Group.IsPerfect (Sp F) := CentralRootLifts.perfect (by omega)
  let : Fact p.Prime := ⟨hp⟩
  exact not_dvd_card_kernel hp2 (universalProjection (Sp F))
    (universalProjection_surjective (Sp F)) (universalProjection_ker_le_center (Sp F))

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary
