module

public import Theory.SpecificGroups.HigherClassicalCovers.Linear.PrimaryBounds
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.CoprimeRootLifts
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.PrimaryReduction

/-!
# The two-primary linear covering bound from presentation faithfulness

Remove the defining-prime Sylow subgroup of a perfect central kernel and
retain the literal map to PSL₄. The quotient kernel is prime to the field
characteristic, so its elementary roots lift with the Steinberg relations.
If the elementary presentation is faithful in SL₄, this gives a surjection
from SL₄ onto that quotient cover. Its kernel order is consequently bounded
by the actual scalar kernel. The original two-part divides this quotient
kernel order, independently of any defining-prime torsion upstairs.

The canonical-kernel and primary-bound consumer applications below retain
presentation faithfulness explicitly. They are conditional reductions,
not the completed source rows of Aschbacher–Smith I.1.4(1),(3), printed
p.408. The missing input is Steinberg's finite-field presentation theorem,
§6, Theorem 9; the root lifting uses §7, Theorem 11, in
refs/KGroup/GLS3/Chapter2St1.tex. No nondefining-prime exclusion is needed
for this two-primary reduction.
-/

@[expose] public section

namespace Theory.SpecificGroups.HigherClassicalCovers.Linear

open Theory.GroupTheory PerfectCentralCovering
open Theory.SpecificGroups.LinearHigher
open scoped MatrixGroups

universe u v w
variable (F : Type u) [Field F] [Finite F]

/-- Faithfulness bounds the entire kernel when its order is prime to the
characteristic. The map from SL₄ commutes with the original projection. -/
theorem kernel_card_le_of_coprime_of_matrixMap_injective
    {p : ℕ} [CharP F p]
    (hinj : Function.Injective (matrixMap (n := 4) (F := F)))
    {E : Type v} [Group E] [Finite E] (c : PerfectCentralCovering.Cover E PSL(4, F))
    (hcop : (Nat.card c.toMonoidHom.ker).Coprime p) :
    Nat.card c.toMonoidHom.ker ≤ Nat.gcd 4 (Nat.card F - 1) := by
  let : Group.IsPerfect E := c.isPerfect
  obtain ⟨s, hs, hfac, _⟩ := CoprimeRootLifts.exists_covering_of_matrixMap_injective
    c.toMonoidHom c.surjective c.ker_le_center hcop (by decide : 2 ≤ 4) hinj
  have he := kernel_card_eq_mul_of_surjective_factor (projection F)
    c.toMonoidHom s c.surjective hs hfac
  rw [← card_projectionKernel]
  apply Nat.le_of_dvd Nat.card_pos
  rw [he]
  exact dvd_mul_left _ _

/-- Quotienting only the defining-prime part preserves the original
2-Sylow bound; no exclusion of defining-prime torsion is assumed. -/
theorem sylow_two_card_le_of_matrixMap_injective {p : ℕ}
    [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (hinj : Function.Injective (matrixMap (n := 4) (F := F)))
    {E : Type v} [Group E] [Finite E] (c : PerfectCentralCovering.Cover E PSL(4, F))
    (P : Sylow 2 c.toMonoidHom.ker) :
    Nat.card P ≤ Nat.gcd 4 (Nat.card F - 1) := by
  apply c.sylow_card_le_of_coprime_kernel_bound (Ne.symm hp2) (p := p) ?_ P
  intro H _ _ d hcop
  exact kernel_card_le_of_coprime_of_matrixMap_injective F hinj d hcop

/-- Application to the actual canonical universal kernel, at prime field
order. Faithfulness is the only presentation premise. -/
theorem universalKernel_sylow_two_card_le_of_matrixMap_injective {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p)
    (hinj : Function.Injective (matrixMap (n := 4) (F := F)))
    (P : Sylow 2 (UniversalKernel F)) :
    Nat.card P ≤ Nat.gcd 4 (Nat.card F - 1) := by
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime (by rwa [← Nat.card_eq_fintype_card])
  exact sylow_two_card_le_of_matrixMap_injective F hp2 hinj
    (universalCover PSL(4, F)) P

/-- The precise Fermat-prime canonical-kernel application, still conditional
on the finite-field presentation theorem. -/
theorem universalKernel_sylow_two_card_le_of_fermat_of_matrixMap_injective {p : ℕ}
    (hp : p.Prime) (hF : Nat.card F = p)
    (hfermat : ∃ m : ℕ, p = 2 ^ (2 ^ m) + 1)
    (hinj : Function.Injective (matrixMap (n := 4) (F := F)))
    (P : Sylow 2 (UniversalKernel F)) :
    Nat.card P ≤ Nat.gcd 4 (Nat.card F - 1) := by
  have hp2 : p ≠ 2 := by
    obtain ⟨m, rfl⟩ := hfermat
    have he : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
    have hpow : 2 ≤ 2 ^ (2 ^ m) := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) he
    omega
  exact universalKernel_sylow_two_card_le_of_matrixMap_injective F hp hp2 hF hinj P

/-- The actual primary-bound consumer. Presentation faithfulness supplies
its two-primary premise; the two independent odd exclusions remain explicit. -/
theorem projection_isUniversal_of_odd_exclusions_of_matrixMap_injective {p : ℕ}
    (hp : p.Prime) (hF : Nat.card F = p)
    (hfermat : ∃ m : ℕ, p = 2 ^ (2 ^ m) + 1)
    (hinj : Function.Injective (matrixMap (n := 4) (F := F)))
    (hnondef : NondefiningKernelExclusion F p)
    (hdef : ¬ p ∣ Nat.card (UniversalKernel F)) :
    Theory.GroupTheory.Covering.IsUniversal.{u, u, w} (projectionCovering F) :=
  projection_isUniversal_of_primary_bounds F hnondef hdef
    (universalKernel_sylow_two_card_le_of_fermat_of_matrixMap_injective F hp hF hfermat hinj)

end Theory.SpecificGroups.HigherClassicalCovers.Linear
