module
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideSetup

/-!
# Lifting the quotient involution coverage to two local fibers

An involution outside the normal closure maps to an involution in the
quotient. A quotient conjugator lifts to the actual local subgroup, leaving
an involution over `x` or `(xy)^7`. Thus classification in those two fibers
combines with quotient coverage to give coverage by the ten concrete words.
Both classification premises are explicit and remain to be certified.

The local generators are the literal ATLAS `J4G1-max1W1` words documented
in `Cardinality.Subgroup`; no splitting of the extension is assumed.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
@[expose] public section
namespace Janko4.Simplicity.Max1Fusion
open Cardinality
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localX localY
  localKernelSeed localKernel

/-- Lifting quotient conjugators reduces the outside branch to two fibers. -/
theorem outside_coverage_of_quotient_and_fibers
    (hquotient : ∀ w : LocalQuotient hA hB, orderOf w = 2 →
      ∃ g : LocalQuotient hA hB,
        QuotientGroup.mk' (localKernel hA hB) (localX hA hB) = g * w * g⁻¹ ∨
        QuotientGroup.mk' (localKernel hA hB) ((localX hA hB * localY hA hB)^7) =
          g * w * g⁻¹)
    (hfibers : ∀ w : max1Subgroup hA hB, orderOf w = 2 →
      (QuotientGroup.mk' (localKernel hA hB) w =
          QuotientGroup.mk' (localKernel hA hB) (localX hA hB) ∨
       QuotientGroup.mk' (localKernel hA hB) w =
          QuotientGroup.mk' (localKernel hA hB) ((localX hA hB * localY hA hB)^7)) →
      ∃ (i : Fin 10) (g : max1Subgroup hA hB),
        outsideRepresentative hA hB i = g * w * g⁻¹)
    (z : max1Subgroup hA hB) (hz : z ∉ localKernel hA hB) (ho : orderOf z = 2) :
    ∃ (i : Fin 10) (g : max1Subgroup hA hB),
      outsideRepresentative hA hB i = g * z * g⁻¹ := by
  let π := QuotientGroup.mk' (localKernel hA hB)
  have hq : orderOf (π z) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ← ho, pow_orderOf_eq_one, map_one]
    · exact fun h => hz ((QuotientGroup.eq_one_iff z).mp h)
  obtain ⟨q, hq⟩ := hquotient (π z) hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (localKernel hA hB) q
  have hg : orderOf (g * z * g⁻¹) = 2 :=
    (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z).trans ho
  have he : π (g * z * g⁻¹) = π (localX hA hB) ∨
      π (g * z * g⁻¹) = π ((localX hA hB * localY hA hB)^7) := by
    simpa only [map_mul, map_inv, eq_comm] using hq
  obtain ⟨i, k, hk⟩ := hfibers (g * z * g⁻¹) hg he
  exact ⟨i, k*g, by simpa only [mul_inv_rev, mul_assoc] using hk⟩

end Janko4.Simplicity.Max1Fusion
