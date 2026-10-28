module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.Perfect

/-!
# An actual central subgroup of order three in the Held cover candidate

The word `(x⁻¹*y⁻¹)²` in the checked perfect pair equals `(a * bray)⁷`.
It has order three, centralizes the candidate, and fixes ATLAS letter 31.
Centrality then makes it fix that letter's entire orbit. Consequently its
cyclic subgroup is a central subgroup of order three in the actual orbit
kernel. Only the reverse kernel containment remains a finite-certificate
obligation.

Source: the concrete ATLAS words for GLS3 Table 5.3p, outer 2C row.
-/

@[expose] public section
open Subgroup
namespace Held.OuterInvolution.FixedStructure

def centralGenerator : candidate := (firstGenerator⁻¹ * secondGenerator⁻¹) ^ 2

theorem centralGenerator_val : centralGenerator.val.val = (a * bray) ^ 7 :=
  center_word_eq.symm

theorem centralGenerator_pow : centralGenerator ^ 3 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change centralGenerator.val.val ^ 3 = 1
  rw [centralGenerator_val, ← pow_mul]
  exact a_bray_pow_twenty_one

theorem centralGenerator_ne_one : centralGenerator ≠ 1 := by
  intro h
  have hz : (a * bray) ^ 7 = 1 := by
    rw [← centralGenerator_val]
    exact congrArg (fun d : candidate => d.val.val) h
  apply a_not_commutes_center_word
  rw [hz]
  exact Commute.one_right a

theorem centralGenerator_order : orderOf centralGenerator = 3 :=
  orderOf_eq_prime centralGenerator_pow centralGenerator_ne_one

theorem centralGenerator_mem_center : centralGenerator ∈ center candidate := by
  rw [mem_center_iff]
  intro d
  apply Subtype.ext
  apply Subtype.ext
  change d.val.val * centralGenerator.val.val = centralGenerator.val.val * d.val.val
  rw [centralGenerator_val]
  have hc : d.val * (aFixed * brayFixed) ^ 7 = (aFixed * brayFixed) ^ 7 * d.val :=
    (mem_centralizer_singleton_iff (G := fixed)
      (g := (aFixed * brayFixed) ^ 7) (k := d.val)).mp
        (candidate_le_center_word_centralizer d.property)
  have he := congrArg fixed.subtype hc
  simpa only [map_mul, map_pow, Subgroup.subtype_apply, aFixed, brayFixed] using he

theorem centralGenerator_fixes_base : centralGenerator • (30 : Fin 2058) = 30 := by
  change representation centralGenerator.val.val 30 = 30
  rw [centralGenerator_val, map_pow, map_mul, bray_representation]
  decide +kernel

theorem centralGenerator_mem_orbitKernel : centralGenerator ∈ orbitKernel := by
  rw [mem_orbitKernel]
  intro x
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp x.property
  change centralGenerator • x.val = x.val
  rw [← hg, ← mul_smul]
  rw [← mem_center_iff.mp centralGenerator_mem_center g, mul_smul,
    centralGenerator_fixes_base]

theorem centralZpowers_le_center : zpowers centralGenerator ≤ center candidate :=
  zpowers_le.mpr centralGenerator_mem_center

theorem centralZpowers_le_orbitKernel : zpowers centralGenerator ≤ orbitKernel :=
  zpowers_le.mpr centralGenerator_mem_orbitKernel

theorem centralZpowers_card : Nat.card (zpowers centralGenerator) = 3 := by
  rw [Nat.card_zpowers, centralGenerator_order]

/-- The missing upper containment identifies the complete kernel. -/
theorem orbitKernel_eq_centralZpowers
    (h : orbitKernel ≤ zpowers centralGenerator) : orbitKernel = zpowers centralGenerator :=
  le_antisymm h centralZpowers_le_orbitKernel

end Held.OuterInvolution.FixedStructure
