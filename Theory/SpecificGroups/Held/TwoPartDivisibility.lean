module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer

/-!
# A certified lower bound for the Held two-part

The original four-word subgroup is a two-group. Its certified orbit of
length 512 and a nonidentity point stabilizer give order at least 1024.
Consequently its order, and hence the order of the actual Held carrier,
is divisible by 2¹⁰. No exact ambient order formula is used.

Source: the ATLAS HeG1-p2058B0 subgroup calculations, used in the
Aschbacher–Smith C.5.13 containing-model comparison, printed pp.162–163.
-/

public section
namespace Held
open Subgroup LocalPairs.SylowGeometry.Calculations

/-- The certified two-subgroup supplies the full required lower two-part. -/
theorem two_pow_ten_dvd_card : 2^10 ∣ Nat.card He := by
  obtain ⟨k, hk⟩ := representative_isPGroup.exists_card_eq
  have hge : 2^10 ≤ 2^k := by
    rw [← hk]
    exact InnerNormalizer.representative_card_ge_of_orbit_labels
      InnerNormalizer.orbitSizeLabel_eq_card_orbit
  have hle : 10 ≤ k := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hge
  exact ((pow_dvd_pow 2 hle).trans (hk.symm.dvd)).trans
    representative.card_subgroup_dvd_card

end Held
