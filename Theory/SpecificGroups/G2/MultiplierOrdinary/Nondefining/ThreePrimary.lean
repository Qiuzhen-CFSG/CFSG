module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddThreePrimary
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.ThreePrimary.ValuationOne
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.ThreePrimary.NonsplitTorus
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.ThreePrimary.NonsplitNormalizer

/-!
# Three-primary transfer for even-characteristic G₂

The split and nonsplit torus normalizers exclude three at every three-adic
valuation of q − 1 and q + 1. In the nonsplit case, the norm-one torus and
the rational Weyl elements use the same Lang conjugator. Adjoining the
order-three Weyl cycle to the torus's full three-primary subgroup produces
an actual Sylow subgroup, including the order-243 Sylow subgroup of G₂(8).

The swapping reflection makes the torus preimage in a central cover abelian;
the torus inverter fixes the cycle and inverts the derived subgroup of the
Sylow preimage. Central transfer therefore excludes three from the literal
canonical universal kernel. All local model premises are discharged below.
The earlier valuation-one and conditional interfaces are retained.

Source: Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408, and GLS III §6.1.
-/

public section
namespace Atlas.G2.MultiplierOrdinary.Nondefining.ThreePrimary
open PerfectCentralCovering
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem three_dvd_sub_one_or_add_one :
    3 ∣ Nat.card F - 1 ∨ 3 ∣ Nat.card F + 1 := by
  let := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  have hnot : ¬ 3 ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hn]
    exact fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  rw [Nat.dvd_iff_mod_eq_zero] at hnot ⊢
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

omit [CharP F 2] in
/-- The full split branch, including arbitrary three-powers in the torus. -/
theorem universal_not_three_dvd_kernel_of_split
    (hF : 4 < Nat.card F) (hd : 3 ∣ Nat.card F - 1) :
    ¬ 3 ∣ Nat.card (universalProjection (Model F)).ker :=
  OddThreePrimary.universal_not_three_dvd_kernel_of_split (by omega) hd

/-- The nonsplit branch when the three-part of the field order plus one is three. -/
theorem universal_not_three_dvd_kernel_of_nonsplit_valuation_one
    (hF : 4 < Nat.card F) (hd : 3 ∣ Nat.card F + 1)
    (hnine : ¬ 9 ∣ Nat.card F + 1) :
    ¬ 3 ∣ Nat.card (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact not_three_dvd_kernel_of_valuation_one (universalProjection (Model F))
    (universalProjection_surjective _) (universalProjection_ker_le_center _) hd hnine

/-- Every even-field case outside the higher nonsplit valuation. -/
theorem universal_not_three_dvd_kernel_of_not_nine_dvd
    (hF : 4 < Nat.card F) (hnine : ¬ 9 ∣ Nat.card F + 1) :
    ¬ 3 ∣ Nat.card (universalProjection (Model F)).ker := by
  rcases three_dvd_sub_one_or_add_one (F := F) with hd | hd
  · exact universal_not_three_dvd_kernel_of_split hF hd
  · exact universal_not_three_dvd_kernel_of_nonsplit_valuation_one hF hd hnine

/-- Reduction of the complete source range to actual nonsplit normalizers
when nine divides the field order plus one. The unconditional theorem below
discharges this geometric premise. -/
theorem universal_not_three_dvd_kernel_of_nonsplit_data
    (hF : 4 < Nat.card F)
    (hnonsplit : 9 ∣ Nat.card F + 1 → Nonempty (OddThreePrimary.LocalData F)) :
    ¬ 3 ∣ Nat.card (universalProjection (Model F)).ker := by
  by_cases hnine : 9 ∣ Nat.card F + 1
  · obtain ⟨D⟩ := hnonsplit hnine
    exact OddThreePrimary.universal_not_three_dvd_kernel_of_localData (by omega) D
  · exact universal_not_three_dvd_kernel_of_not_nine_dvd hF hnine

/-- The full nonsplit branch, including arbitrary three-powers in q + 1. -/
theorem universal_not_three_dvd_kernel_of_nonsplit
    (hF : 4 < Nat.card F) (hd : 3 ∣ Nat.card F + 1) :
    ¬ 3 ∣ Nat.card (universalProjection (Model F)).ker := by
  obtain ⟨D⟩ := exists_nonsplit_localData hd
  exact OddThreePrimary.universal_not_three_dvd_kernel_of_localData (by omega) D

/-- Three does not divide the canonical universal kernel of G₂ over any
finite field of characteristic two and order greater than four. This supplies
the three-primary exclusion for the ordinary even-field multiplier entry. -/
theorem universal_not_three_dvd_kernel (hF : 4 < Nat.card F) :
    ¬ 3 ∣ Nat.card (universalProjection (Model F)).ker :=
  universal_not_three_dvd_kernel_of_nonsplit_data hF
    (exists_nonsplit_localData_of_nine_dvd hF)

end Atlas.G2.MultiplierOrdinary.Nondefining.ThreePrimary
end
