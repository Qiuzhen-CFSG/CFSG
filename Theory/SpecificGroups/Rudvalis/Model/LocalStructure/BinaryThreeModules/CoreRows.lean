module
public import Theory.Representation.PSL3Two.NaturalDualNormalCore
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# Rudvalis rows excluded by a marked binary-three residual

The actual max4 core has centre of order eight, excluding a normal marked
natural-dual six-space. The actual max6 quotient is S₅ with its full two-core
kernel, and its certified order has no factor seven; hence it cannot contain
an injectively embedded group with the marked SL₃(2) two-core quotient.
These are local-row exclusions, without a Sylow-placement or ambient
maximal-two-local coverage assumption.

Source: the Ru inspection in Aschbacher–Smith 4.4.3, printed pp.622–623;
GLS3 Table 5.3r. The existing generation and centre certificates are reused.
-/

public section
namespace Rudvalis.BinaryThreeModules
open Subgroup BinaryLinearThree.NaturalDual SylowOvergroups
variable {M S : Type*} [Group M] [Group S]

/-- Reuse the proved centre calculation on the full intrinsic max4 core. -/
theorem max4_core_center_card : Nat.card (center (pCore 2 max4)) = 8 :=
  (Nat.card_congr (centerCongr CoveringIncidence.intrinsicCoreEquiv).toEquiv).trans
    CoveringIncidence.max4Core_center_card

/-- A local with the marked six-space obstruction cannot be the literal max4 row. -/
theorem not_max4_of_core_center_large (h : 64 ≤ Nat.card (center (pCore 2 M))) :
    ¬ Nonempty (M ≃* max4) := by
  rintro ⟨e⟩
  rw [core_center_card_congr e,max4_core_center_card] at h
  omega

/-- The original quotient projection forces a factor seven in any containing local. -/
theorem seven_dvd_of_marked_residual (r : S →* M) (hr : Function.Injective r)
    (e : (S ⧸ pCore 2 S) ≃* BinaryLinearThree.Group) : 7 ∣ Nat.card M := by
  have hq := card_quotient_dvd_card (pCore 2 S)
  rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL] at hq
  exact (show 7 ∣ 168 by decide).trans (hq.trans (card_dvd_of_injective r hr))

/-- The max6 row cannot contain the actual marked binary-three residual. -/
theorem not_max6_of_marked_residual (r : S →* M) (hr : Function.Injective r)
    (e : (S ⧸ pCore 2 S) ≃* BinaryLinearThree.Group) :
    ¬ Nonempty (M ≃* max6) := by
  rintro ⟨a⟩
  have h := seven_dvd_of_marked_residual r hr e
  rw [Nat.card_congr a.toEquiv,max6_card] at h
  norm_num at h
end Rudvalis.BinaryThreeModules
