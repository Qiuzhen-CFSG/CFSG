module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.FieldFour.Relations
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary

/-!
# Compatible positive-root lifts for Sp₄ over the field of four elements

Rank-two root geometry supplies additive, torus-equivariant sections and
all positive-root relations in the literal universal central cover. The
existing matrix-coordinate construction gives a section of the actual
unipotent subgroup. Its odd index and central transfer exclude two from
the universal-kernel order.

The geometric proof needs only |F| > 2, so its universal-cover construction
is also exported with that hypothesis. The field-four statements below
are the precise small-field input to the even symplectic multiplier assembly.

Source: Aschbacher–Smith I.1.3, printed p.407, citing GLS3 §6.1; the resulting
whole-component identification is used in 13.6.6, printed p.927. This proves
the two-primary input, without assuming the multiplier-table conclusion.
-/

public section

open PerfectCentralCovering

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.FieldFour

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Compatible positive-root lifts into the literal universal covering group.
The rank-two argument includes the field of four elements. -/
theorem universal_positive_root_lifts_of_card_gt_two (hF : 2 < Nat.card F) :
    Nonempty (PositiveRootLifts (universalProjection (Sp F))) := by
  let : Group.IsPerfect (Sp F) := CentralRootLifts.perfect hF
  exact exists_positive_root_lifts hF (universalProjection (Sp F))
    (universalProjection_surjective (Sp F)) (universalProjection_ker_le_center (Sp F))

/-- The field-four instance of the four additive root sections and all their
positive-root relations, for the exact universal projection. -/
theorem universal_positive_root_lifts (hF : Nat.card F = 4) :
    Nonempty (PositiveRootLifts (universalProjection (Sp F))) :=
  universal_positive_root_lifts_of_card_gt_two (by omega)

/-- A homomorphic section over the actual matrix Sylow two-subgroup. -/
theorem exists_universal_unipotent_section (hF : Nat.card F = 4) :
    ∃ s : unipotent (F := F) →* UniversalGroup (Sp F),
      (universalProjection (Sp F)).comp s = (unipotent (F := F)).subtype := by
  obtain ⟨L⟩ := universal_positive_root_lifts hF
  exact L.exists_unipotent_section

/-- The constructed field-four lifts discharge the transfer premise for the
literal universal kernel consumed by the multiplier assembly. -/
theorem not_two_dvd_universal_kernel (hF : Nat.card F = 4) :
    ¬ 2 ∣ Nat.card (universalProjection (Sp F)).ker := by
  obtain ⟨L⟩ := universal_positive_root_lifts hF
  exact not_two_dvd_universal_kernel_of_positive_root_lifts (by omega) L

end Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.FieldFour
