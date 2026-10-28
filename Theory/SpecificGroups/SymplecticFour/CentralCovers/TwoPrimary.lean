module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.PositiveRoots
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.Transfer
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.FieldFour.Relations
public import Theory.SpecificGroups.SymplecticFour.CentralRootLifts

/-!
# The two-primary symplectic kernel: local-to-global assembly

A section over the concrete unipotent subgroup excludes two from the order
of any finite perfect central-cover kernel: that subgroup has odd index,
and central transfer applies. Compatible lifts of its four positive roots
construct the required section by the proved coordinate multiplication law.

The final theorem below applies this calculation to the literal universal
projection, with no extra lift or relation premise. The rank-two construction
in `FieldFour.Relations` works uniformly for every field of order greater
than two, including order four: separating diagonal tori and the mixed-root
commutator give additive root sections, and torus equivariance eliminates
the crossing-relation defect. Thus it supplies all the required relations
throughout the requested range |F| > 3.

Source: Aschbacher–Smith I.1.3, printed p.407, citing GLS98 §6.1. This is
the defining-prime part of the whole-component Sp₄ identification used in
13.6.6, printed p.927. Odd-prime exclusion and final multiplier assembly
are separate from this module.
-/

public section

open PerfectCentralCovering

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Splitting over the standard matrix Sylow two-subgroup excludes two from
the kernel order. The section equation uses its literal inclusion in Sp₄. -/
theorem not_two_dvd_kernel_of_unipotent_section
    {E : Type*} [Group E] [Finite E] (f : Cover E (Sp F))
    (s : unipotent (F := F) →* E)
    (hs : f.toMonoidHom.comp s = (unipotent (F := F)).subtype) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  have hcard : Nat.card F = 2 ^ (n : ℕ) := by simpa using hn
  exact not_dvd_card_kernel_of_section f (unipotent (F := F))
    (two_not_dvd_index_unipotent hcard n.pos) s hs

/-- The complete positive-root relations suffice for the two-primary
exclusion for any finite perfect central cover of the actual matrix group. -/
theorem not_two_dvd_kernel_of_positive_root_lifts
    {E : Type*} [Group E] [Finite E] (f : Cover E (Sp F))
    (L : PositiveRootLifts f.toMonoidHom) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨s, hs⟩ := L.exists_unipotent_section
  exact not_two_dvd_kernel_of_unipotent_section f s hs

/-- Application to the exact universal kernel consumed by the I.1.3
symplectic multiplier assembly. The root-relation premise is still explicit. -/
theorem not_two_dvd_universal_kernel_of_positive_root_lifts
    (hF : 3 < Nat.card F)
    (L : PositiveRootLifts (universalProjection (Sp F))) :
    ¬ 2 ∣ Nat.card (universalProjection (Sp F)).ker := by
  let : Group.IsPerfect (Sp F) := CentralRootLifts.perfect (by omega)
  exact not_two_dvd_kernel_of_positive_root_lifts (universalCover (Sp F)) L

/-- Two does not divide the kernel order of the literal universal central
cover of Sp₄ over a finite characteristic-two field of order greater than
three. The rank-two root construction includes the field of order four. -/
theorem not_two_dvd_universal_kernel (hF : 3 < Nat.card F) :
    ¬ 2 ∣ Nat.card (universalProjection (Sp F)).ker := by
  let : Group.IsPerfect (Sp F) := CentralRootLifts.perfect (by omega)
  obtain ⟨L⟩ := FieldFour.exists_positive_root_lifts (by omega : 2 < Nat.card F)
    (universalProjection (Sp F)) (universalProjection_surjective (Sp F))
    (universalProjection_ker_le_center (Sp F))
  exact not_two_dvd_universal_kernel_of_positive_root_lifts hF L

end Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary

end
