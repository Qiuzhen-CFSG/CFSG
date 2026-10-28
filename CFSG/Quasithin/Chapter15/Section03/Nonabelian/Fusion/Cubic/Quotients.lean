module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.Coset
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.Lifting

/-!
# The two source quotient maps for cubic centralizers

The first quotient is `H/Z`, with relative normality proved from `H = C_G(Z)`.
The second map lands in the distinct actor quotient `H/O₂(H)` and has a
proved two-group kernel. The source equality `U = O₂(H)` identifies its
fiber with the actual `U/Z`, without imposing ambient normality on `Z`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.59(1) and the proof of 15.3.61(1), printed p.1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic
variable {G : Type*} [Group G]

/-- `Z` is central in its actual centralizer. -/
theorem denominator_le_center_H (Z : Subgroup G) :
    Z.subgroupOf (centralizerH Z) ≤ center (centralizerH Z) := by
  intro z hz
  apply mem_center_iff.mpr
  intro h
  apply Subtype.ext
  exact (mem_centralizer_iff.mp h.property z hz).symm

/-- The denominator of `H/Z` is normal only in `H`. -/
theorem denominator_normal_H (Z : Subgroup G) :
    (Z.subgroupOf (centralizerH Z)).Normal :=
  by
    constructor
    intro z hz h
    rw [mem_center_iff.mp (denominator_le_center_H Z hz) h, mul_inv_cancel_right]
    exact hz

attribute [local instance] denominator_normal_H

abbrev CentralQuotient (Z : Subgroup G) :=
  centralizerH Z ⧸ Z.subgroupOf (centralizerH Z)

noncomputable def centralProjection (Z : Subgroup G) : centralizerH Z →* CentralQuotient Z :=
  QuotientGroup.mk' _

noncomputable def actorProjection (Z : Subgroup G)
    (hZ : Z.subgroupOf (centralizerH Z) ≤ pCore 2 (centralizerH Z)) :
    CentralQuotient Z →* ActorQuotient Z :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by simpa only [comap_id] using hZ)

@[simp] theorem actorProjection_mk (Z : Subgroup G)
    (hZ : Z.subgroupOf (centralizerH Z) ≤ pCore 2 (centralizerH Z))
    (h : centralizerH Z) :
    actorProjection Z hZ (centralProjection Z h) = QuotientGroup.mk' _ h := rfl

theorem actorProjection_surjective (Z : Subgroup G)
    (hZ : Z.subgroupOf (centralizerH Z) ≤ pCore 2 (centralizerH Z)) :
    Function.Surjective (actorProjection Z hZ) := by
  intro a
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (centralizerH Z)) a
  exact ⟨centralProjection Z h, rfl⟩

theorem actorProjection_kernel_two (Z : Subgroup G)
    (hZ : Z.subgroupOf (centralizerH Z) ≤ pCore 2 (centralizerH Z)) :
    IsPGroup 2 (actorProjection Z hZ).ker := by
  rw [actorProjection, QuotientGroup.ker_map, comap_id]
  exact (pCore_isPGroup (p := 2) (G := centralizerH Z)).map _

theorem closure_subgroupOf_H_eq_core (Z ZS : Subgroup G)
    (hU : closureU Z ZS = coreQ Z) :
    (closureU Z ZS).subgroupOf (centralizerH Z) = pCore 2 (centralizerH Z) := by
  rw [hU]
  exact comap_map_eq_self_of_injective (centralizerH Z).subtype_injective _

theorem denominator_le_core (Z ZS : Subgroup G)
    (hZZS : Z ≤ ZS) (hU : closureU Z ZS = coreQ Z) :
    Z.subgroupOf (centralizerH Z) ≤ pCore 2 (centralizerH Z) := by
  rw [← closure_subgroupOf_H_eq_core Z ZS hU]
  exact fun _ hz => ZS_le_closureU Z ZS (hZZS hz)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic
