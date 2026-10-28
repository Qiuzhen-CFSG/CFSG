module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction.Image
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.LinearThree.Placement
public import Theory.GroupTheory.PCoreActionCardKernel

/-!
# The two-group kernel of the original wreath action

The marked orbit image is SL₃(2)², of exactly the order of L₀/O₂(L₀).
Kernel--image counting therefore makes the kernel on L₀ a two-group.
Since L₀T/L₀ is also a two-group, the full kernel is a two-group.
This uses the original orbit and relative normality inside L₀T.

Source: Aschbacher--Smith 10.1.1(3), 10.2.4, pp.741,747.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}
  {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- The prescribed original action has a two-group kernel. -/
theorem LiftData.kernel_two (f : LiftData s hz) : IsPGroup 2 f.hom.ker := by
  let J := localJoin T L
  let R := (localOrbit T L).subgroupOf J
  let : R.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  have hgen : R ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show localOrbit T L ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hq : IsPGroup 2 (J ⧸ R) :=
    isPGroup_quotient_of_sup_eq_top R ((T : Subgroup G).subgroupOf J)
      T.isPGroup'.comap_subtype hgen
  apply f.hom.isPGroup_ker_of_card_image_eq_core_quotient R hq
  obtain ⟨e⟩ := CentralHall.LinearThree.quotient_equiv D s.quotient (survivor_nonnormal s)
  let c : R ≃* localOrbit T L := subgroupOfEquivOfLe le_sup_left
  let q := (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans e
  rw [show R.map f.hom = base.range from f.orbit_image,
    Nat.card_congr (MonoidHom.ofInjective base_injective).toEquiv.symm,
    Nat.card_congr q.toEquiv, Nat.card_fun, Nat.card_prod]
  have hbit : Nat.card Bit = 2 := by
    change Nat.card (ZMod 2) = 2
    exact Nat.card_zmod 2
  rw [hbit,pow_two]

/-- A lift alone suffices: its full image and two-group kernel have been proved. -/
def LiftData.actionData (f : LiftData s hz) : ActionData s hz where
  hom := f.hom
  onto := f.surjective
  kernel_two := f.kernel_two
  equivariant := f.equivariant

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction
