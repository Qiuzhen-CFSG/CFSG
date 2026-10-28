module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.IntrinsicParabolics
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.SylowAlignment
public import Theory.AtlasPort.LinearGroups.G2.HigherFieldResiduals
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.AtlasPort.LinearGroups.G2.DerivedParabolicGeneration
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance
/-!
# Both G2 source models have an intrinsic invariant parabolic pair

The standard Sylow subgroup intrinsically determines two root subgroups;
their normalizers are the two proper generating parabolics. This survives
restriction to the actual binary derived group. The intrinsic pair lift
therefore excludes an ambient minimal parabolic for either normal model.

Source: Aschbacher–Smith B.6.9, p.116, using the G2 parabolic geometry of
2.3.9(7), p.526. The original normal subgroup and Sylow are retained.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterB
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
/-- A normal full G2 supplement has two distinct proper Sylow overgroups. -/
theorem not_minimalParabolic_of_normal_g2
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal]
    (hgen : L ⊔ (T : Subgroup G) = ⊤) (e : L ≃* Model F) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  exact not_minimalParabolic_of_intrinsic_parabolics T L e hgen sylow parabolic₁ parabolic₂
    parabolics_generate HigherFieldResiduals.parabolic₁_isCoatom.ne_top
    HigherFieldResiduals.parabolic₂_isCoatom.ne_top
    (sylow_le_borel.trans borel_le_parabolic₁) (sylow_le_borel.trans borel_le_parabolic₂)
    LieAutomorphismExtensions.InnerFieldCoverage.parabolics_invariant_of_sylow
omit [Field F] [Finite F] [CharP F 2] in
/-- The actual binary derived G2 model has the same obstruction. -/
theorem not_minimalParabolic_of_normal_binary_g2_derived
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal]
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (e : L ≃* commutator (Model (ZMod 2))) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  let D := commutator (Model (ZMod 2))
  let P := (parabolic₁ (F := ZMod 2)).subgroupOf D
  let Q := (parabolic₂ (F := ZMod 2)).subgroupOf D
  have hjoin : P ⊔ Q = ⊤ := by
    apply map_injective D.subtype_injective
    rw [Subgroup.map_sup,subgroupOf_map_subtype,subgroupOf_map_subtype,
      ← MonoidHom.range_eq_map,range_subtype]
    exact DerivedParabolicGeneration.binary_restricted_pair_generate
  have hcD : Nat.card D = 6048 := DerivedEvenOrder.card_derived_binary (by simp)
  have hp : P ≠ ⊤ := by
    have hc : Nat.card P = 96 := by
      change Nat.card ((parabolic₁ (F:=ZMod 2)).subgroupOf D) = 96
      rw [parabolic₁_binary]
      exact BinaryParabolicPair.card_derivedFirst
    intro hh
    rw [hh,Nat.card_congr Subgroup.topEquiv.toEquiv,hcD] at hc
    norm_num at hc
  have hq : Q ≠ ⊤ := by
    have hc : Nat.card Q = 96 := BinaryParabolicPair.card_derivedSecond
    intro hh
    rw [hh,Nat.card_congr Subgroup.topEquiv.toEquiv,hcD] at hc
    norm_num at hc
  apply not_minimalParabolic_of_intrinsic_parabolics T L e hgen
    BinaryParabolicPair.derivedSylow P Q hjoin hp hq
  · change (BinaryParabolicPair.derivedSylow : Subgroup D) ≤
      (parabolic₁ (F:=ZMod 2)).subgroupOf D
    rw [parabolic₁_binary]
    exact BinaryParabolicPair.derivedSylow_le_first
  · exact BinaryParabolicPair.derivedSylow_le_second
  · intro a ha
    apply SylowParabolicInvariance.restricted_parabolics_invariant a
    rwa [BinaryParabolicPair.derivedSylow_eq] at ha
end CFSG.Quasithin.ChapterB
