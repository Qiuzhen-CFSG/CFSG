module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceFour
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.AbelianSource
/-!
# Removing the abelian and distance-four branches in the literal SL₃ source

The actual natural center section becomes the existing intrinsic section
on the same selected component. Its original-module centralizer obstruction
excludes critical distance four. Together with the abelian MS source and the
proved even-distance reduction, every actual source setup has b>4.

No universal classification, exact dual quotient or greater-distance
conclusion is assumed. The remaining MS93 (4.4)–(4.5) geometry must close
this last branch in the final C.1.34/source assembly.

Source: Aschbacher–Smith C.1.34, pp.136–137 and 15.4.20, p.1164;
MS93 (4.6), pp.901–912.
-/

public section
open Subgroup CFSG.Quasithin.ChapterC
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry
universe u

private theorem double_gt_four (n : ℕ) (h2 : 2 < n+n) (hne : n+n ≠ 4) : 4 < n+n := by
  omega

noncomputable def coreCenterSectionOfNatural {A : Type*} [Group A]
    (m : BinaryMS.NaturalCenterSection A) : CoreCenterSection A 1 where
  quotientIso := m.marking
  layer := m.layer
  normal := m.normal
  center_le := m.center_le
  map := {
    toFun x := Multiplicative.ofAdd (fun _ => (m.projection x).toAdd)
    map_one' := by rw [map_one]; rfl
    map_mul' x y := by rw [map_mul]; rfl }
  intertwining l x := by
    funext i
    exact m.action l x
  kernel_central x hx := by
    apply m.kernel_central x
    exact congrArg Multiplicative.ofAdd (congrArg (fun y : Multiplicative (Fin 1 → Natural.Space) => y.toAdd 0) hx)

variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}
variable (h : Input d i j H U K) (s : Selected H U K K₁ r)
  {κ : GroupClass.{u}} {R : Subgroup H}
  (hMS : SourceCases.MSPair κ H (K₁.subgroupOf H) R)
  (e : ((K₁.subgroupOf H) ⧸ pCore 2 (K₁.subgroupOf H)) ≃* Natural.Actor)

include h s in
/-- The actual selected source excludes the whole nonabelian distance-four branch. -/
theorem not_source_ms_distance_four
    (s₀ : BinaryMS.MS93.InputSetup (hMS.binaryInput e))
    (hb : s₀.geometry.b s₀.reduction.radical = 4) : False := by
  have hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (K₁.subgroupOf H)) :=
    not_source_ms_abelian_core h s hMS e
  obtain ⟨m⟩ := s₀.naturalCenterSection_of_nonabelian_distance_four hc hb
  exact not_source_coreCenterSection h s (coreCenterSectionOfNatural m)

include h s in
/-- Both completed source branches are eliminated before the remaining b>4 argument. -/
theorem source_ms_distance_greater_four
    (s₀ : BinaryMS.MS93.InputSetup (hMS.binaryInput e)) :
    4 < s₀.geometry.b s₀.reduction.radical := by
  have hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (K₁.subgroupOf H)) :=
    not_source_ms_abelian_core h s hMS e
  obtain ⟨common⟩ := s₀.commonFacts hc
  have hlarge := common.large_distance
  have heven := s₀.geometry.even (BinaryMS.MS93.alpha s₀.reduction.radical) rfl
  change Even (s₀.geometry.b s₀.reduction.radical) at heven
  obtain ⟨n,hn⟩ := heven
  have hne := not_source_ms_distance_four h s hMS e s₀
  rw [hn] at hlarge hne ⊢
  exact double_gt_four n hlarge hne

include h s in
/-- Original input supplies the setup witnessing the sole remaining distance branch. -/
theorem exists_source_ms_distance_greater_four :
    ∃ s₀ : BinaryMS.MS93.InputSetup (hMS.binaryInput e),
      4 < s₀.geometry.b s₀.reduction.radical := by
  have hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (K₁.subgroupOf H)) :=
    not_source_ms_abelian_core h s hMS e
  obtain ⟨s₀⟩ := BinaryMS.MS93.exists_setup (hMS.binaryInput e) hc
  exact ⟨s₀,source_ms_distance_greater_four h s hMS e s₀⟩
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry
