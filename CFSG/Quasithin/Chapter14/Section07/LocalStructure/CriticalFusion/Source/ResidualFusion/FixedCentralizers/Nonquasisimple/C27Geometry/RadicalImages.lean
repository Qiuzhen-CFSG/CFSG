module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RadicalImages
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.ThompsonControl

/-!
# The original D radical in its faithful component image

The two-core of the normalizer of Rᵤ* ∩ Lᵤ* is that same intersection.
Thus the nontrivial branch is an actual radical subgroup of Lᵤ*, with no
quotient-image or normalizer hypothesis left for a model marking to supply.
The trivial intersection is retained for the separate outer-action branch.

Source: Aschbacher–Smith 14.7.68(2), applying C.2.7, pp.146–147,1071–1072.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedComponent_C27_intersection_core
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    (normalizer ((starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
      (starImage Lu (d.fixedCore u) Lu) : Set (starImage Lu (d.fixedCore u) Lu))).pCoreIn 2 =
      (starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf (starImage Lu (d.fixedCore u) Lu) := by
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  exact ChapterC.C27Source.star_intersection_normalizer_core_of_normal_input
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K)

theorem fixedComponent_C27_intersection_radical
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hne : (starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
      (starImage Lu (d.fixedCore u) Lu) ≠ ⊥) :
    IsPRadical 2 ((starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
      (starImage Lu (d.fixedCore u) Lu)) :=
  ⟨hne,d.fixedComponent_C27_intersection_core u h⟩

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
