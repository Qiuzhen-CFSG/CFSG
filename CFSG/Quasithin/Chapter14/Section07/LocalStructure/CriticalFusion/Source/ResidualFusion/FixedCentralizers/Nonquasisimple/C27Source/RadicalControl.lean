module

public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RadicalControl
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Source.LocalClauses

/-!
# Radical-normalizer placement for D's original fixed component

The genuine C.2.3 input from the original fixed centralizer puts the
component normalizer of Rᵤ* in the image of H∩Lᵤ. When Rᵤ* acts internally,
this is the exact normalizer of Rᵤ*∩Lᵤ* required by the intrinsic classical
radical theorem; this same intersection is then nontrivial and radical.
The outer-action placement remains a separate source case.

Source: Aschbacher--Smith 14.7.68(2), pp.1071--1072, and C.2.7(3), pp.146--147.
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

theorem fixedComponent_C27_radical_normalizer_control
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    starImage Lu (d.fixedCore u) Lu ⊓
        normalizer (starImage Lu (d.fixedCore u) (d.fixedCore u) :
          Set (StarQuotient Lu (d.fixedCore u))) ≤
      starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u) := by
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  exact ChapterC.C27Source.star_radical_normalizer_control
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K)

theorem fixedComponent_C27_inner_radical_placement
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hinner : starImage Lu (d.fixedCore u) (d.fixedCore u) ≤
      starImage Lu (d.fixedCore u) Lu) :
    IsPRadical 2 ((starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu)) ∧
      normalizer ((starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
          (starImage Lu (d.fixedCore u) Lu) : Set (starImage Lu (d.fixedCore u) Lu)) ≤
        (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
          (starImage Lu (d.fixedCore u) Lu) := by
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  have hi := d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
    d.point_mem_U_commutator_K
  exact ⟨ChapterC.C27Source.star_intersection_radical_of_inner hi hinner,
    ChapterC.C27Source.star_intersection_normalizer_control_of_inner hi hinner⟩

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
