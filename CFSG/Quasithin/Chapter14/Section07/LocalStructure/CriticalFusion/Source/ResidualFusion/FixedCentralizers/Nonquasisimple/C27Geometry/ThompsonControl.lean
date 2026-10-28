module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.ThompsonControl
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Source.LocalClauses

/-!
# The marked normalizer restriction for the original fixed component

Apply C.2.7's displayed (*) to the original relatively normal component Lᵤ
and radical Rᵤ inside Gᵤ. Every image uses the original star quotient. This
supplies the geometric starting inequality in 14.7.68; the eight marked
alternatives remain separate mathematical obligations.

Source: Aschbacher–Smith 14.7.68(2), pp.1071–1072, and C.2.7, p.146.
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

theorem fixedComponent_C27_thompson_control
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    starImage Lu (d.fixedCore u) Lu ⊓ normalizer
        (starImage Lu (d.fixedCore u) (Stellmacher.elementaryAbelianMaxJ (d.fixedCore u)) :
          Set (StarQuotient Lu (d.fixedCore u))) ≤
      starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u) ∧
      starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u) <
        starImage Lu (d.fixedCore u) Lu := by
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  exact ChapterC.C27Source.star_thompson_intersection_of_normal_input
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K)

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
