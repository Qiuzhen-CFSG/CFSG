module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RankOneSylow
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.ThompsonControl

/-!
# Original fixed-component Sylow and Borel geometry in the rank-one row

Retain the actual moved section, natural action mark, ratio and offender
clause supplied by the genuine B.5.1 rank-one row. The original Rᵤ is Sylow
in LᵤRᵤ, its Thompson image is a Sylow of Lᵤ*, and the original marked
intersection is its Borel normalizer. No kernel equality or Borel placement
is an input. Block reconstruction and the other rows remain separate.

Source: Aschbacher–Smith 14.7.68(2) and C.2.7(3)(a)(i), pp.1071–1072,146.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedComponent_C27_rankOne_geometry
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hCJ : starImage Lu (d.fixedCore u) Lu ≤ offenderSubgroup (starRepresentation Lu (d.fixedCore u)))
    (s : MovedSection
      ((starRepresentation Lu (d.fixedCore u)).comp (offenderSubgroup (starRepresentation Lu (d.fixedCore u))).subtype)
      ((starImage Lu (d.fixedCore u) Lu).subgroupOf (offenderSubgroup (starRepresentation Lu (d.fixedCore u)))))
    (k : BinaryField)
    (natural : ActionEquiv (s.action.comp
      ((starImage Lu (d.fixedCore u) Lu).subgroupOf (offenderSubgroup (starRepresentation Lu (d.fixedCore u)))).subtype)
      (linearNatural k 2))
    (hratio : quadraticRatio s.action = 1)
    (hoff : ∀ B, IsBestOffender s.action B →
      ∃ S : Sylow 2 ((starImage Lu (d.fixedCore u) Lu).subgroupOf
        (offenderSubgroup (starRepresentation Lu (d.fixedCore u)))),
        B = (S : Subgroup _).map ((starImage Lu (d.fixedCore u) Lu).subgroupOf
          (offenderSubgroup (starRepresentation Lu (d.fixedCore u)))).subtype) :
    Chapter1.IsSylowIn 2 (starImage Lu (d.fixedCore u) (elementaryAbelianMaxJ (d.fixedCore u)))
      (starImage Lu (d.fixedCore u) Lu) ∧
      IsRankOneBorel (starImage Lu (d.fixedCore u) Lu)
        (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) ∧
      Chapter1.IsSylowIn 2 (d.fixedCore u) (Lu ⊔ d.fixedCore u) := by
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  exact ChapterC.C27Source.rankOne_row_geometry
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K) hCJ s k natural hratio hoff

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
