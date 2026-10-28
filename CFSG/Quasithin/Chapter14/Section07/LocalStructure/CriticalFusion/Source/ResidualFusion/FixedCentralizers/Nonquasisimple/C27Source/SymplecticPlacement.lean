module

public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Source.LocalClauses

/-!
# The original D symplectic row has the required marked placement

For the actual fixed component Lᵤ and radical Rᵤ, the source B.5 conclusion
and the large symplectic model put N_{Lᵤ*}(Rᵤ*∩Lᵤ*) in the image of H∩Lᵤ.
This retains the original Rᵤ and its possible outer action. The marked
intersection is a point or plane parabolic unless Lᵤ is a chi-zero block;
no normalizer, inner-action or parabolic premise is added.

Source: Aschbacher--Smith 14.7.68(2), pp.1071--1072, via C.2.7(3), pp.146--147.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

omit [CharP k 2] in
theorem fixedComponent_C27_symplectic_radical_placement
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (e : starImage Lu (d.fixedCore u) Lu ≃* Sp k) (hk : 4 ≤ Nat.card k) :
    IsPRadical 2 ((starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu)) ∧
      normalizer ((starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
          (starImage Lu (d.fixedCore u) Lu) : Set (starImage Lu (d.fixedCore u) Lu)) ≤
        (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
          (starImage Lu (d.fixedCore u) Lu) := by
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  exact ChapterC.C27Source.star_symplectic_radical_placement
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K) e hk

theorem fixedComponent_C27_symplectic_marked_parabolic_or_chiZero
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (e : starImage Lu (d.fixedCore u) Lu ≃* Sp k) (hk : 4 ≤ Nat.card k) :
    (∃ g : Sp k,
      (((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
          (starImage Lu (d.fixedCore u) Lu)).map e.toMonoidHom).map
          (MulAut.conj g).toMonoidHom = pointParabolic ∨
      (((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
          (starImage Lu (d.fixedCore u) Lu)).map e.toMonoidHom).map
          (MulAut.conj g).toMonoidHom = planeParabolic) ∨
      ChapterC.IsBlock (Lu.subgroupOf (d.fixedCentralizer u)) ∧ ChapterC.IsChiZeroBlock Lu := by
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  exact ChapterC.C27Source.star_symplectic_marked_parabolic_or_chiZero
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K) e hk

/-- The literal C.2.7(e) parabolic predicate on the original D star intersection. -/
theorem fixedComponent_C27_sp4Four_parabolic_or_chiZero
    {F₄ : Type} [Field F₄] [Finite F₄] [CharP F₄ 2]
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (e : starImage Lu (d.fixedCore u) Lu ≃* Sp F₄) (hF : Nat.card F₄ = 4) :
    IsSp4FourMaximalParabolic ((starM Lu (d.fixedCore u)
        (F.H ⊓ d.fixedCentralizer u)).subgroupOf (starImage Lu (d.fixedCore u) Lu)) ∨
      ChapterC.IsBlock (Lu.subgroupOf (d.fixedCentralizer u)) ∧ ChapterC.IsChiZeroBlock Lu := by
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  exact ChapterC.C27Source.star_sp4Four_parabolic_or_chiZero
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K) e hF

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
