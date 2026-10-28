module

public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticParabolic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.StarResidual
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.SymplecticParabolics

/-!
# Excluding the nonbinary symplectic row at the original fixed centralizer

The source Thompson and radical geometry constructs the full point or plane
parabolic on the literal Lᵤ* and (H ∩ Lᵤ)*. Its scalar quotient contradicts
the perfect A₅ residual already constructed from the original K-image.
This excludes every even field of size at least four, before any block or
C.2.7 alternatives have been assumed. The binary derived row remains separate.

Source: Aschbacher--Smith C.2.7(3)(e), pp.145--147, and 14.7.68(2), pp.1071--1072.
-/

public section
open Subgroup Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
open FullSieve FullSieve.SourceInterface Nonquasisimple

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The entire nonbinary symplectic B.5 row is impossible on the original star component. -/
theorem Data.fixedComponent_C27_symplectic_row_impossible (d : Data T L V F W) (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : starImage Lu (d.fixedCore u) Lu ≃* Sp k) (hk : 4 ≤ Nat.card k) : False := by
  have input := d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
    d.point_mem_U_commutator_K
  obtain ⟨g,hg⟩ := ChapterC.C27Source.star_symplectic_marked_parabolic_from_source input e hk
  let P := (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
    (starImage Lu (d.fixedCore u) Lu)
  let a := e.trans (MulAut.conj g)
  have hg' : P.map a.toMonoidHom = pointParabolic ∨
      P.map a.toMonoidHom = planeParabolic := by
    have ha : a.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := rfl
    rw [ha]
    simpa only [← Subgroup.map_map] using hg
  let t := (subgroupOfEquivOfLe
    (starM_le Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))).symm.trans (a.subgroupMap P)
  apply symplectic_parabolic_impossible (d.fixedStarM_hasA5TwoResidual_of_source u h) hk
  rcases hg' with hp | hp
  · exact Or.inl ⟨t.trans (MulEquiv.subgroupCongr hp)⟩
  · exact Or.inr ⟨t.trans (MulEquiv.subgroupCongr hp)⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
