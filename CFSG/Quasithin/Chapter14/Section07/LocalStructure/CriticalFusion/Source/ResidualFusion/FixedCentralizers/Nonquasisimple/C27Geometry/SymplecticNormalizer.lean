module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticNormalizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.RadicalImages

/-!
# The exact symplectic normalizer in the original D component

Apply the intrinsic symplectic radical classification to the actual Lᵤ* and
Rᵤ*∩Lᵤ*. All C.2.3 hypotheses and relative component normality come from the
original fixed-centralizer case. A symplectic marking and nontriviality select
this row; no parabolic, Borel, rank bound or placement assertion is an input.

Source: Aschbacher–Smith 14.7.68(2), applying C.2.7 and Aschbacher (1981), 8.2(7).
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

theorem fixedComponent_C27_symplectic_normalizer_parabolic_or_borel
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : starImage Lu (d.fixedCore u) Lu ≃* Sp k)
    (hne : (starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
      (starImage Lu (d.fixedCore u) Lu) ≠ ⊥) :
    ∃ g : Sp k,
      (normalizer ((starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu) : Set (starImage Lu (d.fixedCore u) Lu))).map
          ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = pointParabolic ∨
      (normalizer ((starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu) : Set (starImage Lu (d.fixedCore u) Lu))).map
          ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = planeParabolic ∨
      (normalizer ((starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu) : Set (starImage Lu (d.fixedCore u) Lu))).map
          ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) =
            Theory.SpecificGroups.SymplecticFour.borel := by
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  exact ChapterC.C27Source.star_symplectic_normalizer_parabolic_or_borel
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K) e hne

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
