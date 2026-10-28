module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.LinearNormalizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.RadicalImages

/-!
# The genuine normalizer flag in the type-A fixed-component row

For an actual type-A marking of Lᵤ*, the nontrivial Rᵤ*∩Lᵤ* determines its
normalizer's partial flag. The marking is the original B.5 row parameter;
no parabolic placement is assumed, and M_K* is not identified here.

Source: Aschbacher–Smith 14.7.68(2), using C.2.7 and Aschbacher (1981), 8.2(7).
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedComponent_C27_linear_normalizer_flag
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    {n : ℕ} (hn : 2 ≤ n) (e : starImage Lu (d.fixedCore u) Lu ≃* SL(n,k))
    (hne : (starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
      (starImage Lu (d.fixedCore u) Lu) ≠ ⊥) :
    ∃ (r : ℕ) (U : Fin r → Submodule k (Fin n → k)),
      0 < r ∧ r < n ∧ StrictMono U ∧
      (∀ i, U i ≠ ⊥ ∧ U i ≠ ⊤) ∧
      (normalizer ((starImage Lu (d.fixedCore u) (d.fixedCore u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu) : Set (starImage Lu (d.fixedCore u) Lu))).map
          e.toMonoidHom = ⨅ i, Matrix.HigherLinear.parabolicSL (U i) := by
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  exact ChapterC.C27Source.star_linear_normalizer_flag
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K) hn e hne

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
