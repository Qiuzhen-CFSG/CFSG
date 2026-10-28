module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.CoreDisplacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLinearAmbient.LineFusion

/-!
# The original involution-centralizer core and its displacement

Choose an involution z of Z(S) central in the original T. Its actual
centralizer has a self-centralizing two-core R ≤ T, and [R,C_G(Z(S))] ≤ S.
This is the quotient-action premise used in the pending even-degree torus
argument, with every original Chapter12 hypothesis retained.

Source: Aschbacher–Smith §5.3.5–7, pp.660–661, applied on p.795.
The containment R ≤ S and terminal ambient recognition remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (d : Global.Preparation T L H A B (residual H))
  (hp : Group.IsPerfect (residual H))
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
  (he : Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F)) ∨
    Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F).reverse))
  (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include D h hmany hn hpsl hH d hp hm hF he hmax

/-- The original Chapter12 central involution and its actual core displacement. -/
theorem rankOne_global_linear_centralizer_core_setup :
    ∃ z : G, z ∈ centerIn (Global.sourceS L H) ∧ orderOf z = 2 ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      (centralizer ({z} : Set G)).pCoreIn 2 ≤ (T : Subgroup G) ∧
      ⁅(centralizer ({z} : Set G)).pCoreIn 2,
        centralizer (centerIn (Global.sourceS L H) : Set G)⁆ ≤ Global.sourceS L H ∧
      centralizer ({z} : Set G) ⊓
        centralizer ((centralizer ({z} : Set G)).pCoreIn 2 : Set G) ≤
          (centralizer ({z} : Set G)).pCoreIn 2 :=
  d.linear_exists_centralizer_core_setup (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
