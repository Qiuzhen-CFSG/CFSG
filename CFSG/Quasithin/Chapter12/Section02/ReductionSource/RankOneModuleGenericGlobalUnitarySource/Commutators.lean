module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Commutators
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four

/-!
# The original prepared degree-two unitary branch is impossible

The literal whole-module input supplies the same prepared ambient hypotheses.
Two inner quotient actors yield a nonzero long-root commutator in the full
centralizer selected earlier. Its previously proved disjointness from the
original right-residual center gives the contradiction. Both orientations,
the original full Sylow and q=4 remain included.

The ordinary-even comparison still requires its own fixed-centralizer lower
bound or an alternative ambient argument. No such premise is erased here.
Source: Aschbacher–Smith F.4.35,37–38 and 12.2, pp.292–294,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}
variable (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
include D h hmany hn hpsl hH d hp hm hc

theorem rankOne_unitaryFour_outer_long_commutator
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L)
    (hlarge : 4 ≤ (L.pCoreIn 2).relIndex
      (((T : Subgroup G) ⊓ L) ⊓ centralizer ({u.val} : Set G))) :
    let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
    (_root_.commutator P).map P.subtype ⊓
      (center (residual H)).map (residual H).subtype ≠ ⊥ :=
  d.unitaryFour_outer_long_commutator
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc u hu ho hlarge

omit hc in
/-- No original prepared degree-two unitary comparison exists. -/
theorem rankOne_unitaryFour_degreeTwo_impossible
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    False :=
  d.unitaryFour_degreeTwo_impossible
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he

/-- The literal original chosen-module row reduces to an ordinary comparison. -/
theorem rankOne_unitaryFour_comparison_ordinary :
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse) :=
  d.unitaryFour_comparison_ordinary
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
