module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.FieldAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder

/-!
# The common field action for the original Chapter 12 symplectic pair

The entire common normalizer acts with one coherent field homomorphism on
both central roots and both central-quotient coordinates. Actual native
flag automorphisms realize these actions, and the whole pure Borel has
trivial field part. This applies to W = wholeReduced T L and retains the
whole residual, both orientations and n = 2.

Full agreement on the endpoints, ambient fusion, field-involution Sylow
placement and the full-extension order comparison remain required.
Source: Aschbacher–Smith 5.3.2, p.659, and the Chapter 12 application,
p.795 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original prepared source pair has a coherent common field action
and native representatives on its center and central quotient. -/
theorem rankOne_global_symplectic_native_middle_field_control
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    m = n ∧
      ((∃ a : Global.SymplecticMarkedMiddleAction L (residual H) (Global.sourceS L H)
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F),
        Global.SymplecticFieldControl hF a.action) ∨
       (∃ a : Global.SymplecticMarkedMiddleAction L (residual H) (Global.sourceS L H)
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse,
        Global.SymplecticFieldControl hF (fun g => (a.action g).reverse))) :=
  d.symplectic_native_middle_field_control
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
