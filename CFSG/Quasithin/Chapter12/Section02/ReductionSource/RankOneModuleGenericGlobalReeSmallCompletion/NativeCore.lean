module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeSmallCompletion.NativeCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeSmallCompletion

/-!
# Native Ree completion in the original Chapter12 ambient group

The original full extension, compatible whole-normalizer diagram and ambient
order bound yield a faithful native linear/Borel/Suzuki completion in G.
Ambient simplicity and the normal native-image subgroup prove exact native
order. The same Borel marking carries the positive and Cartan calculations,
including q=8. This is a reduction to native group recognition; it does not
supply an isomorphism to the native group or GlobalExit.

Source: Aschbacher–Smith 5.3.1–4, F.4.17,24 and 12.2.2,
printed pp.658–659,283,287–288,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open ChapterF.SourceCompletion.GeneralReeExtension
open ChapterF.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal original-module application of the normal native-image reduction
and marked Cartan calculation. The earlier full-extension premises are retained. -/
theorem rankOne_global_ree_full_normalizers_native_completion
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse))
    (E : SourceExtension m)
    (hext : Nonempty (RankTwoAmalgam.Iso
        (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (residual H : Set G))) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (residual H : Set G))) E.amalgam.reverse))
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    2*m+1 = n ∧ 0 < m ∧ Nat.card G = Nat.card (ReeF4.Model m) ∧
      ∃ c : GeneralReeFour.Completion m G,
        c.left.range ⊓ c.right.range = c.middle.range ∧
        ((ReeF4.Parabolics.unipotent m).subgroupOf (ReeF4.Parabolics.borel m)).map c.middle ⊓
          centralizer (((ReeF4.Parabolics.fixedTorus m).subgroupOf (ReeF4.Parabolics.borel m)).map c.middle : Set G) = ⊥ ∧
        c.middle.range ⊓ normalizer
          (((ReeF4.Parabolics.fixedTorus m).subgroupOf (ReeF4.Parabolics.borel m)).map c.middle : Set G) =
          ((ReeF4.Parabolics.fixedTorus m).subgroupOf (ReeF4.Parabolics.borel m)).map c.middle :=
  d.ree_full_normalizers_native_completion
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he E hext horder

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
