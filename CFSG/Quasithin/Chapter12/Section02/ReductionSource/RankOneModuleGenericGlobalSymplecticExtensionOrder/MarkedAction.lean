module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.MarkedAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder

/-!
# The original Chapter 12 common normalizer on the native symplectic pair

The full intersection N_G(L) ∩ N_G(O²(H)) acts faithfully on the native
marked parabolic amalgam through the same three comparison maps. This
application uses W = wholeReduced T L, retains the whole residual and both
orientations, and includes n = 2. The action retains the full pure common
Borel, including its odd Cartans.

This is a marked-amalgam action, not yet a native Sp₄ automorphism action.
Its pointwise native extendibility and the subsequent ambient fusion,
outer transfer and order comparison remain required by 5.3.2–4.

Source: Aschbacher–Smith 5.3.1–2, printed pp.658–659, and the Chapter 12
application on p.795 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual full common normalizer has a faithful native marked-pair
action, with the original exponent and original source conjugation. -/
theorem rankOne_global_symplectic_native_middle_action
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
      (Nonempty (Global.SymplecticMarkedMiddleAction L (residual H) (Global.sourceS L H)
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
       Nonempty (Global.SymplecticMarkedMiddleAction L (residual H) (Global.sourceS L H)
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :=
  d.symplectic_native_middle_action
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
