module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.SquareCentralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder

/-!
# Nonroot square centralizers in the original full normalizers

Apply the square-centralizer calculation to W = wholeReduced T L and the
original chosen module. In each full normalizer, the whole centralizer of
a nonidentity square of S is already in the full middle. The calculation
uses the compatible pure comparison, including its reversed orientation;
it applies at n = 2 and retains the whole residual of H.

This supplies the last local inference of Aschbacher–Smith F.4.39, printed
p.294 of `refs/quasithin.pdf`. The preceding global containment, fusion and
outer transfer remain to be proved by the source extension/order owner.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- In either full normalizer, the original nonroot square has exactly its
centralizer in the whole normalizer intersection. -/
theorem rankOne_global_symplectic_square_full_normalizer_centralizers
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
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (i : Fin 2) (z : Global.sourceS L H) (hz : z ≠ 1)
    (hsq : ∃ y : Global.sourceS L H, y^2=z) :
    centralizer ({z.val} : Set G) ⊓ normalizer (![L,residual H] i : Set G) =
      centralizer ({z.val} : Set G) ⊓
        (normalizer (L : Set G) ⊓ normalizer (residual H : Set G)) :=
  d.symplectic_square_full_normalizer_centralizers
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he i z hz hsq

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
