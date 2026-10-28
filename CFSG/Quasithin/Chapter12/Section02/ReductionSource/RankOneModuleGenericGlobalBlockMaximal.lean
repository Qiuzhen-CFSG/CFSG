module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalBlockMaximal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Right maximality in the original linear and symplectic pair

The literal whole-residual comparison gives K = O²(H) maximal in L(G,T)
when the original exponent differs from two. This removes the right-maximality
premise from the normalizer application for these rows. In every linear row,
the complete alternative is maximality or an exceptional maximal A₇ block,
with the original exponent then equal to two.

Both orientations use the whole overlap and S = O₂(N_G(L) ∩ H).
Preparation, exhaustive comparison and original uniqueness are still upstream
obligations; these local results do not recognize the ambient completion.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653, and the Chapter12
application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The full linear-row alternative on the actual Chapter12 residual. -/
theorem rankOne_global_linear_maximal_or_exceptional
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
      (LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (LinearThree.amalgam F).reverse)) :
    m = n ∧ (residual H ∈ Chapter1.LStar G (T : Subgroup G) ∨
      n = 2 ∧ ∃ J ∈ Chapter1.LStar G (T : Subgroup G),
        residual H < J ∧ ChapterC.IsExceptionalA7Block J) :=
  d.linear_maximal_or_exceptional
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

/-- The actual normalizer pair in either block row with n > 2. No separate
right-maximality, common-Sylow or enlarged-core hypothesis is required. -/
theorem rankOne_global_block_normalizer_local_conditions
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 2 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he :
      (Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (LinearThree.amalgam F)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (LinearThree.amalgam F).reverse)) ∨
      (Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (SymplecticFour.amalgam F)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (SymplecticFour.amalgam F).reverse))) :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) :=
  d.block_normalizer_local_conditions
    (D.rankOne_generic_input_of_many h hmany (by omega) hpsl)
    hH hp (by omega) F hm hF he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
