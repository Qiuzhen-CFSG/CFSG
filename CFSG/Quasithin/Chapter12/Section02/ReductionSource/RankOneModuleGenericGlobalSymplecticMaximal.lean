module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticMaximal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Right maximality of the original symplectic pair

The actual Sp₄ comparison makes K = O²(H) maximal in L(G,T), including
original exponent two. Consequently the ambient normalizer pair satisfies
5.3's local conditions with no separate right-maximality, common-Sylow,
or enlarged-core premises. Both orientations retain the whole overlap and
S = O₂(N_G(L) ∩ H).

This completes the symplectic row of 5.2.8 in the Chapter12 application.
Exhaustive comparison, the nonblock maximality rows, original uniqueness
and recognition of the ambient completion remain explicit obligations.
Source: Aschbacher–Smith 5.2.8, printed p.652, and Chapter12, p.795
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- All symplectic rows have maximal right residual, including Sp₄(4). -/
theorem rankOne_global_symplectic_right_maximal
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
      (SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (SymplecticFour.amalgam F).reverse)) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) :=
  d.symplectic_right_maximal
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

/-- The actual symplectic normalizer pair at every original exponent n > 1. -/
theorem rankOne_global_symplectic_normalizer_local_conditions
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
      (SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (SymplecticFour.amalgam F).reverse)) :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) :=
  d.symplectic_normalizer_local_conditions
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
