module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.NativeLift
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder

/-!
# The actual native common-normalizer action in Chapter 12

For W = wholeReduced T L the entire original common normalizer now acts
faithfully on native Sp₄(F), with exactly the original conjugation maps on
both pure parabolics and their whole intersection. The pure common Borel is
the exact inner preimage. No native-extendibility premise remains; both
orientations and n = 2 are included.

Source: Aschbacher–Smith 5.3.2, p.659, and its Chapter 12 application,
p.795 of `refs/quasithin.pdf`. Full endpoint realization and ambient order
are subsequent source obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The prepared original Chapter 12 pair has a faithful native common-normalizer
action with both endpoint markings and the exact inner preimage. -/
theorem rankOne_global_symplectic_native_middle_lift
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
        ∃ σ : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →*
          SourceNormalizerExtension.flagAutomorphisms F,
          Function.Injective σ ∧ SourceNormalizerExtension.restriction.comp σ = a.action ∧
          (∀ g, DiagramAutomorphisms.PreservesDiagram (σ g).val) ∧
          ∀ g, (σ g).val ∈ (MulAut.conj : Sp F →* MulAut (Sp F)).range ↔
            g.val ∈ (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
              ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G)) ∨
       (∃ a : Global.SymplecticMarkedMiddleAction L (residual H) (Global.sourceS L H)
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse,
        ∃ σ : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →*
          SourceNormalizerExtension.flagAutomorphisms F,
          Function.Injective σ ∧ SourceNormalizerExtension.reverseRestriction.comp σ = a.action ∧
          (∀ g, DiagramAutomorphisms.PreservesDiagram (σ g).val) ∧
          ∀ g, (σ g).val ∈ (MulAut.conj : Sp F →* MulAut (Sp F)).range ↔
            g.val ∈ (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
              ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G))) :=
  d.symplectic_native_middle_lift
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
