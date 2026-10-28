module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Splitting
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.Local

/-!
# The exceptional-local splitting at the literal Chapter 12 consumer

The original ChosenModule supplies the generic input with its whole reduced
subgroup. The nonmaximal linear comparison selects the exceptional local,
and the source splitting theorem constructs its complement and sections of
its actual quotient maps. This is the splitting step of Aschbacher–Smith
5.2.17, printed p.655 (`refs/quasithin.pdf`). The ambient recognition and
GlobalExit application remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The selected original exceptional local has an actual complement and
sections preserving each chosen quotient marking. -/
theorem rankOne_global_linear_nonmaximal_exceptional_splitting
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
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    : ∃ J ∈ Chapter1.LStar G (T : Subgroup G), residual H < J ∧
      (∃ C : Subgroup J, (pCore 2 J).IsComplement' C) ∧
      ∀ e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 7),
        ∃ s : alternatingGroup (Fin 7) →* J,
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))).comp s = MonoidHom.id _ := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨_,hc⟩ := d.linear_maximal_or_exceptional hi hH hp F hm hF he
  obtain ⟨_,J,hJ,hKJ,_⟩ := hc.resolve_left hnonmax
  exact ⟨J,hJ,hKJ,d.linear_exceptional_splitting hi hH hp F hm hF he hJ hKJ⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
