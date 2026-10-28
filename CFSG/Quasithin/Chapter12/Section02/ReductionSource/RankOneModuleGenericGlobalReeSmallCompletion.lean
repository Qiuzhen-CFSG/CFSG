module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeSmallCompletion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeOvercomponent

/-!
# The original Chapter12 full-normalizer Ree completion

The prepared whole-residual pair retains the original parameter n=2m+1.
Given the source full extension, compatible normalizer diagram and ambient
order bound, the normalizers generate the entire ambient group and their
completion is a small octagon with the full extension's order. Native group
recognition and its GlobalExit application remain separate obligations.

Source: Aschbacher–Smith 5.3.1–4, F.4.24 and 12.2.2, printed
pp.658–659,287–288,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open ChapterF.SourceCompletion.GeneralReeExtension
open ChapterF.SourceCompletion
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal original-module application of full-extension smallness,
order equality and generation by the two whole normalizers. -/
theorem rankOne_global_ree_full_normalizers_small_completion
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
    2*m+1 = n ∧ 0 < m ∧
      normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
      Nat.card G = Nat.card E.carrier ∧
      ∃ c : Completion E (normalizer (L : Set G) ⊔ normalizer (residual H : Set G) : Subgroup G),
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Function.Injective (MulAction.toPermHom
          (normalizer (L : Set G) ⊔ normalizer (residual H : Set G) : Subgroup G)
          (Vertex c.cosetFamily)) ∧
        (∀ v (p : (graph c.cosetFamily).Walk v v), p.IsCycle → 16 ≤ p.length) ∧
        (∀ v w, (graph c.cosetFamily).dist v w ≤ 8) ∧
        (∃ v, ∃ p : (graph c.cosetFamily).Walk v v, p.IsCycle ∧ p.length = 16) :=
  d.ree_full_normalizers_small_completion
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he E hext horder

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
