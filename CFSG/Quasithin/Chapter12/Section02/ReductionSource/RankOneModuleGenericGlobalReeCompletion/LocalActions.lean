module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.LocalActions
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.Sylow

/-!
# The original Chapter12 Ree pair and its faithful native local actions

The actual prepared pair has the same full factor and parabolic normalizers,
and each parabolic has trivial ambient centralizer. Conjugation gives
faithful actions of both full normalizers on the native parabolics. Their
whole intersection acts faithfully on the compatible native amalgam, with
the original marking and both inclusion squares preserved.

This discharges the local-action input to 5.3.2 for the original Chapter12
consumer, at every positive Ree parameter and in both supplied comparison
orientations. Extending the action to the complete native model, the full
short-root centralizer and order comparison, and ambient recognition remain.
Source: Aschbacher–Smith 5.3.1–2 and 12.2.2, printed pp.658–659,795
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Full ambient normalizer and centralizer identities for the original parabolics. -/
theorem rankOne_global_ree_parabolic_normalizers_and_centralizers
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
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse)) :
    (∀ i : Fin 2, normalizer (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i : Set G) =
      normalizer (![L,residual H] i : Set G)) ∧
    (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ≤
      normalizer (ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H) : Set G)) ∧
    (∀ i : Fin 2,
      centralizer (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i : Set G) = ⊥) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hh := d.ree_full_normalizers_preserve_parabolics hi hH hp m he
  exact ⟨hh.1,hh.2,d.ree_parabolic_centralizers_eq_bot hi hH hp m he⟩

/-- The actual full normalizers act faithfully on the native parabolics, with
a compatible action of their entire intersection and exact marked conjugation. -/
theorem rankOne_global_ree_compatible_parabolic_actions
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
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse)) :
    ∃ e : RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse,
    ∃ (l : normalizer (L : Set G) →* MulAut (ReeF4.Parabolics.parabolic m .linear))
      (r : normalizer (residual H : Set G) →* MulAut (ReeF4.Parabolics.parabolic m .suzuki))
      (a : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →*
        RankTwoAmalgam.Iso (ReeFour.amalgam m).reverse (ReeFour.amalgam m).reverse),
      Function.Injective l ∧ Function.Injective r ∧ Function.Injective a ∧
      (∀ g x, (e.left.symm (l g (e.left x)) : G) = (g : G)*(x : G)*(g : G)⁻¹) ∧
      (∀ g x, (e.right.symm (r g (e.right x)) : G) = (g : G)*(x : G)*(g : G)⁻¹) ∧
      (∀ g, (a g).left = l (inclusion inf_le_left g)) ∧
      (∀ g, (a g).right = r (inclusion inf_le_right g)) ∧
      (∀ g x, (e.middle.symm ((a g).middle (e.middle x)) : G) =
        (g : G)*(x : G)*(g : G)⁻¹) := by
  exact d.ree_compatible_parabolic_actions
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
