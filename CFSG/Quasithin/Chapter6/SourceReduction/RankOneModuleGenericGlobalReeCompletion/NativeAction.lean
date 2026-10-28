module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.LocalActions
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.AmalgamActions

/-!
# The original whole normalizer intersection acts on the complete Ree model

The faithful compatible parabolic actions of the actual prepared pair extend
to native Ree automorphisms. The resulting homomorphism is faithful and
retains the original conjugation equations, both endpoint restrictions and
the whole Borel restriction. Positivity follows from the original comparison;
both supplied orientations are retained through the proved exclusion.

No native ambient action is an additional input. This supplies the common
normalizer action in 5.3.2. Extending both full normalizers simultaneously,
the full-extension order comparison and ambient identification remain.
Source: Aschbacher–Smith 5.3.1–2 and F.4.3, printed pp.658–659,274
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion.GeneralReeFour
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ)
  (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
include d h hH hp he

/-- The entire original normalizer intersection acts faithfully on the complete
native Ree group, retaining both endpoint restrictions and the whole middle. -/
theorem Preparation.ree_native_intersection_action :
    ∃ e : RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse,
    ∃ (a : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →*
        RankTwoAmalgam.Iso (ReeFour.amalgam m).reverse (ReeFour.amalgam m).reverse)
      (σ : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →*
        MulAut (ReeF4.Model m)),
      Function.Injective σ ∧
      (∀ g x, (e.left.symm ((a g).left (e.left x)) : G) =
        (g : G)*(x : G)*(g : G)⁻¹) ∧
      (∀ g x, (e.right.symm ((a g).right (e.right x)) : G) =
        (g : G)*(x : G)*(g : G)⁻¹) ∧
      (∀ g x, (e.middle.symm ((a g).middle (e.middle x)) : G) =
        (g : G)*(x : G)*(g : G)⁻¹) ∧
      (∀ g (x : ReeF4.Parabolics.parabolic m .linear),
        σ g x.val=((a g).left x).val) ∧
      (∀ g (x : ReeF4.Parabolics.parabolic m .suzuki),
        σ g x.val=((a g).right x).val) ∧
      (∀ g (x : ReeF4.Parabolics.borel m),
        σ g x.val=((a g).middle x).val) := by
  obtain ⟨e,l,r,a,_,_,ha,hl,hr,hal,har,hb⟩ :=
    d.ree_compatible_parabolic_actions h hH hp m he
  have hm := d.ree_parameter_positive h hp m 0 .linear e.left
  let σ := (nativeActionExtension hm).comp a
  refine ⟨e,a,σ,(nativeActionExtension_injective hm).comp ha,?_,?_,hb,?_,?_,?_⟩
  · intro g x
    rw [hal]
    exact hl (inclusion inf_le_left g) x
  · intro g x
    rw [har]
    exact hr (inclusion inf_le_right g) x
  · intro g x
    exact nativeActionExtension_left hm (a g) x
  · intro g x
    exact nativeActionExtension_right hm (a g) x
  · intro g x
    exact nativeActionExtension_middle hm (a g) x

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
