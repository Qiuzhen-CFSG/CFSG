module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.MarkedAction
public import CFSG.Quasithin.Chapter5.Section03SymplecticSource.NativeLift

/-!
# Native lifts of the original common-normalizer action

Marked recognition of the two concrete native completions discharges the
pointwise extendibility premise of the previous faithful-action construction.
The resulting homomorphism acts on Sp₄(F), agrees with the original conjugation
on both full pure parabolics and their whole Borel, and has exactly that Borel
as its inner preimage. Both orientations and q = 4 are retained.

This is the simultaneous native-action step in Aschbacher–Smith 5.3.2,
printed p.659 of `refs/quasithin.pdf`. The two full endpoint maps and the
ambient fusion/order argument are further obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- The entire original common normalizer acts faithfully on the native group,
with its prescribed actions on both parabolics and the whole Borel. -/
theorem Preparation.symplectic_native_middle_lift
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    m = n ∧
      ((∃ a : SymplecticMarkedMiddleAction L (residual H) (sourceS L H)
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F),
        ∃ σ : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →*
          SourceNormalizerExtension.flagAutomorphisms F,
          Function.Injective σ ∧ SourceNormalizerExtension.restriction.comp σ = a.action ∧
          (∀ g, DiagramAutomorphisms.PreservesDiagram (σ g).val) ∧
          ∀ g, (σ g).val ∈ (MulAut.conj : Sp F →* MulAut (Sp F)).range ↔
            g.val ∈ (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
              ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G)) ∨
       (∃ a : SymplecticMarkedMiddleAction L (residual H) (sourceS L H)
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse,
        ∃ σ : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →*
          SourceNormalizerExtension.flagAutomorphisms F,
          Function.Injective σ ∧ SourceNormalizerExtension.reverseRestriction.comp σ = a.action ∧
          (∀ g, DiagramAutomorphisms.PreservesDiagram (σ g).val) ∧
          ∀ g, (σ g).val ∈ (MulAut.conj : Sp F →* MulAut (Sp F)).range ↔
            g.val ∈ (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
              ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G))) := by
  obtain ⟨hmn,ha⟩ := d.symplectic_native_middle_action h hH hp F hm hF he
  have hm' : 1 < m := hmn ▸ h.exponent
  refine ⟨hmn,?_⟩
  rcases ha with ha | ha
  · obtain ⟨a⟩ := ha
    exact Or.inl ⟨a, a.native_lift_of_extendible hF hm'
      (fun g => Chapter5.Section03SymplecticSource.restriction_surjective hF hm' (a.action g))⟩
  · obtain ⟨a⟩ := ha
    exact Or.inr ⟨a, a.native_lift_of_extendible_reverse hF hm'
      (fun g => Chapter5.Section03SymplecticSource.reverseRestriction_surjective hF hm' (a.action g))⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
