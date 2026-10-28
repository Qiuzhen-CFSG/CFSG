module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.Order

/-!
# Completion of the prepared symplectic source row

The full-normalizer marking and the proved equality with its full carrier
order discharge the three extension inputs of the existing completion.
The same extension supplies the whole intersection, faithful coset action
and original Cartan data. The existing recognition consumer then identifies
the original simple group, retaining both orientations and field order four.

Source: Aschbacher--Smith 5.3.2--4, printed pp.658--659, and F.4.31--43,
printed pp.291--296 of refs/quasithin.pdf. Preparation, the perfect whole
residual and the pure comparison remain the original source inputs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0<m) (hF : Nat.card F=2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include d h hH hp hm hF he

/-- The same extension supplies both the whole-normalizer comparison and
the full ambient order bound, with no further premise. -/
theorem Preparation.symplectic_extension_order :
    m=n ∧ ∃ E : SourceExtension F,
      (Nonempty (RankTwoAmalgam.Iso (SymplecticCompletion.diagram L (residual H)) E.amalgam) ∨
       Nonempty (RankTwoAmalgam.Iso (SymplecticCompletion.diagram L (residual H)) E.amalgam.reverse)) ∧
      Nat.card G≤Nat.card E.carrier := by
  obtain ⟨hmn,⟨a⟩⟩ := d.symplectic_full_normalizer_marking h hH hp F hm hF he
  exact ⟨hmn,a.extension,a.full_comparison,(d.symplectic_extension_card_eq h hH hp F hm hF he a).le⟩

/-- The literal prepared completion, with its extension and order inputs discharged. -/
theorem Preparation.symplectic_prepared_extension_completion :
    let E := (d.symplecticNormalizerMarking h hH hp F hm hF he).extension
    m = n ∧ Nat.card F = 2^n ∧
      Chapter5.Section03GreenExtension.SourceLocalConditions
        (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
      ∃ c : Completion E (SymplecticCompletion.join L (residual H)),
        c.middle.range = (normalizer (L : Set G) ⊓ normalizer (residual H : Set G)).subgroupOf
          (SymplecticCompletion.join L (residual H)) ∧
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Nat.card (SymplecticCompletion.join L (residual H)) ≤ Nat.card E.carrier ∧
        c.middle.range.normalCore = ⊥ ∧
        Function.Injective (MulAction.toPermHom (SymplecticCompletion.join L (residual H))
          (Subgroup.CosetGeometry.RankTwo.Vertex c.cosetFamily)) ∧
        Nat.card c.unipotentMap.range = Nat.card F ^ 4 ∧
        Nat.card c.torusMap.range = (Nat.card F - 1)^2 ∧
        c.torusMap.range ≤ normalizer (c.unipotentMap.range : Set (SymplecticCompletion.join L (residual H))) ∧
        c.unipotentMap.range ⊓ centralizer (c.torusMap.range : Set (SymplecticCompletion.join L (residual H))) = ⊥ :=
  d.symplectic_prepared_extension_completion_of_order h hH hp F hm hF he
    (d.symplectic_extension_card_eq h hH hp F hm hF he
      (d.symplecticNormalizerMarking h hH hp F hm hF he)).le

/-- Apply the existing recognition theorem to the same constructed extension. -/
theorem Preparation.symplectic_prepared_recognition :
    m=n ∧ Nat.card F=2^n ∧ SymplecticCompletion.join L (residual H)=⊤ ∧
      ClassicalGroup.IsPSp G 2 (2^n) := by
  let a := d.symplecticNormalizerMarking h hH hp F hm hF he
  obtain ⟨hmn,hFn,hgen,_,hsp⟩ := d.symplectic_extension_recognition h hH hp F hm hF he
    a.extension a.full_comparison (d.symplectic_extension_card_eq h hH hp F hm hF he a).le
  exact ⟨hmn,hFn,hgen,hsp⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
