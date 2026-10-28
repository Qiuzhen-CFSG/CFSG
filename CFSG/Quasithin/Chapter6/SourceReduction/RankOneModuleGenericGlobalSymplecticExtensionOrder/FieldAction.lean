module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.MarkedAction
public import Theory.SpecificGroups.SymplecticFour.SourceNormalizerExtension.FieldAction

/-!
# A coherent field action for the original full common normalizer

Conjugation by the entire original common normalizer acts on the same marked
pure symplectic amalgam. The native square-map argument supplies a single
homomorphism to the field automorphism group, simultaneously controlling both
central-root factors and both central-quotient coordinates. Each value has
an actual native flag automorphism with those same actions. The entire pure
Borel has trivial field part, including its odd Cartans.

The original preparation and whole residual supply all premises. Both
orientations and n = 2 are retained. The native representatives do not yet
agree with the full endpoint actions; no full-normalizer extension or ambient
order bound is inferred from agreement on the center and central quotient.

Source: the simultaneous local-action construction required in
Aschbacher–Smith 5.3.2, printed p.659 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open SourceNormalizerExtension QuotientActors

/-- A common field homomorphism for an actual marked action, with native
representatives on the entire Sylow center and its central quotient. -/
def SymplecticFieldControl {D F : Type*} [Group D] [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2^m)
    (ρ : D → RankTwoAmalgam.Iso (SourceNormalizerExtension.diagram F)
      (SourceNormalizerExtension.diagram F)) : Prop :=
  ∃ σ : D →* (F ≃+* F),
    (∀ g : D, ∃ c d : Fˣ,
      (∀ x : F × F, (planeAction (sylowAction hF (ρ g)) (Multiplicative.ofAdd x)).toAdd =
        (c * σ g x.1, d * σ g x.2)) ∧
      (∀ x : F × F, centralAction (sylowAction hF (ρ g)) x =
        ((c:F)^2 * d * σ g x.1, c * d * σ g x.2))) ∧
    (∀ g : D, ∀ b : borel (F := F), ρ g = restriction (innerBorel b) → σ g = 1) ∧
    ∀ g : D, ∃ α : flagAutomorphisms F,
      planeAction (sylowAction hF (restriction α)) = planeAction (sylowAction hF (ρ g)) ∧
      centralAction (sylowAction hF (restriction α)) = centralAction (sylowAction hF (ρ g))

private theorem field_control {D F : Type*} [Group D] [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2^m) (hm : 1 < m)
    (ρ : D →* RankTwoAmalgam.Iso (SourceNormalizerExtension.diagram F)
      (SourceNormalizerExtension.diagram F)) : SymplecticFieldControl hF ρ := by
  refine ⟨(fieldAction hF hm).comp ρ, fun g => fieldAction_spec hF hm (ρ g), ?_,
    fun g => native_representative hF hm (ρ g)⟩
  intro g b he
  change fieldAction hF hm (ρ g) = 1
  rw [he]
  exact fieldAction_innerBorel hF hm b

variable {G : Type*} [Group G] [Finite G]

/-- The original full common normalizer has one coherent field action in
both orientations, realized natively on the center and central quotient. -/
theorem Preparation.symplectic_native_middle_field_control
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
        SymplecticFieldControl hF a.action) ∨
       (∃ a : SymplecticMarkedMiddleAction L (residual H) (sourceS L H)
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse,
        SymplecticFieldControl hF (fun g => (a.action g).reverse))) := by
  obtain ⟨hmn,ha⟩ := d.symplectic_native_middle_action h hH hp F hm hF he
  have hm' : 1 < m := hmn ▸ h.exponent
  refine ⟨hmn,?_⟩
  rcases ha with ha | ha
  · obtain ⟨a⟩ := ha
    exact Or.inl ⟨a,field_control hF hm' a.action⟩
  · obtain ⟨a⟩ := ha
    let ρ : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →*
        RankTwoAmalgam.Iso (SourceNormalizerExtension.diagram F)
          (SourceNormalizerExtension.diagram F) :=
      { toFun := fun g => (a.action g).reverse
        map_one' := by rw [map_one]; rfl
        map_mul' := fun g k => by rw [map_mul]; rfl }
    exact Or.inr ⟨a,field_control hF hm' ρ⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
