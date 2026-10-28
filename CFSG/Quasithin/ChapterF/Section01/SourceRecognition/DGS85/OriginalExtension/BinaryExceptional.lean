module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.BinaryBorel
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalRigidity
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCatalogue

/-!
# Restoring the six binary exceptional marked rows

In the six exceptional rows other than J₂ and Aut(J₂), a parabolic comparison
makes the full reduced Borel a two-group. The original pair consequently
equals the reduced pair. Transport preserves the three group markings, and
the existing faithful exceptional rigidity theorem supplies both commuting
squares. The literal selected-perfect-factor consumer then excludes these
rows using its original nonsolvability hypotheses.

Source: DGS (1985), (15.1)(d), p.226, and (15.3), pp.228–231;
Aschbacher–Smith F.1.12, pp.263–264. The hypothesis is genuine parabolic
recognition. Binary Ree structural types are not identified with these
concrete models here. The J₂ extension remains a separate source argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.BinaryExceptional
open GreenBook GreenBook.ExceptionalModels SuzukiContainment

private theorem transport_parabolicModel
    {A D C A' D' C' : Type*} [Group A] [Group D] [Group C]
    [Group A'] [Group D'] [Group C']
    {α : RankTwoAmalgam A D C} {β : RankTwoAmalgam A' D' C'}
    (f : Iso α β) {c : Case} (he : ParabolicModel c β) : ParabolicModel c α := by
  cases c <;> obtain ⟨e⟩ := he <;> exact ⟨f.toParabolicEquiv.trans e⟩

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S) {c : Case} (hj : c ≠ .j2) (ha : c ≠ .autJ2)
  (he : ParabolicModel c (reducedAmalgam L S) ∨
    ParabolicModel c (reducedAmalgam L S).reverse)

include hj ha he in
/-- Both orientations of an actual binary exceptional parabolic comparison
identify the entire reduced Borel as a two-group. -/
theorem reduced_borel_isPGroup : IsPGroup 2 (commonBorel L (reducedSylow L S)) := by
  rcases he with he | he
  · exact (ExceptionalRigidity.sylow_of_parabolicModel
      (ofSubgroups_left_injective ..) (ofSubgroups_right_injective ..) hj ha he).isPGroup
  · exact (ExceptionalRigidity.sylow_of_parabolicModel
      (inclusion_injective (commonBorel_le_parabolic 1))
      (inclusion_injective (commonBorel_le_parabolic 0)) hj ha he).isPGroup

include h hj ha he in
/-- No enlargement of S or of either full endpoint remains on these rows. -/
theorem original_sylow_eq_reduced : S = reducedSylow L S :=
  BinaryBorel.original_sylow_eq_reduced h (reduced_borel_isPGroup hj ha he)

include h hj ha he in
/-- Restore the raw parabolic comparison in its supplied orientation. -/
theorem original_parabolicModels :
    ParabolicModel c (originalAmalgam L S) ∨
      ParabolicModel c (originalAmalgam L S).reverse := by
  let f := BinaryBorel.originalIsoReduced h (reduced_borel_isPGroup hj ha he)
  exact he.elim (fun e => Or.inl (transport_parabolicModel f e))
    (fun e => Or.inr (transport_parabolicModel f.reverse e))

include h hj ha he in
/-- The existing source-faithful rigidity supplies both original inclusion
squares, after the original-versus-reduced premise has been removed. -/
theorem original_models :
    IsModel c (originalAmalgam L S) ∨ IsModel c (originalAmalgam L S).reverse := by
  have hc : pCore 2 (parabolic L S 0 ⊔ parabolic L S 1 : Subgroup G) = ⊥ := by
    rw [parabolics_generate]
    exact h.twoCore_free
  rcases original_parabolicModels h hj ha he with ho | ho
  · exact Or.inl (ExceptionalRigidity.isModel_of_subgroup_parabolicModel
      _ _ _ _ _ hc ho)
  · have hc' : pCore 2 (parabolic L S 1 ⊔ parabolic L S 0 : Subgroup G) = ⊥ := by
      rw [sup_comm]
      exact hc
    exact Or.inr (ExceptionalRigidity.isModel_of_subgroup_parabolicModel
      _ _ _ (commonBorel_le_parabolic 1) (commonBorel_le_parabolic 0) hc' ho)

end BinaryExceptional

open Chapter6.Source.RankOneGeneric GreenBook.ExceptionalModels
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  {c : Case} (hj : c ≠ .j2) (ha : c ≠ .autJ2)
include d h hTH hp hj ha

/-- The literal perfect-selected-factor consumer excludes every restored
binary exceptional row, before any identification of R with the residual. -/
theorem not_reduced_binary_exceptional_parabolicModels :
    ¬ (ParabolicModel c (reducedAmalgam ![L,R] (Global.sourceS L H)) ∨
      ParabolicModel c (reducedAmalgam ![L,R] (Global.sourceS L H)).reverse) := by
  intro he
  let hf := d.hypothesisF11 h hTH
  let J : Iso (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
      (originalAmalgam ![L,R] (Global.sourceS L H)) := {
    left := MulEquiv.refl _
    right := MulEquiv.refl _
    middle := MulEquiv.subgroupCongr (lemma_F_1_3_6 hf)
    left_commutes := fun _ => rfl
    right_commutes := fun _ => rfl }
  have hn := d.not_exceptional_parabolic_models h hp c
  rcases BinaryExceptional.original_parabolicModels hf hj ha he with ho | ho
  · exact hn.1 (BinaryExceptional.transport_parabolicModel J ho)
  · exact hn.2 (BinaryExceptional.transport_parabolicModel J.reverse ho)

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
