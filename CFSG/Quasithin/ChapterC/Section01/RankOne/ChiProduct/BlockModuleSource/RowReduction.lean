module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ComponentSource.Models

/-!
# The actual B.4 rows which can enlarge a local seed

Every B.4 row except the odd alternating natural modules and exceptional
A₇ module satisfies the proved proper Sylow-overgroup Fitting bound.
The symmetric rows are restricted with their original marked group map,
so the surviving conclusion retains the action, not just an actor type.
B.1.13 uses the bound to rule out every other row for a strict seed.

Source: Aschbacher--Smith B.1.13 and C.1.28, printed pp.73--74,133.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
open ChapterB.ComponentRecognition.SylowOvergroups

/-- Only the two alternating natural rows and the exceptional A₇ module
can enlarge a locally subnormal seed in the B.1.13 argument. -/
theorem action_bound_or_alternating_module
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (L H : Subgroup D) [IsQuasisimple L]
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) :
    ProperSylowFittingBound L ∨
      (∃ n, (n = 5 ∨ n = 7) ∧ Nonempty (ActionEquiv (ρ.comp L.subtype) (alternatingNatural n))) ∨
      (Nonempty (L ≃* alternatingGroup (Fin 7)) ∧ Module.finrank (ZMod 2) W = 4) := by
  cases h with
  | linearTwo F _ e _ _ =>
    exact Or.inl (properSylowFittingBound_psl2 F.Carrier F.degree F.degree_pos F.card_eq
      (e.groupEquiv.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F.Carrier))))
  | linearThree F _ e _ =>
    let : IsQuasisimple SL(3,F.Carrier) := IsQuasisimple.of_mulEquiv e.groupEquiv
    exact Or.inl (properSylowFittingBound_of_equiv e.groupEquiv
      (properSylowFittingBound_of_centralQuotient (MulEquiv.refl _)
        (ComponentSource.linearThree_properSylowFittingBound F.Carrier F.degree_pos F.card_eq)))
  | symplectic F hF _ e _ =>
    exact Or.inl (properSylowFittingBound_of_equiv e.groupEquiv
      (properSylowFittingBound_sp_four F.Carrier F.degree hF F.card_eq))
  | symplecticTwo e _ =>
    exact Or.inl (properSylowFittingBound_of_equiv
      (e.subgroupEquiv.trans
        (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (F := ZMod 2) (by simp)))
      (AlternatingSix.ProperSylowOvergroups.centralCover_fitting_bound (MonoidHom.id _)
        Function.surjective_id (by simp)))
  | g2 F _ _ e _ _ =>
    exact Or.inl (properSylowFittingBound_of_equiv e.groupEquiv
      (properSylowFittingBound_g2 F.Carrier (MulEquiv.refl _)))
  | g2Two e _ _ =>
    apply Or.inl
    apply properSylowFittingBound_of_equiv e.subgroupEquiv
    intro S X hSX hX
    rw [generalizedFitting_eq_pCore_of_selfCentralizing 2
      (TwistedExceptional.BinaryG2.centralizer_twoCore_le S X hX hSX)]
    exact le_sup_left
  | symmetric n hn e _ _ =>
    right; left
    refine ⟨n,hn,⟨?_⟩⟩
    refine { groupEquiv := e.subgroupEquiv
             linearEquiv := e.action.linearEquiv
             intertwines := ?_ }
    intro l w
    have hh := e.action.intertwines ⟨l,e.contained l.property⟩ w
    rw [e.compatible] at hh
    exact hh
  | alternatingSix _ e _ _ =>
    exact Or.inl (properSylowFittingBound_of_equiv e.groupEquiv
      (AlternatingSix.ProperSylowOvergroups.centralCover_fitting_bound (MonoidHom.id _)
        Function.surjective_id (by simp)))
  | alternatingSeven _ _ e hd _ _ =>
    exact Or.inr (Or.inr ⟨⟨e⟩,hd⟩)
  | tripleSix _ a _ =>
    exact Or.inl (properSylowFittingBound_of_centralQuotient a.quotientEquiv
      (AlternatingSix.ProperSylowOvergroups.centralCover_fitting_bound (MonoidHom.id _)
        Function.surjective_id (by simp)))
  | binaryLinear d hd _ e _ =>
    apply Or.inl
    apply properSylowFittingBound_of_equiv
      (e.groupEquiv.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < d)).symm)
    rcases hd with rfl | rfl
    · exact ComponentSource.linearFour_properSylowFittingBound
    · exact properSylowFittingBound_psl5_two
  | orthogonalSix _ _ e _ _ =>
    apply Or.inl
    apply properSylowFittingBound_of_equiv e.groupEquiv
    intro S X hSX hX
    rw [generalizedFitting_eq_pCore_of_selfCentralizing 2
      (ComponentSource.alternatingEight_sylow_overgroup_core S X hSX hX)]
    exact le_sup_left
  | symmetricEight _ e _ =>
    apply Or.inl
    apply properSylowFittingBound_of_equiv e.subgroupEquiv
    intro S X hSX hX
    rw [generalizedFitting_eq_pCore_of_selfCentralizing 2
      (ComponentSource.alternatingEight_sylow_overgroup_core S X hSX hX)]
    exact le_sup_left
  | exteriorFive _ _ e _ _ _ =>
    exact Or.inl (properSylowFittingBound_of_equiv
      (e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 5)).symm)
      properSylowFittingBound_psl5_two)

/-- Pull the surviving action charts back through the original component
marking. This keeps large quotient expressions out of the intertwiner proof. -/
theorem action_bound_or_alternating_module_of_marking
    {D B W : Type*} [Group D] [Finite D] [Group B] [Finite B]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (τ : Representation (ZMod 2) B W)
    (L H : Subgroup D) [IsQuasisimple L]
    (a : B ≃* L) (ha : ∀ b, ρ (a b) = τ b)
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) :
    ProperSylowFittingBound B ∨
      (∃ n, (n = 5 ∨ n = 7) ∧ Nonempty (ActionEquiv τ (alternatingNatural n))) ∨
      (Nonempty (B ≃* alternatingGroup (Fin 7)) ∧ Module.finrank (ZMod 2) W = 4) := by
  rcases action_bound_or_alternating_module ρ L H h with hb | hn | hd
  · exact Or.inl (properSylowFittingBound_of_equiv a hb)
  · obtain ⟨n,hn,⟨c⟩⟩ := hn
    right; left
    refine ⟨n,hn,⟨{ groupEquiv := a.trans c.groupEquiv
                    linearEquiv := c.linearEquiv
                    intertwines := ?_ }⟩⟩
    intro b w
    have hh := c.intertwines (a b) w
    change c.linearEquiv (ρ (a b) w) = _ at hh
    rw [ha b] at hh
    exact hh
  · obtain ⟨⟨e⟩,hd⟩ := hd
    exact Or.inr (Or.inr ⟨⟨a.trans e⟩,hd⟩)

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
