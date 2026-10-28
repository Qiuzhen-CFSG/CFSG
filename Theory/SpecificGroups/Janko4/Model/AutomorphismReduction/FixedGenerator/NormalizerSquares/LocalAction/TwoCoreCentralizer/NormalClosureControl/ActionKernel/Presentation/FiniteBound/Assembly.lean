module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover1
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover2
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover3
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.LowerRelations

/-!
# The recursive stabilizer bound

The three checked covers have indices 320, 3 and 4. The lifted relations
provide surjections from each child presentation onto the named subgroup;
starting from the trivial subgroup proves finiteness and the bound 3840.
See `source/README.md` for the untrusted discovery provenance.
-/

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound
open Subgroup.CosetWordCertificate

/-- A finite child presentation and a finite coset cover bound the parent. -/
public theorem finite_card_le_of_child {α β γ : Type*} {rels : Set (FreeGroup α)}
    (r : γ → Word β) (g : β → PresentedGroup rels)
    (hr : ∀ i, eval g (r i) = 1) {n k : Nat}
    (hc : Finite (PresentedGroup (Set.range (fun i => FreeGroup.mk (r i)))) ∧
      Nat.card (PresentedGroup (Set.range (fun i => FreeGroup.mk (r i)))) ≤ n)
    (cover : Subgroup.GeneratorCosetCover (Subgroup.closure (Set.range g))
      PresentedGroup.of (Fin k)) :
    Finite (PresentedGroup rels) ∧ Nat.card (PresentedGroup rels) ≤ n * k := by
  let f : PresentedGroup (Set.range (fun i => FreeGroup.mk (r i))) →* PresentedGroup rels :=
    PresentedGroup.toGroup (f := g) (by rintro _ ⟨i, rfl⟩; exact hr i)
  have hf : f.range = Subgroup.closure (Set.range g) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
      (Set.range (fun i => FreeGroup.mk (r i))), MonoidHom.map_closure, ← Set.range_comp]
    congr 1
    apply congrArg Set.range
    funext i
    exact PresentedGroup.toGroup.of _
  let := hc.1
  have hfin : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have hcard : Nat.card f.range ≤ n :=
    (Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective).trans hc.2
  rw [hf] at hfin hcard
  let := hfin
  obtain ⟨hp, hb⟩ := PresentedGroup.finite_card_le_of_cosetCover _ cover
  refine ⟨hp, hb.trans ?_⟩
  simpa only [Nat.card_fin] using Nat.mul_le_mul_right k hcard

private theorem level3_bound : Finite Level3 ∧ Nat.card Level3 ≤ 4 := by
  have h := PresentedGroup.finite_card_le_of_cosetCover (⊥ : Subgroup Level3) Cover3.cover
  simpa only [level3Subgroup, Nat.card_eq_fintype_card, Fintype.card_fin,
    Fintype.card_unique, one_mul] using h

/-- The seven-generator abstract presentation is finite, with order at most 3840. -/
public theorem stabilizer_finite_card_le : Finite Level1 ∧ Nat.card Level1 ≤ 3840 := by
  have h2 : Finite Level2 ∧ Nat.card Level2 ≤ 12 :=
    finite_card_le_of_child level3Relator level2Generator liftedRelations23 level3_bound Cover2.cover
  exact finite_card_le_of_child level2Relator level1Generator liftedRelations12 h2 Cover1.cover

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound
