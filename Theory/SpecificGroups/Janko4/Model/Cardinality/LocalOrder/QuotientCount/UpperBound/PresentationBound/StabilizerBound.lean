module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound.StabilizerBound.Terminal
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound.StabilizerBound.Relations
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound.StabilizerBound.Cover1
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound.StabilizerBound.Cover2
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound.StabilizerBound.Cover3
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound.StabilizerBound.Cover4
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound.StabilizerBound.Cover5

/-!
# Cardinal bound for the short stabilizer presentation

The ten-generator presentation has a chain of certified coset covers of indices
23, 22, 21, 20, and 16. At each step, the defining relations of the next abstract
presentation are proved for the named subgroup generators. Its presentation
therefore surjects onto that subgroup. The terminal subgroup is cyclic with a
defining cube relation, so has order at most three.

Multiplication along the chain gives the unconditional bound 10200960. The data
originate in GAP's multistage presentation algorithm (see `StabilizerBound/source/README.md`
and the adjacent `source/extract.g`); all relation replacements and coset
deductions are checked by Lean, with no permutation-image order assumptions.
-/

namespace Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound
open Subgroup.CosetWordCertificate StabilizerChain

private theorem descend {α β γ : Type*} {rels : Set (FreeGroup α)}
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

private theorem level5_bound : Finite Level5 ∧ Nat.card Level5 ≤ 48 := by
  have h := terminal_bound
  let := h.1
  obtain ⟨hp, hb⟩ := PresentedGroup.finite_card_le_of_cosetCover level5Subgroup Cover5.cover
  refine ⟨hp, hb.trans ?_⟩
  simpa only [Nat.card_fin] using Nat.mul_le_mul_right 16 h.2

/-- The explicit short stabilizer presentation is finite of order at most 10200960. -/
public theorem stabilizer_presentation_bound :
    Finite StabilizerPresentation ∧ Nat.card StabilizerPresentation ≤ 10200960 := by
  have h4 : Finite Level4 ∧ Nat.card Level4 ≤ 960 :=
    descend level5Relator level4Generator liftedRelations45 level5_bound Cover4.cover
  have h3 : Finite Level3 ∧ Nat.card Level3 ≤ 20160 :=
    descend level4Relator level3Generator liftedRelations34 h4 Cover3.cover
  have h2 : Finite Level2 ∧ Nat.card Level2 ≤ 443520 :=
    descend level3Relator level2Generator liftedRelations23 h3 Cover2.cover
  exact descend level2Relator level1Generator liftedRelations12 h2 Cover1.cover

end Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound
