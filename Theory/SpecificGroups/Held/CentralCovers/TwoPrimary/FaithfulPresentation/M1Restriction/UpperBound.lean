module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBound.Terminal
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBound.Relations
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBound.Cover0
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBound.Cover1
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBound.Cover2

/-!
# Order bound for the independent twelve-relator M₁ presentation

The literal presentations frozen in `M1Restriction/source/levels.json` give a
chain of named subgroups. Checked abstract coset deductions bound their indices
by 1360, 90 and 8. Relator replacement proofs construct the homomorphisms from
each child presentation onto its named subgroup; the last subgroup is cyclic
with a square-one generator. Multiplying these bounds gives 1958400.

The frozen GAP data guide discovery only. All coset transitions and child
relations follow from the literal defining relators, without any permutation
order, lifting to Held's presentation, or global faithfulness assumption.
See `UpperBound/source/README.md` for the certificate format and measurements.
-/

namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
open Subgroup.CosetWordCertificate UpperBoundChain

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

private theorem level2_bound : Finite Level2 ∧ Nat.card Level2 ≤ 16 := by
  have h := terminal_bound
  let := h.1
  obtain ⟨hp, hb⟩ := PresentedGroup.finite_card_le_of_cosetCover level2Subgroup Cover2.cover
  refine ⟨hp, hb.trans ?_⟩
  simpa only [Nat.card_fin] using Nat.mul_le_mul_right 8 h.2

/-- The group on exactly the twelve frozen relators is finite of order at most 1958400. -/
public theorem localPresentation_bound : LocalPresentationBound := by
  have h1 : Finite Level1 ∧ Nat.card Level1 ≤ 1440 :=
    descend level2Relator level1Generator liftedRelations12 level2_bound Cover1.cover
  exact descend level1Relator level0Generator liftedRelations01 h1 Cover0.cover

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
