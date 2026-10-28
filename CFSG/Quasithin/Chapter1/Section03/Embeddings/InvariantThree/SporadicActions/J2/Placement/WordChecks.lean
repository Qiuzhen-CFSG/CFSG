module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.WordChecks.Normalizers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.WordChecks.Orders

/-!
# Finite word checks for the J₂ pair placement

The fixed subgroup lies in the normalizer of the fixed second radical. Of the
72 retained representatives, the first six lie in that normalizer; every other
representative has the retained order-five obstruction word. These statements
are unconditional finite calculations in the concrete degree-100 carrier.

`Normalizers` checks both conjugation directions on each radical generator;
`Orders` checks fifth powers and nonidentity. The independent double-coset
coverage obligation and the source pair-placement assembly remain with the
parent module.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511/PDF p.528,
and GLS3 Table 5.3g. Witness provenance is retained in `Placement/source/`.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics

/-- The seven fixed subgroup generators normalize the second radical. -/
theorem s_le_p₂ : Seed.s ≤ Seed.p₂ := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i, hi⟩, rfl⟩
  have h := WordChecks.normalizerElement_mem ⟨i, by omega⟩
  change Seed.sGenerator ⟨i, hi⟩ ∈ Seed.p₂
  simpa only [WordChecks.normalizerElement, dif_pos hi] using h

/-- Representatives zero through five lie in the actual second normalizer. -/
theorem representative_mem_p₂ (i : Fin 72) (hi : i.val < 6) :
    representative i ∈ Seed.p₂ := by
  have h := WordChecks.normalizerElement_mem ⟨i.val + 7, by omega⟩
  have hge : ¬ i.val + 7 < 7 := by omega
  simpa only [WordChecks.normalizerElement, dif_neg hge, Nat.add_sub_cancel]
    using h

/-- The exact finite alternative consumed by the pair-placement proof. -/
theorem representative_mem_p₂_or_orderOf_obstruction (i : Fin 72) :
    representative i ∈ Seed.p₂ ∨ orderOf (obstruction i) = 5 := by
  by_cases hi : i.val < 6
  · exact Or.inl (representative_mem_p₂ i hi)
  · exact Or.inr (WordChecks.obstruction_order_five i (by omega))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement
