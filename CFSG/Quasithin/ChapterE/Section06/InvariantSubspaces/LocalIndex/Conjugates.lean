module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Reduction

/-!
# Conditional assembly of the conjugate-module calculation

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.6(1)–(5)
and C.5.7, printed pp.155–160.

The three inputs separate the product calculation from the natural and
alternating-five elementary-family calculations. Frattini invariance and
identification of the two Sylow-invariant members are proved in `Reduction`.
No index assertion is assumed. The theorem here remains conditional until
all three inputs have been constructed from the published local hypotheses.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates

open Subgroup
universe u
variable {G : Type u} [Group G] {K : GroupClass.{u}}

/-- Assembly of the conjugate calculation from the three independent inputs.
The module/extension calculations are still explicit premises; this theorem
alone does not establish C.5.6 or the local index theorem. -/
theorem conjugateInput_of_calculations [Finite G]
    (hfactor : FactorizationInput (G := G) K)
    (hnatural : NaturalFamilyInput (G := G) K)
    (halternating : AlternatingFamilyInput (G := G) K) : ConjugateInput (G := G) K := by
  intro A H R L h hb x hx hnc
  have hp := hfactor A H R L h hb x hx hnc
  refine ⟨frattini_invariant_of_factorization h hb hx hp, ?_⟩
  intro hf
  have hfamily : Q R L ∈ Stellmacher.elementaryAbelianMaxSubgroups (S R) ∧
      ∀ E ∈ invariantFamily R (S R), E = Q R L ∨ E = opposite R L x := by
    rcases h.block with hL2 | hA3 | hA5
    · have he := hnatural A H R L h hb (Or.inl hL2) x hx hnc hp hf
      refine ⟨by rw [he]; simp, ?_⟩
      intro E hE
      simpa only [he, Set.mem_insert_iff, Set.mem_singleton_iff] using hE.1
    · have he := hnatural A H R L h hb (Or.inr hA3) x hx hnc hp hf
      refine ⟨by rw [he]; simp, ?_⟩
      intro E hE
      simpa only [he, Set.mem_insert_iff, Set.mem_singleton_iff] using hE.1
    · obtain ⟨E, r, _, _, _, he, hEn, hErn⟩ :=
        halternating A H R L h hb hA5 x hx hnc hp hf
      refine ⟨by rw [he]; simp, ?_⟩
      intro B hB
      have hBm := hB.1
      rw [he] at hBm
      rcases Set.mem_insert_iff.mp hBm with hBq | hBm
      · exact Or.inl hBq
      rcases Set.mem_insert_iff.mp hBm with hBo | hBm
      · exact Or.inr hBo
      rcases Set.mem_insert_iff.mp hBm with hBE | hBE
      · exact False.elim (hEn (hBE ▸ hB.2))
      · exact False.elim (hErn ((Set.mem_singleton_iff.mp hBE) ▸ hB.2))
  exact (invariant_pair_of_candidates h hb hx hnc hfamily.1 hfamily.2).2

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates
end
