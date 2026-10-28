module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Covering
public import CFSG.Quasithin.ChapterA.Section02.QuotientRanks
public import Theory.Quasithin.CoprimeRank
public import Theory.Quasithin.NormalTwoRank
public import Theory.GroupTheory.GeneralizedFitting.LayerImages

/-!
# The two-core and rank obstruction in a minimal counterexample

Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.10 and
A.2.14, printed pp.35 and 37. The quotient-rank inequalities force the
semisimple offending section to have rank greater than two. If O₂(G) were
nontrivial, G itself would be a two-local, bounding all its odd-prime ranks.
Induction on G/O₂(G) bounds the image of the semisimple section. Coprime
kernel rank preservation then contradicts the offending section's rank.

The quotient maps here are literal induced maps by the image of O₂(G);
no ambient normality is imposed on the original section's numerator.
-/

public section

open Theory.GroupTheory Subgroup
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- A.2.14: the offending semisimple section has ordinary p-rank greater than two. -/
theorem lemma_A_2_14 (h : CounterexampleToTheoremA K G S p)
    (ih : TheoremAOnProperSections K G) : 2 < primeRank p S := by
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  have ho : p ≠ 2 := by
    rintro rfl
    exact (by decide : ¬ Odd 2) h.2.2.2.2.2.1
  apply lt_of_not_ge
  intro hr
  apply h.2.2.2.2.2.2
  refine ⟨.inl ⟨?_, isQuasithin_iff_twoLocalPrimeRank.mp h.1 p
    h.2.2.2.2.1 h.2.2.2.2.2.1⟩, fun _ => ?_⟩
  · exact TwoLocalPrimeRank.le_of_surjective_of_target_le_two ho f hf
      ((twoLocalPrimeRank_le_primeRank p).trans hr)
  · exact PrimeRank.le_of_surjective_of_target_le_two ho f hf hr

/-- A.2.10: the two-core of a minimal counterexample to A vanishes. -/
theorem lemma_A_2_10 (h : CounterexampleToTheoremA K G S p)
    (ih : TheoremAOnProperSections K G) : pCore 2 G = ⊥ := by
  by_contra hO
  have hG : IsStronglyQuasithin G := fun r hr ho =>
    Theory.Quasithin.primeRank_le_two_of_normal_two_subgroup h.1 (pCore 2 G)
      hO pCore_isPGroup r hr ho
  have hQ : IsStronglyQuasithin (G ⧸ pCore 2 G) := by
    intro r hr ho
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup).trans (hG r hr ho)
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  let N := (pCore 2 G).map f
  let : N.Normal := Subgroup.Normal.map inferInstance f hf
  let q := QuotientGroup.map (pCore 2 G) N f (Subgroup.le_comap_map _ _)
  have hq : Function.Surjective q := QuotientGroup.map_surjective_of_surjective (pCore 2 G) N f
    ((QuotientGroup.mk'_surjective N).comp hf) _
  have hS : IsSemisimple (S ⧸ N) :=
    componentLayer_eq_top_of_surjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) h.2.2.2.1
  have hA := ih (G ⧸ pCore 2 G) (IsProperSectionOf.quotient _ hO)
  have hb := hA.stronglyQuasithin_section hQ (h.2.1.quotient _)
    (IsSectionOf.of_surjective q hq) hS
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  have he := primeRank_quotient_eq_of_isTwoGroup p h.2.2.2.2.2.1 N
    (pCore_isPGroup.map f)
  have hsle : primeRank p S ≤ 2 := he ▸ hb p h.2.2.2.2.1 h.2.2.2.2.2.1
  exact (not_lt_of_ge hsle) (lemma_A_2_14 h ih)

end CFSG.Quasithin.ChapterA.Section02
