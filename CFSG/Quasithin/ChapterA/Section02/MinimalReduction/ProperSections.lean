module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.SimpleException
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Covering

/-!
# Proper-section control in simultaneous induction

Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.15,
printed pp.37–38. Apply A to a proper subgroup and bound its rank either
by the ambient ordinary rank or by its two-local rank. This gives strong
quasithinness of semisimple sections of proper two-locals, hence the C list.
For an arbitrary simple proper section, A either gives quasithinness and
inductive B, or its exceptional unitary witness directly supplies a B model.

Only the honest induction hypothesis on strictly smaller sections is used;
the proofs discharge the section-size and inherited K-group hypotheses.
-/

public section

open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G R : Type u}
    [Group G] [Group R] [Finite G] [Finite R]

/-- A.2.15(1): ordinary-rank control of semisimple proper sections. -/
theorem lemma_A_2_15_1 (ih : TheoremsOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {M : Subgroup G} (hM : M ≠ ⊤) (hRM : IsSectionOf R M) (hR : IsSemisimple R)
    (r : ℕ) (hr : r.Prime) (ho : Odd r) (hrG : primeRank r G ≤ 2) :
    primeRank r R ≤ primeRank r M ∧ primeRank r M ≤ primeRank r G := by
  have hm := Theory.GroupTheory.primeRank_le_of_injective r M.subtype M.subtype_injective
  refine ⟨?_, hm⟩
  exact ((ih.subgroup M hM).1 (hG.subgroup M) (hK.subgroup M) R hRM hR r hr ho).2
    (hm.trans hrG)

/-- A.2.15(2): a proper two-local bounds every semisimple section rank. -/
theorem lemma_A_2_15_2 (ih : TheoremsOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {M : Subgroup G} (hM : M ≠ ⊤) (hlocal : IsTwoLocal M)
    (hRM : IsSectionOf R M) (hR : IsSemisimple R)
    (r : ℕ) (hr : r.Prime) (ho : Odd r) :
    primeRank r R ≤ primeRank r M ∧
      primeRank r M ≤ twoLocalPrimeRank r G ∧ twoLocalPrimeRank r G ≤ 2 := by
  have hloc := isQuasithin_iff_twoLocalPrimeRank.mp hG r hr ho
  refine ⟨?_, hlocal.primeRank_le r, hloc⟩
  exact ((ih.subgroup M hM).1 (hG.subgroup M) (hK.subgroup M) R hRM hR r hr ho).2
    ((hlocal.primeRank_le r).trans hloc)

/-- The two-local part of A.2.15(3), with both model-list conclusions. -/
theorem lemma_A_2_15_3_of_twoLocal (ih : TheoremsOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {M : Subgroup G} (hM : M ≠ ⊤) (hlocal : IsTwoLocal M)
    (hRM : IsSectionOf R M) (hR : IsSemisimple R)
    (hs : IsSimpleGroup R) (hna : ¬ IsMulCommutative R) :
    IsTheoremBModel R ∧ IsTheoremCModel R := by
  have hr : IsStronglyQuasithin R := by
    intro r hr ho
    obtain ⟨h₁, h₂, h₃⟩ := lemma_A_2_15_2 ih hG hK hM hlocal hRM hR r hr ho
    exact h₁.trans (h₂.trans h₃)
  have hm := (ih.section_of_proper_subgroup hM hRM).2.2 hs hna hr
    (hRM.isKGroup (hK.subgroup M))
  exact ⟨hm.toTheoremBModel, hm⟩

end CFSG.Quasithin.ChapterA.Section02

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G R : Type u}
    [Group G] [Group R] [Finite G] [Finite R]

/-- A.2.15(3): every nonabelian simple section of a proper subgroup is on the B list. -/
theorem lemma_A_2_15_3 (ih : TheoremsOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {M : Subgroup G} (hM : M ≠ ⊤)
    (hRM : IsSectionOf R M) (hR : IsSemisimple R)
    (hs : IsSimpleGroup R) (hna : ¬ IsMulCommutative R) : IsTheoremBModel R := by
  classical
  let := hs
  by_cases he : ∃ p, TheoremAException M R p
  · obtain ⟨p, hp⟩ := he
    exact hp.theoremBModel_of_simple
  · have hq : IsQuasithin R := by
      apply isQuasithin_iff_twoLocalPrimeRank.mpr
      intro p hp ho
      have hc := ((ih.subgroup M hM).1 (hG.subgroup M) (hK.subgroup M)
        R hRM hR p hp ho).1
      exact (hc.resolve_right (fun h => he ⟨p, h⟩)).1.trans
        (isQuasithin_iff_twoLocalPrimeRank.mp (hG.subgroup M) p hp ho)
    exact (ih.section_of_proper_subgroup hM hRM).2.1 hs hna hq
      (hRM.isKGroup (hK.subgroup M))

end CFSG.Quasithin.ChapterA.Section02
