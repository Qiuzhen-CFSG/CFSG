module

public import Theory.GroupTheory.OddPrimeSectionCentralizers

/-!
# Cyclic prime-core centralizers in rank-two sections

This is clause (1) of Aschbacher–Smith, Lemma A.1.31, printed pp.27–28.
The rank bound is on H before quotienting by N. The surjective theorem
applies to the literal quotient map; an explicit multiplicative equivalence
identifies its internal centralizer with the ambient intersection below.
Clauses (2) and (3) belong to the separate SectionRank assembly.
-/

public section

namespace CFSG.Quasithin.ChapterA
open Subgroup Theory.GroupTheory

/-- Source A.1.31(1): every nontrivial two-subgroup of the characteristic-p
quotient has cyclic centralizer in its p-core. -/
theorem lemma_A_1_31_1
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {N : Subgroup H} [N.Normal]
    (hrank : primeRank p H ≤ 2) (hp : Odd p)
    (hF : generalizedFitting (H ⧸ N) = pCore p (H ⧸ N))
    (R : Subgroup (H ⧸ N)) (hR : IsPGroup 2 R) (hne : R ≠ ⊥) :
    IsCyclic (pCore p (H ⧸ N) ⊓ centralizer (R : Set (H ⧸ N)) : Subgroup (H ⧸ N)) := by
  let : IsCyclic ((centralizer (R : Set (H ⧸ N))).subgroupOf (pCore p (H ⧸ N))) :=
    cyclic_primeCore_centralizer_of_surjective_rank_le_two hp hrank
      (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hF R hR hne
  exact isCyclic_of_surjective (primeCoreCentralizerEquivInf p R).toMonoidHom
    (primeCoreCentralizerEquivInf p R).surjective

end CFSG.Quasithin.ChapterA
