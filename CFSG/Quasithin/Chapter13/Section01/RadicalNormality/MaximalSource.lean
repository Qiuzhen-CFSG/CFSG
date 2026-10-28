module
public import CFSG.Quasithin.Chapter13.Section01.RadicalNormality.Source
public import CFSG.Quasithin.Chapter13.Section01.SourceHypotheses

/-!
# The original 13.1 hypotheses at the radical-embedding branch

The maximal-overgroup construction preserves the original L and its canonical
Ξₚ(L). In the remaining linear-three branch, the same maximal K satisfies the
actual earlier Hypothesis 12.2.3. Thus the full seven-case theorem 12.2.2 can be
applied directly when its producer is completed; no independently chosen model,
Sylow subgroup, or faithful component must be aligned.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
Lemmas 13.1.2 and 13.1.4, pp.866--867.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.Adequate
open CFSG.Quasithin.Chapter1.XiEmbedding
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter13.Section01
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal source counterexample yields either a normal radical in a
maximal nonquasisimple faithful overgroup, or an actual 12.2.3 input with the
linear-three obstruction. No classification conclusion is a premise. -/
theorem Hypothesis1311.exists_normal_radical_or_linear_source
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    (hA410 : A410EarlierResult G)
    {L₀ : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T) :
    ∃ K ∈ LStar G T, L₀ ≤ K ∧ FaithfulMaximalLocal T K ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
        p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) ∧ XiP p L₀ ≠ ⊥ ∧
        ((((XiP p L₀).subgroupOf K).Normal ∧ K ∈ nonquasisimpleFaithful T) ∨
          (Hypothesis1223 KnownSimple.IsKnownSimple T K ∧
            LinearThreeModel p (XiQuotient K) ∧ p ^ 2 ∣ Nat.card (XiQuotient K))) := by
  obtain ⟨K, hK, hLK, hf, hTK, p, hp, ho, hp3, hd, hne, ha⟩ :=
    RadicalNormality.exists_maximal_source_alternative h.simpleQTKE hA36 hA38 hL hA410
  have hmax : FaithfulMaximalLocal T K :=
    ⟨hK, ((mem_faithfulLocalComponents_iff T K).mp hf).2⟩
  refine ⟨K, hK, hLK, hmax, hTK, p, hp, ho, hp3, hd, hne, ?_⟩
  rcases ha with ⟨hn, hq⟩ | ⟨hq, hm, hdiv⟩
  · exact Or.inl ⟨hn, hf, hq⟩
  · exact Or.inr ⟨h.hypothesis1223 hmax hq, hm, hdiv⟩

end CFSG.Quasithin.Chapter13.Section01
