module
public import CFSG.Quasithin.Chapter13.Section01.RadicalNormality.MaximalSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Selection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
/-!
# A genuine chosen module in the remaining 13.1.4 obstruction

The intrinsic embedding theorem leaves a maximal overgroup K whose original
two-core quotient is an odd linear-three group. Its already proved
T-normalization and literal Hypothesis 12.2.3 construct a homogeneous chosen
module by the normalized source selection theorem. Thus the remaining
classification step can use the actual K, T and reduced conjugation module;
no module witness or global normalization result is an additional premise.

This is the input to the unresolved earlier module-classification elimination,
not a claim that the linear-three alternative has already been excluded.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
Lemma 13.1.4, p.867, and Theorem 12.2.2, pp.794--795.
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

/-- The nonnormal branch comes with a constructed original chosen module. -/
theorem Hypothesis1311.exists_normal_radical_or_linear_chosen_source
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
            LinearThreeModel p (XiQuotient K) ∧ p ^ 2 ∣ Nat.card (XiQuotient K) ∧
            ∃ V : Subgroup G, Nonempty (ChosenModule T K V))) := by
  obtain ⟨K, hK, hLK, hf, hTK, p, hp, ho, hp3, hd, hne, ha⟩ :=
    h.exists_normal_radical_or_linear_source hA36 hA38 hA410 hL
  refine ⟨K, hK, hLK, hf, hTK, p, hp, ho, hp3, hd, hne, ?_⟩
  rcases ha with ha | ⟨h12, hm, hdiv⟩
  · exact Or.inl ha
  · obtain ⟨V, ⟨D⟩⟩ := h12.toHypothesis1221.exists_chosen_of_normalizes hTK
    exact Or.inr ⟨h12, hm, hdiv, V, ⟨D⟩⟩
end CFSG.Quasithin.Chapter13.Section01
