module
public import CFSG.Quasithin.Chapter13.Section01.RadicalNormality.ChosenSource
public import CFSG.Quasithin.Chapter13.Section01.RadicalNormality.LinearOrbit.Full
/-!
# The canonical radical in the maximal-overgroup branch of 13.1.4

The intrinsic embedding theorem and source homogeneous selection construct
the same maximal overgroup, prime radical and actual chosen module. The full
orbit linear-three exclusion removes the only nonnormal alternative using
exactly the earlier source 3.1.8/3.2.5 cubic-ratio bound. The ambient 13.1.1
hypotheses, original Sylow subgroup and all inclusions are preserved.

The ratio bound is a genuine remaining earlier theorem owned by the Section
3 source assembly. It is not a model-classification certificate. The result
here is the maximal-overgroup normality step, not all clauses of 13.1.4 or
the later uniqueness theorem 13.1.7.
Source: Aschbacher--Smith, Lemma 13.1.4, pp.867--868.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter1.XiEmbedding Chapter12.Section02
open Chapter1.Section02 Chapter1.Section02.Adequate
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
/-- The maximal-overgroup branch of 13.1.4 now needs only the genuine earlier
3.1.8 bound on the original FSU orbit, not a seven-model classification. -/
theorem Hypothesis1311.exists_normal_radical_of_orbit_bound
    (h : Hypothesis1311 T)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    (hA410 : A410EarlierResult G)
    (hbound : ∀ (K W : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T K →
      ∀ D : ChosenModule T K W, cubicRatio D.orbitRepresentation ≤ 2)
    {L₀ : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T) :
    ∃ K ∈ LStar G T, L₀ ≤ K ∧ FaithfulMaximalLocal T K ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
        p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) ∧ XiP p L₀ ≠ ⊥ ∧
        ((XiP p L₀).subgroupOf K).Normal ∧ K ∈ nonquasisimpleFaithful T := by
  obtain ⟨K, hK, hLK, hf, hTK, p, hp, ho, hp3, hd, hne, ha⟩ :=
    h.exists_normal_radical_or_linear_chosen_source hA36 hA38 hA410 hL
  refine ⟨K, hK, hLK, hf, hTK, p, hp, ho, hp3, hd, hne, ?_⟩
  rcases ha with hn | ⟨h12, hm, _, W, ⟨D⟩⟩
  · exact hn
  · exact (linear_three_whole_orbit_excluded D h12.toHypothesis1221 hp ho hp3 hm
      (hbound K W h12 D)).elim
end CFSG.Quasithin.Chapter13.Section01
