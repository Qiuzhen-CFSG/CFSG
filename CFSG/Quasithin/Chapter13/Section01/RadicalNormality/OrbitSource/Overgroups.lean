module
public import CFSG.Quasithin.Chapter13.Section01.RadicalNormality.OrbitSource
/-!
# Propagating canonical radical normality through every local overgroup

Embed the given local overgroup K of L₀ in a maximal local M. The intrinsic
embedding theorem makes a nonnormal canonical radical force an odd
linear-three quotient of M. Original faithfulness propagation and homogeneous
selection construct its actual orbit module, whose cubic ratio exceeds two.
The genuine earlier Section 3 orbit bound excludes that alternative. Restrict
normality from M to the original K. A.3.6 then makes K nonquasisimple, so the
original faithful nonquasisimple family is upward closed in L(G,T).

The same L₀, K, prime p and Ξₚ(L₀) are retained. The full model list of
12.2.2 is unnecessary for this step. The earlier 3.1.8/3.2.5 bound and
universal A.3.6, A.3.8 and A.4.10 remain named source obligations.
Source: Aschbacher--Smith, proof of Lemma 13.1.4, p.867.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter1.XiEmbedding Chapter12.Section02
open Chapter1.Section02 Chapter1.Section02.Adequate
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
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

include h hA38 hA410
private theorem faithful_normalized_overgroup
    {L₀ K : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T)
    (hK : K ∈ L G T) (hLK : L₀ ≤ K) :
    K ∈ MainForward.faithfulLocalComponents T ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) := by
  have hl := ((mem_faithfulLocalComponents_iff T L₀).mp hL.1).1
  have hTL := radicalLocal_invariant_of_A38 hA38 hl
    (uniqueness_local_quotient_sqtk h.simpleQTKE hl.2.2) hL.2
  have hTK := local_chain_normalizes hl hK hLK hTL
  have he : (T : Subgroup G) ⊓ normalizer (L₀ : Set G) =
      (T : Subgroup G) ⊓ normalizer (K : Set G) := by
    rw [inf_eq_left.mpr hTL, inf_eq_left.mpr hTK]
  exact ⟨(faithful_chain_of_A410_of_normalizer_eq T (h.simpleQTKE.evenCharacteristic T)
    hA410 hL.1 hK hLK he).2, hTK⟩

include hA36 hbound
/-- The same canonical radical is normal in every original local overgroup. -/
theorem Hypothesis1311.radical_normal_in_overgroup_of_orbit_bound
    {L₀ K : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T)
    (hK : K ∈ L G T) (hLK : L₀ ≤ K)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀))) :
    ((XiP p L₀).subgroupOf K).Normal := by
  obtain ⟨M, hM, hKM⟩ := exists_mem_LStar_ge hK
  have hLM := hLK.trans hKM
  have hn : ((XiP p L₀).subgroupOf M).Normal := by
    rcases RadicalNormality.source_normal_or_linear_three h.simpleQTKE hA36 hA38
      hL hM.1 hLM ho hd with hn | ⟨hq, hm, _⟩
    · exact hn
    obtain ⟨hf, hTM⟩ := faithful_normalized_overgroup h hA38 hA410 hL hM.1 hLM
    have hfM : FaithfulMaximalLocal T M :=
      ⟨hM, ((mem_faithfulLocalComponents_iff T M).mp hf).2⟩
    have h12 := h.hypothesis1223 hfM hq
    obtain ⟨V, ⟨D⟩⟩ := h12.toHypothesis1221.exists_chosen_of_normalizes hTM
    have hl := ((mem_faithfulLocalComponents_iff T L₀).mp hL.1).1
    have hp3 := (XiP_oddQuotient_of_A36 hA36 hl
      (uniqueness_local_quotient_sqtk h.simpleQTKE hl.2.2) hL.2 ho hd).1
    exact (linear_three_whole_orbit_excluded D h12.toHypothesis1221 Fact.out ho hp3 hm
      (hbound M V h12 D)).elim
  have hXiM : XiP p L₀ ≤ M := (XiP_le p L₀).trans hLM
  exact normal_subgroupOf_of_le_normalizer
    (hKM.trans ((normal_subgroupOf_iff_le_normalizer hXiM).mp hn))

/-- The original nonquasisimple faithful family is upward closed in L(G,T),
using the genuine earlier whole-orbit bound. -/
theorem Hypothesis1311.nonquasisimpleFaithful_overgroup_of_orbit_bound
    {L₀ K : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T)
    (hK : K ∈ L G T) (hLK : L₀ ≤ K) :
    K ∈ nonquasisimpleFaithful T := by
  obtain ⟨p, hp, ho, _, hd, _, _⟩ :=
    exists_odd_radical_source h.simpleQTKE hA36 hL
  let : Fact p.Prime := ⟨hp⟩
  have hn := h.radical_normal_in_overgroup_of_orbit_bound hA36 hA38 hA410 hbound
    hL hK hLK ho hd
  exact ⟨(faithful_normalized_overgroup h hA38 hA410 hL hK hLK).1,
    source_overgroup_not_quasisimple h.simpleQTKE hA36 hL hK hLK ho hd hn⟩
end CFSG.Quasithin.Chapter13.Section01
