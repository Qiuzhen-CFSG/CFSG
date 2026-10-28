module

public import CFSG.Quasithin.Chapter11.Defs
public import CFSG.Quasithin.Chapter11.Section01To02.NormalizerSteps

/-!
# Chapter 11: legacy helpers and source-facing prerequisites

The historical source-numbered declarations in this file are elementary
projections or identity implications, not proofs of the correspondingly numbered
Aschbacher–Smith results. Their public signatures are retained for compatibility.
The old alternatives contain no group isomorphisms, and the old conclusion
record is not the terminal conclusion of either section.

The imported `SourceDefs` and `NormalizerSteps` modules provide genuine local
definitions and elementary steps. The source results 11.1.1–11.2.5 remain
unfinished; their recognition, module, pushing-up, and weak-closure premises
still need to be proved from the Chapter 11 counterexample setup.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed pp.760–770.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter11

open Subgroup

variable {G : Type*} [Group G]

theorem tinvariant_iff_le_normalizer {T U : Subgroup G} :
    TInvariant T U ↔ T ≤ NG U := by
  rfl

theorem invariant_subspace_le_normalizer {T V : Subgroup G}
    (U : InvariantSubspace T V) : T ≤ NG U.carrier := U.invariant

theorem mem_NG_iff {U : Subgroup G} {g : G} :
    g ∈ NG U ↔ ∀ x : G, x ∈ U ↔ g * x * g⁻¹ ∈ U := by
  exact Subgroup.mem_normalizer_iff

/-- Legacy record projection; not source Lemma 11.1.1. -/
theorem lemma_11_1_1 {H L : Subgroup G} {n : ℕ}
    (h : ComponentEmbedding H L n) :
    ∃ K : Subgroup G, L ≤ K ∧ K.Normal ∧ K ≤ H ∧
      ComponentAlternative n := by
  exact ⟨h.K, h.le_component, h.normal, h.contained, h.alternative⟩

/-- Legacy labels, always inhabited by `equal`; not a refinement theorem. -/
inductive RefinedNormalizerAlternative (n : ℕ) : Prop where
  | equal
  | sl2Prime (p : ℕ) (prime : p.Prime)
  | l2Prime (p : ℕ) (prime : p.Prime)
  | pgl3Four

/-- Legacy record with ambient normality and no quotient-model conditions. -/
structure RefinedNormalizerCertificate (H L : Subgroup G) (n : ℕ) where
  K : Subgroup G
  le_component : L ≤ K
  normal : K.Normal
  contained : K ≤ H
  alternative : RefinedNormalizerAlternative n

/-- Legacy record projection; not source Proposition 11.1.2. -/
theorem proposition_11_1_2 {H L : Subgroup G} {n : ℕ}
    (h : RefinedNormalizerCertificate H L n) :
    ∃ K : Subgroup G, L ≤ K ∧ K.Normal ∧ K ≤ H ∧
      RefinedNormalizerAlternative n := by
  exact ⟨h.K, h.le_component, h.normal, h.contained, h.alternative⟩

/-- Legacy uniqueness among all centralizing subgroups. Its hypotheses force
`K = ⊥`; source 11.1.3 instead concerns noncentralizing C-components. -/
theorem lemma_11_1_3 {H V K : Subgroup G}
    (hK : K ≤ H) (hKcentral : K ≤ centralizer (V : Set G))
    (hUnique : ∀ C : Subgroup G, C ≤ H → C ≤ centralizer (V : Set G) → C = K) :
    ∃! C : Subgroup G, C ≤ H ∧ C ≤ centralizer (V : Set G) := by
  refine ⟨K, ⟨hK, hKcentral⟩, ?_⟩
  intro C hC
  exact hUnique C hC.1 hC.2

/-- Legacy identity implication; not either containment in source 11.1.4. -/
theorem lemma_11_1_4 {T V U : Subgroup G}
    (_hU : U ≤ V) (hT : T ≤ NG U) : T ≤ NG U := by
  exact hT

/-- Legacy identity implication; does not express source 11.1.5. -/
theorem lemma_11_1_5 {T V R1 M L : Subgroup G}
    (h : NG R1 ≤ M ∨ (∃ _hV : V = V ⊔ M, ∃ _hBlock : Prop,
      centralizer (T : Set G) ≤ L)) :
    NG R1 ≤ M ∨ (∃ _hV : V = V ⊔ M, ∃ _hBlock : Prop,
      centralizer (T : Set G) ≤ L) := by
  exact h

/-- Legacy numerical alternatives, omitting the module assertions of 11.2.1. -/
inductive Lemma1121Alternative (n k : ℕ) : Prop where
  | small (h : k ≤ n)
  | sl3Double (h : k ≤ 2 * n)

/-- Legacy elementary helper; no source-completion claim. -/
theorem lemma_11_2_1 {n k : ℕ} (h : Lemma1121Alternative n k) :
    k ≤ n ∨ k ≤ 2 * n := by
  cases h with
  | small h => exact Or.inl h
  | sl3Double h => exact Or.inr h

/-- Legacy record projection; not a bound on the actual weak-closure parameters. -/
theorem lemma_11_2_2 {T M V : Subgroup G} (d : WeakClosureData T M V) :
    d.s ≤ d.r ∧ d.weakClosure ≤ NG V := by
  exact ⟨d.r_lower, d.weakClosure_le⟩

/-- Legacy elementary helper; no source-completion claim. -/
theorem lemma_11_2_3 {T V : Subgroup G} {U : Subgroup G}
    (_hU : U ≤ V) (hT : T ≤ NG U) : T ≤ NG U := by
  exact hT

/-- Legacy elementary helper; no source-completion claim. -/
theorem lemma_11_2_4 {_T V : Subgroup G} {W : Subgroup G}
    (hW : W ≤ NG V) (_hcomm : W ≤ centralizer (V : Set G)) :
    W ≤ NG V := by
  exact hW

/-- Legacy elementary helper; no source-completion claim. -/
theorem lemma_11_2_5 {_T V H : Subgroup G}
    (hH : H ≤ NG V) : H ≤ NG V := hH

/-- Legacy collection of elementary bounds; not a source terminal conclusion. -/
structure Section01To02Conclusion where
  T : Subgroup G
  normalizerV1 : Subgroup G
  normalizerV2 : Subgroup G
  v1_invariant : T ≤ normalizerV1
  v2_invariant : T ≤ normalizerV2
  weakClosureParameter : ℕ
  weakClosureBound : ℕ
  parameter_le : weakClosureParameter ≤ weakClosureBound

/-- Legacy elementary helper; no source-completion claim. -/
theorem section01To02_conclusion {T V V1 V2 : Subgroup G}
    (d : WeakClosureData T T V)
    (hV1 : T ≤ NG V1) (hV2 : T ≤ NG V2) :
    Nonempty (Section01To02Conclusion (G := G)) := by
  exact ⟨
    { T := T
      normalizerV1 := NG V1
      normalizerV2 := NG V2
      v1_invariant := hV1
      v2_invariant := hV2
      weakClosureParameter := d.s
      weakClosureBound := d.r
      parameter_le := d.r_lower }⟩

end CFSG.Quasithin.Chapter11
