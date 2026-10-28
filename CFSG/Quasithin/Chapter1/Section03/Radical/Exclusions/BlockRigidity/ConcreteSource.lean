module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.CenterlessSource
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.SourceC19
/-!
# The actual binary-block exclusion in 1.3.8

The centerless two-factor argument and the proved guarded C.1.9 discharge
both earlier algebraic inputs to the original residual-factor construction.
The original odd trace then contradicts the normalizer's factor permutation.
No A.1.15 or block-commutation callback remains; the ambient Configuration
and original binary-block embedding are still the source hypotheses.
Source: Aschbacher--Smith, proof of 1.3.8, printed p.514.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalExclusions
open BlockRigidity
universe u
variable {G : Type u} [Group G]
private theorem conjugate_pair_permutation {A B : Subgroup G} {d : G}
    (h : (A.conjBy d = A ∨ A.conjBy d = B) ∧
      (B.conjBy d = A ∨ B.conjBy d = B)) :
    (A.conjBy d = A ∧ B.conjBy d = B) ∨
      (A.conjBy d = B ∧ B.conjBy d = A) := by
  have hi : Function.Injective (fun C : Subgroup G => C.conjBy d) :=
    map_injective (MulAut.conj d).injective
  rcases h with ⟨ha | ha, hb | hb⟩
  · have he : A = B := hi (ha.trans hb.symm)
    exact Or.inl ⟨ha, hb.trans he⟩
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · have he : A = B := hi (ha.trans hb.symm)
    exact Or.inl ⟨ha.trans he.symm, hb⟩

/-- The actual residual factors, their normalizer permutation, and their odd
trace in the final paragraph of 1.3.8. Every factor is explicitly identified;
each normalizer element fixes both factors or swaps them. -/
theorem BinaryBlockEmbedding.concrete_factor_pair_source [Finite G]
    (T : Sylow 2 G) {p : ℕ} {X P L₀ M H₀ K : Subgroup G}
    (h : BinaryBlockEmbedding p T X P H₀ K)
    (hc : Configuration p T X P L₀ M)
    (hH : H₀ ∈ HOver G (T : Set G))
    (h114 : HOver G (T : Set G) ⊆ He G) :
    ∃ t : G, t ∈ (T : Subgroup G) ⊓ normalizer P ∧ t ∉ normalizer K ∧
      let W := blockResidual X K
      let Z_X := (center X).map X.subtype
      let A := W ⊔ Z_X
      let B := W.conjBy t ⊔ Z_X
      X = W ⊔ W.conjBy t ∧
      W.conjBy t = blockResidual X (K.conjBy t) ∧
      ⁅W, W.conjBy t⁆ = ⊥ ∧
      (∀ d ∈ normalizer (X : Set G),
        (A.conjBy d = A ∧ B.conjBy d = B) ∨
          (A.conjBy d = B ∧ B.conjBy d = A)) ∧
      P ⊓ A = P ⊓ K := by
  obtain ⟨t, ht, htn, hgen, hres⟩ := h.residual_factorization
  have hcomm := blockResidual_commute (X := X)
    (conjugate_commute sourceC19 h h114 hH ht.1 htn)
  obtain ⟨hW, hWt⟩ :=
    h.centerFactors_directlyIndecomposable_of_source T hc hH h114 ht htn
  have hpair := centerFactor_pair_of_centerless hgen.symm hcomm hW hWt
    (xi_center_quotient_center_eq_bot h114 hc.xi)
  exact ⟨t, ht, htn, hgen, hres, hcomm,
    fun d hd => conjugate_pair_permutation (hpair d hd), h.odd_trace hc h114⟩


variable [Finite G]
theorem BinaryBlockEmbedding.false_of_centerless_factors
    (T : Sylow 2 G) {p : ℕ} {X P L₀ M H₀ K : Subgroup G}
    (h : BinaryBlockEmbedding p T X P H₀ K)
    (hc : Configuration p T X P L₀ M)
    (hH : H₀ ∈ HOver G (T : Set G))
    (h114 : HOver G (T : Set G) ⊆ He G) : False := by
  obtain ⟨t, _, _, _, _, _, hpair, htrace⟩ :=
    h.concrete_factor_pair_source T hc hH h114
  have hn : L₀ ≤ normalizer (X : Set G) := by
    rw [← hc.normalizer_radical, hc.normalizer_local]
    exact L₀.le_normalizer
  exact h.no_factor_pair hc _ _
    (fun d hd => (hpair d (hn hd)).imp And.left And.left) htrace
end CFSG.Quasithin.Chapter1.RadicalExclusions
