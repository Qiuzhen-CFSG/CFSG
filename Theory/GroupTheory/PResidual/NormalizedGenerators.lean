module

public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Residuals of normalized generating pairs

Two p-perfect subgroups normalized by a p-subgroup generate precisely the
p-residual of their common overgroup. A commutator bound on both generators
therefore extends to the residual, provided they normalize the bounding layer.

The residual equality follows from its universal property and the p-group
quotient. The commutator bound uses the subgroup of elements centralizing the
actor modulo the layer.

Source application: Aschbacher–Smith, Lemma 15.4.23, printed p.1165,
with `p = 2`, generators `L₁′, L₂`, and layer `O₂(L₁)`.
-/

open Subgroup
variable {G : Type*} [Group G]

/-- A normalized pair of p-perfect generators generates the p-residual. -/
public theorem Subgroup.pResidual_eq_sup_of_normalized_generators {p : ℕ} (A B T : Subgroup G)
    (hA : IsPPerfect p A) (hB : IsPPerfect p B) (hT : IsPGroup p T)
    (hTA : T ≤ normalizer (A : Set G)) (hTB : T ≤ normalizer (B : Set G))
    (hgen : (A ⊔ B) ⊔ T = ⊤) : pResidual p G = A ⊔ B := by
  have hnormal : (A ⊔ B).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le (A ⊔ B).le_normalizer
      ((le_inf hTA hTB).trans (normalizer_inf_normalizer_le_normalizer_sup A B))
  let := hnormal
  apply le_antisymm
  · exact sInf_le ⟨hnormal, isPGroup_quotient_of_sup_eq_top (A ⊔ B) T hT hgen⟩
  · exact sup_le (le_pResidual_of_isPPerfect A hA) (le_pResidual_of_isPPerfect B hB)

/-- A common commutator bound extends from the generators to the residual. -/
public theorem Subgroup.commutator_pResidual_le_of_normalized_generators {p : ℕ} (A B T L N : Subgroup G)
    (hA : IsPPerfect p A) (hB : IsPPerfect p B) (hT : IsPGroup p T)
    (hTA : T ≤ normalizer (A : Set G)) (hTB : T ≤ normalizer (B : Set G))
    (hgen : (A ⊔ B) ⊔ T = ⊤)
    (hAN : A ≤ normalizer (N : Set G)) (hBN : B ≤ normalizer (N : Set G))
    (hAL : ⁅A, L⁆ ≤ N) (hBL : ⁅B, L⁆ ≤ N) : ⁅pResidual p G, L⁆ ≤ N := by
  rw [pResidual_eq_sup_of_normalized_generators A B T hA hB hT hTA hTB hgen]
  exact (commutator_mono
    (sup_le (le_commutatorPreimage hAN hAL) (le_commutatorPreimage hBN hBL)) le_rfl).trans
      (commutator_commutatorPreimage_le (normalizer (N : Set G)) L N le_rfl)
