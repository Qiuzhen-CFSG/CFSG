module

public import CFSG.Quasithin.ChapterF.Section01
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# Generation and faithfulness in the solvable amalgam

The amalgam preceding Lemma 14.2.21 lives in `G₀ = H ⊔ (Y ⊔ T)`.
Restricting the three subgroups to `G₀` proves generation without assuming
`G₀ = G`. A normal subgroup of the common two-subgroup lies in `O₂(G₀)`;
the unique maximal two-local overgroup of `Y T` makes this core trivial.

These results establish the conditions recorded by Chapter F's current
`WeakBNPair` interface. They do not establish the rank-one quotient and
characteristic-two conditions of source Hypothesis F.1.1. The intersection
condition must still be supplied by the source-local analysis.

The final lemma records how rigidity `H = Mc` gives `M = Y T` from the
centralizer decomposition: `C_M(V) ≤ C_G(Z) = Mc`, so `C_M(V) ≤ T`.
Rigidity itself remains a separate, substantive assertion.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed pp. 988–989, Lemma 14.2.21 and its setup.
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam

open CFSG.Quasithin.ChapterF

private theorem faithful_of_core {G : Type*} [Group G]
    (P₁ B P₂ : Subgroup G) (hgen : P₁ ⊔ P₂ = ⊤)
    (hB : IsPGroup 2 B) (hcore : pCore 2 G = ⊥) :
    ∀ N : Subgroup G, (N.subgroupOf (P₁ ⊔ P₂)).Normal → N ≤ B → N = ⊥ := by
  intro N hN hNB
  have hnormal : N.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    rw [← hgen]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (show N ≤ P₁ ⊔ P₂ by
      rw [hgen]; exact le_top)).mp hN
  have hle : N ≤ pCore 2 G := le_sSup ⟨hnormal, hB.to_le hNB⟩
  exact bot_unique (hcore ▸ hle)

/-- Generation and faithfulness in the generated subgroup, from its trivial
two-core and a two-group intersection. No maximality of `H` is assumed. -/
public theorem weak_bn_pair_in_sup_of_twoCore_eq_bot
    {G : Type*} [Group G] (H T A : Subgroup G)
    (hint : H ⊓ A = T) (hT : IsPGroup 2 T)
    (hcore : pCore 2 (H ⊔ A : Subgroup G) = ⊥) :
    WeakBNPair (H ⊔ A : Subgroup G)
      (H.subgroupOf (H ⊔ A)) (T.subgroupOf (H ⊔ A)) (A.subgroupOf (H ⊔ A)) := by
  have hgen : H.subgroupOf (H ⊔ A) ⊔ A.subgroupOf (H ⊔ A) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  refine ⟨?_, ?_, faithful_of_core _ _ _ hgen hT.comap_subtype hcore⟩
  · simpa only [Subgroup.closure_union, Subgroup.closure_eq] using hgen
  · change (H ⊓ A).comap (H ⊔ A).subtype = T.comap (H ⊔ A).subtype
    rw [hint]

/-- Apply unique two-local overgroup control to construct the faithful
amalgam inside `G₀`, once the local intersection has been established. -/
public theorem weak_bn_pair_in_generated
    {G : Type*} [Group G] [Finite G] (H Y T M : Subgroup G)
    (hint : H ⊓ (Y ⊔ T) = T) (hT : IsPGroup 2 T)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → Y ⊔ T ≤ K → K = M)
    (hHM : ¬ H ≤ M) :
    WeakBNPair (H ⊔ (Y ⊔ T) : Subgroup G)
      (H.subgroupOf (H ⊔ (Y ⊔ T))) (T.subgroupOf (H ⊔ (Y ⊔ T)))
      ((Y ⊔ T).subgroupOf (H ⊔ (Y ⊔ T))) := by
  apply weak_bn_pair_in_sup_of_twoCore_eq_bot H T (Y ⊔ T) hint hT
  rw [sup_comm H]
  exact Theory.GroupTheory.twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup
    (Y ⊔ T) H M hunique hHM

/-- The factorization following rigidity in Lemma 14.2.21. The decomposition
input retains the centralizer factor, which the proof eliminates. -/
public theorem m_eq_yt_of_rigidity
    {G : Type*} [Group G] (H M Mc Y T Z V : Subgroup G)
    (hHMc : H = Mc) (hint : H ⊓ M = T)
    (hMc : Mc = Subgroup.centralizer (Z : Set G)) (hZV : Z ≤ V)
    (hdecomp : M ≤ (Y ⊔ T) ⊔ (M ⊓ Subgroup.centralizer (V : Set G)))
    (hY : Y ≤ M) (hT : T ≤ M) : M = Y ⊔ T := by
  have hC : M ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
    rw [← hint, hHMc, hMc]
    exact le_inf (inf_le_right.trans (Subgroup.centralizer_le hZV)) inf_le_left
  apply le_antisymm _ (sup_le hY hT)
  exact hdecomp.trans (sup_le le_rfl (hC.trans le_sup_right))

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
