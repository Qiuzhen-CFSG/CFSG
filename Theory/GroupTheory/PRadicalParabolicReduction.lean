module

public import Theory.GroupTheory.PRadicalSubgroupFusion
public import Theory.GroupTheory.RadicalNormalizerControl

/-!
# Identifying p-radical subgroups inside normal p-subgroups

Suppose `R` is p-radical, `R ≤ U`, and `N(R) ≤ P ≤ N(U)`, where `U`
is a p-group. The radical normalizer-control lemma gives `U ≤ R`; hence
`R = U` and `N(R) = P`. For Borel--Tits, `P` is a parabolic and `U`
its unipotent radical. The geometric existence of such a parabolic is
a separate input, not asserted in this module.

Source: GLS, *The Classification of the Finite Simple Groups*, volume 3,
Corollary 3.1.5, using the normalizer condition for finite p-groups.
-/

namespace SubgroupFusion

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A normal p-subgroup containing a p-radical subgroup and normalized by its
normalizer must equal it. The intermediate overgroup is then its normalizer. -/
public theorem pRadical_eq_of_normalizer_le
    {R U P : Subgroup G} (hR : IsPGroup p R)
    (hrad : normalizerPCore p R ≤ R) (hU : IsPGroup p U)
    (hRU : R ≤ U) (hNP : Subgroup.normalizer (R : Set G) ≤ P)
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) :
    R = U ∧ Subgroup.normalizer (R : Set G) = P := by
  have hUR : U ≤ R :=
    Subgroup.le_of_normalizer_le_normalizer_of_pCore_normalizer_le R U
      hR hU hrad (hNP.trans hPU)
  have heq : R = U := le_antisymm hRU hUR
  refine ⟨heq, le_antisymm hNP ?_⟩
  simpa only [heq] using hPU

/-- The finite Borel--Tits reduction, including containment of the chosen Sylow
subgroup. Geometric applications supply `P`, its radical `U`, the two
containments from Borel--Tits, and an ambient Sylow subgroup in `P`. -/
public theorem PRadicalFamily.eq_radical_and_normalizer
    {S : Sylow p G} {R U P : Subgroup G} (hR : PRadicalFamily S R)
    (hU : IsPGroup p U) (hRU : R ≤ U)
    (hNP : Subgroup.normalizer (R : Set G) ≤ P)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (T : Sylow p G) (hT : (T : Subgroup G) ≤ P) :
    R = U ∧ Subgroup.normalizer (R : Set G) = P ∧ (S : Subgroup G) ≤ P := by
  obtain ⟨heq, hnormalizer⟩ := pRadical_eq_of_normalizer_le
    (S.isPGroup'.to_le hR.2.1.1) hR.2.2 hU hRU hNP hPU
  refine ⟨heq, hnormalizer, ?_⟩
  rw [← hnormalizer] at hT ⊢
  exact extremal_le_normalizer_of_contains_sylow hR.2.1 T hT

end SubgroupFusion
