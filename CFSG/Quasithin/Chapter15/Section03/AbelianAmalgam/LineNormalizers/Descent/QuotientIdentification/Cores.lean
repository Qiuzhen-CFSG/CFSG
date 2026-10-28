module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.QuotientIdentification.Thompson
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreRestriction

/-!
# Core and kernel comparisons for the original line groups

A relatively normal subgroup has two-core equal to its intersection with
the ambient two-core. Apply this in the original `G_E` to `X_E` and `Y_E`.
The restriction of the original quotient map therefore has exactly the
intrinsic two-core as kernel. For `C_G(E)`, the earlier containment
`Q_E ≤ C_G(E)` makes the two embedded cores equal.

These comparisons use the actual subgroup embeddings and intrinsic cores;
no core of the temporary normalizer appears.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification
variable {G : Type*} [Group G]

private theorem core_eq_inf_of_normalizes (A H : Subgroup G) (hAH : A ≤ H)
    (hn : H ≤ normalizer (A : Set G)) : A.pCoreIn 2 = A ⊓ H.pCoreIn 2 :=
  le_antisymm (le_inf (pCoreIn_le 2 A) (pCoreIn_mono_of_normalizes hAH hn))
    (inf_pCoreIn_le_of_le 2 hAH)

/-- The actual two-core of `C_G(E)` is the original `Q_E`. -/
theorem centralizer_twoCore (E : Subgroup G)
    (hQC : lineQ E ≤ centralizer (E : Set G)) :
    (centralizer (E : Set G)).pCoreIn 2 = lineQ E := by
  have hn : lineNormalizer E ≤ normalizer (centralizer (E : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (E : Set G))).mp
      inferInstance
  exact (core_eq_inf_of_normalizes _ _ (centralizer_le_normalizer (E : Set G)) hn).trans
    (inf_of_le_right hQC)

/-- Relative normality identifies the core of the original `X_E`. -/
theorem lineX_twoCore [Finite G] (E : Subgroup G) :
    (lineX E).pCoreIn 2 = lineX E ⊓ lineQ E :=
  core_eq_inf_of_normalizes _ _
    ((lineX_le_centralizer E).trans (centralizer_le_normalizer (E : Set G)))
    (lineNormalizer_le_normalizer_lineX E)

/-- The corresponding comparison for the relatively normal original `Y_E`. -/
theorem lineY_twoCore (Y E : Subgroup G)
    (hn : ((lineY Y E).subgroupOf (lineNormalizer E)).Normal) :
    (lineY Y E).pCoreIn 2 = lineY Y E ⊓ lineQ E :=
  core_eq_inf_of_normalizes _ _ ((lineY_le Y E).trans inf_le_right)
    ((normal_subgroupOf_iff_le_normalizer ((lineY_le Y E).trans inf_le_right)).mp hn)

/-- The original core quotient; it uses no temporary normalizer. -/
noncomputable def quotientMap (E : Subgroup G) :
    lineNormalizer E →* (lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) :=
  QuotientGroup.mk' (pCore 2 (lineNormalizer E))

/-- The map from an actual subgroup of `G_E` to the original core quotient. -/
noncomputable def restrictedQuotient (E A : Subgroup G) (hA : A ≤ lineNormalizer E) :
    A →* (lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) :=
  (quotientMap E).comp (inclusion hA)

/-- The restricted map's kernel is computed intrinsically from relative normality. -/
theorem restrictedQuotient_ker (E A : Subgroup G) (hA : A ≤ lineNormalizer E)
    (hn : (A.subgroupOf (lineNormalizer E)).Normal) :
    (restrictedQuotient E A hA).ker = pCore 2 A := by
  have hcore := core_eq_inf_of_normalizes A (lineNormalizer E) hA
    ((normal_subgroupOf_iff_le_normalizer hA).mp hn)
  have hm : (restrictedQuotient E A hA).ker.map A.subtype = A ⊓ lineQ E := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.property, ?_⟩
      have hq : inclusion hA a ∈ pCore 2 (lineNormalizer E) :=
        (QuotientGroup.eq_one_iff _).mp ha
      exact mem_map_of_mem (lineNormalizer E).subtype hq
    · rintro ⟨hx, y, hy, hyx⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      apply (QuotientGroup.eq_one_iff _).mpr
      have he : inclusion hA ⟨x, hx⟩ = y := Subtype.ext hyx.symm
      rwa [he]
  apply (map_injective A.subtype_injective)
  exact hm.trans hcore.symm

/-- The centralizer action kernel is its own intrinsic two-core. -/
theorem centralizer_quotient_ker (E : Subgroup G) :
    (restrictedQuotient E (centralizer (E : Set G))
      (centralizer_le_normalizer (E : Set G))).ker = pCore 2 (centralizer (E : Set G)) :=
  restrictedQuotient_ker E _ _ inferInstance

/-- The residual `X_E` has exactly its intrinsic two-core as quotient kernel. -/
theorem lineX_quotient_ker [Finite G] (E : Subgroup G) :
    (restrictedQuotient E (lineX E)
      ((lineX_le_centralizer E).trans (centralizer_le_normalizer (E : Set G)))).ker =
        pCore 2 (lineX E) :=
  restrictedQuotient_ker E _ _ (lineX_normal_in_lineNormalizer E)

/-- The residual `Y_E` has exactly its intrinsic two-core as quotient kernel. -/
theorem lineY_quotient_ker (Y E : Subgroup G)
    (hn : ((lineY Y E).subgroupOf (lineNormalizer E)).Normal) :
    (restrictedQuotient E (lineY Y E) ((lineY_le Y E).trans inf_le_right)).ker =
      pCore 2 (lineY Y E) := restrictedQuotient_ker E _ _ hn

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification
