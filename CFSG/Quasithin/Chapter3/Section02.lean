module

public import Theory.GroupTheory.AbelianCoreRecovery

/-!
# The Fundamental Setup: core recovery

Aschbacher--Smith, *The Classification of Quasithin Groups*, §3.2,
combined manuscript (1 March 2004), pp. 578--585.

The group-theoretic argument of Lemma 3.2.11 is established here from the
explicit core containment supplied by the preceding Fundamental Setup results.
The core of `M` is trapped between `O₂(L₀ T)` and `O₂(L₀)`, so the three cores
coincide. Maximal two-locality then identifies the normalizer; characteristic
two and abelianness identify the ambient centralizer. Equal conjugation images
give the final equality `M = L₀ T`.

The setup construction, module lists 3.2.5--3.2.9, fusion conclusions 3.2.10,
and solvable-family exclusions 3.2.13--3.2.14 remain to be assembled from
their preceding source results. No weakened predicate is called the FSU here.
-/

namespace CFSG.Quasithin.Chapter3.Section02

open Subgroup

/-- The core and centralizer argument of 3.2.11. In the source `H = L₀ T`,
`M = N_G(L₀)` and `V = O₂(H)`; the inclusion `V ≤ O₂(L₀)` is supplied by
the internal-module construction. -/
public theorem lemma_3_2_11_of_core_containment
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (L₀ H M V : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hHM : H ≤ M) (hL₀M : L₀ ≤ M) (hM : M = normalizer (L₀ : Set G))
    (hmax : IsMaximalTwoLocal M)
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hV : V = (pCore 2 H).map H.subtype)
    (hVL₀ : V ≤ (pCore 2 L₀).map L₀.subtype) (hne : V ≠ ⊥)
    [IsMulCommutative V] :
    (pCore 2 M).map M.subtype = V ∧
      normalizer (V : Set G) = M ∧ centralizer (V : Set G) = V ∧
      ((H.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom =
        (M.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom → H = M) := by
  have hcore : (pCore 2 M).map M.subtype = V := by
    rw [hV]
    exact mapped_pCore_eq_of_normalized_subgroup_sandwich T L₀ H M hTH hHM
      hL₀M hM.le (hV ▸ hVL₀)
  obtain ⟨hnorm, hcent⟩ := normalizer_and_centralizer_eq_of_abelian_twoCore M V hmax
    hcore.symm hne hchar
  refine ⟨hcore, hnorm, hcent, ?_⟩
  have hVH : V ≤ H := hV ▸ map_subtype_le _
  intro himage
  exact eq_of_normalizer_action_image_eq V H M (hHM.trans hnorm.symm.le)
    hnorm.symm.le (hcent.le.trans hVH) (hcent.le.trans (hVH.trans hHM)) himage

end CFSG.Quasithin.Chapter3.Section02
