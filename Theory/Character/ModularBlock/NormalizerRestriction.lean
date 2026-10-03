module

public import Theory.Character.ModularBlock.RelativeTransferBasic
public import Theory.Character.ModularBlock.NormalizerEmbedding
public import Theory.Character.ModularBlock.DefectSupport

/-!
# Normalizer embedding and nested subgroup restriction

The canonical embedding of C_G(Q) in N_G(Q) is supported on elements
centralizing the copy of Q in that normalizer. Embedding onward into G
and restricting back at Q recovers the original coefficients. More
generally, if a subgroup D of N_G(Q) contains the canonical copy of Q,
restriction at its ambient image agrees before and after that embedding.

The key inclusion is that C_G(D) centralizes Q and hence lies in N_G(Q).
Thus the coefficient maps evaluate at their original indices. These
identities provide the normalizer bridge in Brauer's maximal-support
argument, without requiring any block-theoretic hypotheses.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BrauerThirdMain.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

namespace ModularBlock.BrauerThirdMain

open Subgroup

universe u v

attribute [local instance] Fintype.ofFinite

/-- Every nonzero coefficient of an element embedded from `C_G(Q)` is
indexed by an element centralizing the canonical copy of `Q` in `N_G(Q)`. -/
theorem normalizerAlgebraEmbedding_coeff_centralizes
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G)
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (n : Subgroup.normalizer (Q : Set G))
    (hn : (NormalizerBrauerAction.normalizerAlgebraEmbedding R Q a).coeff n ≠ 0) :
    n ∈ Subgroup.centralizer
      ((Q.subgroupOf (Subgroup.normalizer (Q : Set G))) :
        Set (Subgroup.normalizer (Q : Set G))) := by
  let f := NormalizerBrauerAction.centralizerToNormalizer Q
  have hnRange : n ∈ Set.range f := by
    by_contra hnot
    apply hn
    change Finsupp.mapDomain f a.coeff n = 0
    exact Finsupp.mapDomain_of_notMem_range a.coeff n hnot
  rcases hnRange with ⟨c, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  apply Subtype.ext
  have hqQ : (q : G) ∈ Q := by
    exact hq
  simpa [f] using
    (Subgroup.mem_centralizer_iff.mp c.property (q : G) hqQ)

/-- The canonical copy of `Q` in its normalizer is a `2`-group whenever
`Q` is. -/
theorem subgroupOf_normalizer_isPGroup
    {G : Type v} [Group G]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) :
    IsPGroup 2 (Q.subgroupOf (Subgroup.normalizer (Q : Set G))) := by
  exact hQ.of_equiv
    (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).symm

/-- Restricting an embedded centralizer-algebra element back at `Q`
recovers the original element coefficientwise. -/
theorem subgroupRestriction_subgroupSubtypeMap_normalizerAlgebraEmbedding
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G)
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    DefectSupport.subgroupCentralizerRestriction R Q
        (RelativeTransferBrauer.subgroupSubtypeMap R
          (Subgroup.normalizer (Q : Set G))
          (NormalizerBrauerAction.normalizerAlgebraEmbedding R Q a)) = a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb]
  | single c r =>
      ext x
      rw [DefectSupport.subgroupCentralizerRestriction_apply,
        NormalizerBrauerAction.normalizerAlgebraEmbedding_single,
        RelativeTransferBrauer.subgroupSubtypeMap_single]
      by_cases h : c = x
      · subst x
        simp [NormalizerBrauerAction.centralizerToNormalizer_coe]
      · have h' : (c : G) ≠ (x : G) := by
          intro hcx
          apply h
          exact Subtype.ext hcx
        simp [NormalizerBrauerAction.centralizerToNormalizer_coe, h, h']

/-! A coefficient-level transitivity identity for the normalizer bridge. -/

@[simp] theorem subgroupSubtypeMap_apply_image
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (H : Subgroup G) (a : MonoidAlgebra R H) (h : H) :
    (RelativeTransferBrauer.subgroupSubtypeMap R H a).coeff (h : G) = a.coeff h := by
  change Finsupp.mapDomain H.subtype a.coeff (H.subtype h) = a.coeff h
  exact Finsupp.mapDomain_apply H.subtype_injective a.coeff h

@[simp] theorem normalizerAlgebraEmbedding_apply_image
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G)
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (c : Subgroup.centralizer (Q : Set G)) :
    (NormalizerBrauerAction.normalizerAlgebraEmbedding R Q a).coeff
        (NormalizerBrauerAction.centralizerToNormalizer Q c) = a.coeff c := by
  change Finsupp.mapDomain
      (NormalizerBrauerAction.centralizerToNormalizer Q) a.coeff
      (NormalizerBrauerAction.centralizerToNormalizer Q c) = a.coeff c
  apply Finsupp.mapDomain_apply
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun n : Subgroup.normalizer (Q : Set G) ↦ (n : G)) hxy

theorem subgroupRestriction_normalizerEmbedding_subgroupRestriction_eq
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G)
    (D : Subgroup (Subgroup.normalizer (Q : Set G)))
    (hQD : Q.subgroupOf (Subgroup.normalizer (Q : Set G)) ≤ D)
    (e : MonoidAlgebra R G) :
    let DG : Subgroup G :=
      D.map (Subgroup.normalizer (Q : Set G)).subtype
    DefectSupport.subgroupCentralizerRestriction R DG
        (RelativeTransferBrauer.subgroupSubtypeMap R
          (Subgroup.normalizer (Q : Set G))
          (NormalizerBrauerAction.normalizerAlgebraEmbedding R Q
            (DefectSupport.subgroupCentralizerRestriction R Q e))) =
      DefectSupport.subgroupCentralizerRestriction R DG e := by
  dsimp only
  ext x
  rw [DefectSupport.subgroupCentralizerRestriction_apply,
    DefectSupport.subgroupCentralizerRestriction_apply]
  have hxQ : (x : G) ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have qNmem : (q : G) ∈ Subgroup.normalizer (Q : Set G) :=
      Q.le_normalizer hq
    let qN : Subgroup.normalizer (Q : Set G) := ⟨q, qNmem⟩
    have qP : qN ∈ Q.subgroupOf (Subgroup.normalizer (Q : Set G)) := hq
    have qD : qN ∈ D := hQD qP
    have qDG : (q : G) ∈
        D.map (Subgroup.normalizer (Q : Set G)).subtype :=
      Subgroup.mem_map.mpr ⟨qN, qD, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp x.property q qDG
  let cQ : Subgroup.centralizer (Q : Set G) := ⟨x, hxQ⟩
  have hxN : (x : G) ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.centralizer_le_normalizer (Q : Set G) hxQ
  let xN : Subgroup.normalizer (Q : Set G) := ⟨x, hxN⟩
  have hxNeq : xN =
      NormalizerBrauerAction.centralizerToNormalizer Q cQ := by
    apply Subtype.ext
    rfl
  change (RelativeTransferBrauer.subgroupSubtypeMap R
      (Subgroup.normalizer (Q : Set G))
      (NormalizerBrauerAction.normalizerAlgebraEmbedding R Q
        (DefectSupport.subgroupCentralizerRestriction R Q e))).coeff xN = e.coeff (x : G)
  rw [hxNeq, subgroupSubtypeMap_apply_image,
    normalizerAlgebraEmbedding_apply_image,
    DefectSupport.subgroupCentralizerRestriction_apply]

/-- If the canonical copy of `Q` lies in a subgroup of `N_G(Q)`, the
ambient centralizer of that subgroup is still contained in `N_G(Q)`. -/
theorem centralizer_map_normalizerSubtype_le_normalizer
    {G : Type v} [Group G]
    (Q : Subgroup G)
    (D : Subgroup (Subgroup.normalizer (Q : Set G)))
    (hQD : Q.subgroupOf (Subgroup.normalizer (Q : Set G)) ≤ D) :
    Subgroup.centralizer
        ((D.map (Subgroup.normalizer (Q : Set G)).subtype : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Q : Set G) := by
  intro x hx
  apply Subgroup.centralizer_le_normalizer (Q : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have qNmem : q ∈ Subgroup.normalizer (Q : Set G) := Q.le_normalizer hq
  let qN : Subgroup.normalizer (Q : Set G) := ⟨q, qNmem⟩
  have qP : qN ∈ Q.subgroupOf (Subgroup.normalizer (Q : Set G)) := hq
  have qD : qN ∈ D := hQD qP
  have qDG : q ∈ D.map (Subgroup.normalizer (Q : Set G)).subtype :=
    Subgroup.mem_map.mpr ⟨qN, qD, rfl⟩
  exact Subgroup.mem_centralizer_iff.mp hx q qDG

end ModularBlock.BrauerThirdMain

