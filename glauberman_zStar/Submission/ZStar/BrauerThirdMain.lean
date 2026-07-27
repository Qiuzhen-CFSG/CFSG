import Submission.ZStar.ThirdMainReduction

/-!
# A transfer interface for the specialized Third Main argument

This file starts the correspondence part of the proof from coefficient-level
data already developed in `ThirdMainReduction`.  The first lemmas are purely
algebraic: a `p`-subgroup action cancels the non-fixed transfer cosets, and an
exact maximal-support factor is recovered by Brauer restriction.
-/

noncomputable section

open scoped BigOperators

namespace Submission.ZStar
namespace BrauerThirdMain

open Subgroup
open PrincipalBlockConstruction

universe u v

attribute [local instance] Fintype.ofFinite

/-! ## Conjugation and subgroup Brauer restriction -/

/-- Multiplying a conjugating representative on the left by an element of the
subgroup leaves the `Q`-Brauer restriction unchanged. -/
theorem subgroupRestriction_conjugationMap_q_mul
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) (q : Q) (H : Subgroup G) (g : G)
    (b : MonoidAlgebra R H) :
    DefectSupport.subgroupCentralizerRestriction R Q
        (RelativeTransferBrauer.conjugationMap R H ((q : G) * g) b) =
      DefectSupport.subgroupCentralizerRestriction R Q
        (RelativeTransferBrauer.conjugationMap R H g b) := by
  apply Finsupp.ext
  intro h
  rw [DefectSupport.subgroupCentralizerRestriction_apply,
    DefectSupport.subgroupCentralizerRestriction_apply]
  have hconj :
      RelativeTransferBrauer.conjugationMap R H ((q : G) * g) b =
        MonoidAlgebra.of R G (q : G) *
          RelativeTransferBrauer.conjugationMap R H g b *
            MonoidAlgebra.of R G (q : G)⁻¹ := by
    rw [RelativeTransferBrauer.conjugationMap_apply,
      RelativeTransferBrauer.conjugationMap_apply]
    simp only [map_mul, mul_inv_rev, mul_assoc]
  rw [hconj]
  let a : MonoidAlgebra R G :=
    RelativeTransferBrauer.conjugationMap R H g b
  have hcomm : (q : G) * (h : G) = (h : G) * (q : G) := by
    exact Subgroup.mem_centralizer_iff.mp h.property (q : G) q.property
  change
    (MonoidAlgebra.of R G (q : G) * a *
      MonoidAlgebra.of R G (q : G)⁻¹) (h : G) = a (h : G)
  rw [show MonoidAlgebra.of R G (q : G)⁻¹ =
      MonoidAlgebra.single (q : G)⁻¹ 1 by rfl,
    MonoidAlgebra.mul_single_apply,
    show MonoidAlgebra.of R G (q : G) =
      MonoidAlgebra.single (q : G) 1 by rfl,
    MonoidAlgebra.single_mul_apply]
  simp only [one_mul, mul_one]
  congr 1
  calc
    (q : G)⁻¹ * ((h : G) * ((q : G)⁻¹)⁻¹) =
        (q : G)⁻¹ * ((h : G) * (q : G)) := by simp
    _ = (q : G)⁻¹ * ((q : G) * (h : G)) := by rw [hcomm]
    _ = (h : G) := by simp

/-! ## A fixed-coset transfer calculation -/

/-- Brauer restriction of a relative transfer is the identity term when all
nonidentity fixed cosets have zero restriction.  The hypothesis is stated at
the coefficient level so that the theorem is independent of block theory. -/
theorem subgroupRestriction_relativeTransfer_eq_subtype_of_fixedTerms_zero
    {p : ℕ} [Fact p.Prime]
    {R : Type u} {G : Type v} [CommRing R] [CharP R p]
    [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup p Q)
    (H : Subgroup G) (hQH : Q ≤ H) (b : MonoidAlgebra R H)
    (hbCenter : b ∈ Set.center (MonoidAlgebra R H))
    (hterm : ∀ q : G ⧸ H,
      q ∈ MulAction.fixedPoints Q (G ⧸ H) →
      q ≠ (QuotientGroup.mk (1 : G) : G ⧸ H) →
      DefectSupport.subgroupCentralizerRestriction R Q
        (RelativeTransferBrauer.conjugationMap R H q.out b) = 0) :
    DefectSupport.subgroupCentralizerRestriction R Q
        (RelativeTransferBrauer.relativeTransfer R H b) =
      DefectSupport.subgroupCentralizerRestriction R Q
        (RelativeTransferBrauer.subgroupSubtypeMap R H b) := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  letI : Fintype (MulAction.fixedPoints Q (G ⧸ H)) :=
    Fintype.ofFinite _
  apply Finsupp.ext
  intro x
  rw [DefectSupport.subgroupCentralizerRestriction_apply,
    DefectSupport.subgroupCentralizerRestriction_apply]
  let ev : MonoidAlgebra R G →+ R := Finsupp.applyAddHom (x : G)
  change ev (RelativeTransferBrauer.relativeTransfer R H b) =
    ev (RelativeTransferBrauer.subgroupSubtypeMap R H b)
  rw [RelativeTransferBrauer.relativeTransfer, map_sum]
  let F : (G ⧸ H) → R := fun q ↦
    RelativeTransferBrauer.conjugationMap R H q.out b (x : G)
  have hFinv : ∀ q : Q, ∀ c : G ⧸ H, F (q • c) = F c := by
    intro q c
    change F ((q : G) • c) = F c
    have hout : RelativeTransferBrauer.conjugationMap R H
        ((q : G) • c).out b =
        RelativeTransferBrauer.conjugationMap R H ((q : G) * c.out) b := by
      apply RelativeTransferBrauer.conjugationMap_out_eq_of_mk_eq
        H ((q : G) • c) ((q : G) * c.out)
      · simpa only [smul_eq_mul] using
          (MulAction.Quotient.mk_smul_out H (q : G) c)
      · exact hbCenter
    change RelativeTransferBrauer.conjugationMap R H ((q : G) • c).out b (x : G) =
      RelativeTransferBrauer.conjugationMap R H c.out b (x : G)
    rw [hout]
    exact congrArg (fun y : MonoidAlgebra R
        (Subgroup.centralizer (Q : Set G)) => y x)
      (subgroupRestriction_conjugationMap_q_mul Q q H c.out b)
  let q0 : G ⧸ H := (QuotientGroup.mk (1 : G) : G ⧸ H)
  have hq0fixed : q0 ∈ MulAction.fixedPoints Q (G ⧸ H) := by
    rw [MulAction.mem_fixedPoints]
    intro q
    change (QuotientGroup.mk ((q : G) * 1) : G ⧸ H) =
      (QuotientGroup.mk (1 : G) : G ⧸ H)
    rw [QuotientGroup.eq]
    simpa using H.inv_mem (hQH q.property)
  calc
    (∑ q : G ⧸ H, F q) =
        ∑ q : MulAction.fixedPoints Q (G ⧸ H), F q :=
      SubgroupBrauerMap.sum_eq_sum_fixedPoints_of_smul_invariant hQ F hFinv
    _ = F q0 := by
      let e : MulAction.fixedPoints Q (G ⧸ H) := ⟨q0, hq0fixed⟩
      rw [Fintype.sum_eq_single e]
      intro y hy
      have hy0 : (y : G ⧸ H) ≠ q0 := by
        intro h
        apply hy
        exact Subtype.ext h
      have hz := hterm y.1 y.2 (by simpa [q0] using hy0)
      let evQ : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)) →+ R :=
        Finsupp.applyAddHom x
      change evQ (DefectSupport.subgroupCentralizerRestriction R Q
        (RelativeTransferBrauer.conjugationMap R H y.1.out b)) = 0
      rw [hz, map_zero]
    _ = RelativeTransferBrauer.subgroupSubtypeMap R H b (x : G) := by
      have hout := RelativeTransferBrauer.conjugationMap_out_eq_of_mk_eq
        H q0 (1 : G) (by simp [q0]) b hbCenter
      dsimp only [F]
      rw [hout, RelativeTransferBrauer.conjugationMap_apply]
      simp

/-! ## Primitive extra obstructions -/

/-- A subgroup carries an extra obstruction when the direct Brauer image of
the ambient principal selector has a primitive augmentation-zero factor. -/
def IsExtraObstruction
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) : Prop :=
  IsPGroup 2 Q ∧
    ∃ b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G)),
      BlockPrimitivity.IsCentrallyPrimitive b ∧
        AugmentationScratch.augmentation
            (BrauerBlockReduction.principalResidueField d)
            (Subgroup.centralizer (Q : Set G)) b = 0 ∧
        b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b

/-- A nonzero central idempotent of augmentation zero under a direct Brauer
image contains a primitive extra obstruction. -/
theorem exists_primitiveExtraFactor_of_centralIdempotent
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q)
    (g : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (hgCenter : g ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G))))
    (hgIdem : IsIdempotentElem g)
    (hgNe : g ≠ 0)
    (hgAug : AugmentationScratch.augmentation
      (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)) g = 0)
    (hgFactor : g * DefectSupport.subgroupCentralizerRestriction
      (BrauerBlockReduction.principalResidueField d) Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d) = g) :
    ∃ b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G)),
      BlockPrimitivity.IsCentrallyPrimitive b ∧
        AugmentationScratch.augmentation
            (BrauerBlockReduction.principalResidueField d)
            (Subgroup.centralizer (Q : Set G)) b = 0 ∧
        b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b := by
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let A := MonoidAlgebra K C
  letI : Finite K := ThirdMainReduction.principalResidueField_finite d
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : Finite A := by
    change Finite (C →₀ K)
    infer_instance
  have hmap :
      (Subring.subtype (Subring.center A)) ⟨g, hgCenter⟩ ≠ 0 := by
    simpa [A, K, C] using hgNe
  obtain ⟨bCI, hbPrimitive, hbFactor, _hbMap⟩ :=
    CentralPrimitiveExistence.exists_isCentrallyPrimitive_factor_map_ne_zero
      (A := A) (B := A) (Subring.subtype (Subring.center A)) g
      hgCenter hgIdem hmap
  let b : A := bCI.val
  have hbAug : AugmentationScratch.augmentation K C b = 0 := by
    have h := congrArg (AugmentationScratch.augmentation K C) hbFactor
    rw [map_mul, hgAug, mul_zero] at h
    exact h.symm
  have hbAmbient : b * DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d) = b := by
    calc
      b * DefectSupport.subgroupCentralizerRestriction K Q
            (BrauerBlockReduction.reducedPrincipalBlockElement d) =
          (b * g) * DefectSupport.subgroupCentralizerRestriction K Q
            (BrauerBlockReduction.reducedPrincipalBlockElement d) := by
              rw [hbFactor]
      _ = b * (g * DefectSupport.subgroupCentralizerRestriction K Q
            (BrauerBlockReduction.reducedPrincipalBlockElement d)) := by
              rw [mul_assoc]
      _ = b * g := by rw [hgFactor]
      _ = b := hbFactor
  have hbLocal : b *
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d C = 0 :=
    ThirdMainReduction.primitiveAugmentationZero_mul_localPrincipal_eq_zero
      d C b hbPrimitive hbAug
  have hbExtra : b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b := by
    rw [SubgroupPrincipalBrauer.extraBrauerFactor, mul_sub]
    change b * DefectSupport.subgroupCentralizerRestriction K Q
          (BrauerBlockReduction.reducedPrincipalBlockElement d) -
        b * CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d C = b
    rw [hbAmbient, hbLocal, sub_zero]
  exact ⟨b, by simpa [b, A, K, C] using hbPrimitive,
    by simpa [b, A, K, C] using hbAug,
    by simpa [b, A, K, C] using hbExtra⟩

/-- Failure of the involution equality supplies at least one extra
obstruction in the ambient group. -/
theorem exists_extraObstruction_of_not_brauerEquality
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hne : ¬ CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    ∃ Q : Subgroup G, IsExtraObstruction d Q := by
  obtain ⟨Q, b, hQ, hbPrimitive, hbAug, _hbAmbient,
      _hbLocal, hbExtra, _hQadmissible⟩ :=
    ThirdMainReduction.exists_admissible_primitiveAmbientBrauerFactor_orthogonal_principal_of_not_brauerEquality
      d z hzI hne
  let H := Subgroup.centralizer ({z} : Set G)
  let QG : Subgroup G := Q.map H.subtype
  exact ⟨QG, hQ, b, hbPrimitive, hbAug, hbExtra⟩

/-- Since the subgroup lattice is finite, a nonempty family of extra
obstructions has a member of maximal order. -/
theorem exists_maximal_extraObstruction
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G)
    (hex : ∃ Q : Subgroup G, IsExtraObstruction d Q) :
    ∃ Q : Subgroup G,
      IsExtraObstruction d Q ∧
        ∀ D : Subgroup G, IsExtraObstruction d D →
          Nat.card D ≤ Nat.card Q := by
  classical
  let S : Set (Subgroup G) := {Q | IsExtraObstruction d Q}
  have hSfinite : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := by
    rcases hex with ⟨Q, hQ⟩
    exact ⟨Q, hQ⟩
  obtain ⟨Q, hQmax⟩ :=
    hSfinite.exists_maximalFor (fun D : Subgroup G ↦ Nat.card D) S hSne
  refine ⟨Q, hQmax.1, ?_⟩
  intro D hD
  exact hQmax.le hD

/-- The normalizer orbit sum packages an extra obstruction into a fixed
central idempotent, while preserving the direct ambient factor identity. -/
theorem normalizerOrbitWitness_of_extraObstruction
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQobs : IsExtraObstruction d Q) :
    let K := BrauerBlockReduction.principalResidueField d
    ∃ b : MonoidAlgebra K (Subgroup.centralizer (Q : Set G)),
      ∃ Bc : MonoidAlgebra K (Subgroup.centralizer (Q : Set G)),
        BlockPrimitivity.IsCentrallyPrimitive b ∧
        AugmentationScratch.augmentation K
            (Subgroup.centralizer (Q : Set G)) b = 0 ∧
        b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b ∧
        Bc ∈ Set.center (MonoidAlgebra K
            (Subgroup.centralizer (Q : Set G))) ∧
        IsIdempotentElem Bc ∧ Bc ≠ 0 ∧
        AugmentationScratch.augmentation K
            (Subgroup.centralizer (Q : Set G)) Bc = 0 ∧
        Bc * DefectSupport.subgroupCentralizerRestriction K Q
            (BrauerBlockReduction.reducedPrincipalBlockElement d) = Bc ∧
        b * Bc = b ∧
        (∀ n : Subgroup.normalizer (Q : Set G),
          NormalizerBrauerAction.normalizerConjugate K Q n Bc = Bc) := by
  dsimp only
  rcases hQobs with ⟨hQ, b, hbPrimitive, hbAug, hbExtra⟩
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let Bc := NormalizerBrauerAction.normalizerOrbitSum K Q b
  obtain ⟨hBcCenter, hBcIdem, hBcNe, hBcAug, hBcExtra, hBcLeft,
      hBcFixed⟩ :=
    NormalizerBrauerAction.normalizerOrbitSum_primitiveExtraFactor_properties
      d Q b hbPrimitive hbAug hbExtra
  have hBcAmbient : Bc * DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d) = Bc := by
    have hExtraAmbient :=
      SubgroupPrincipalBrauer.extraBrauerFactor_mul_subgroupRestriction_eq_self
        d Q hQ
    calc
      Bc * DefectSupport.subgroupCentralizerRestriction K Q
          (BrauerBlockReduction.reducedPrincipalBlockElement d) =
          (Bc * SubgroupPrincipalBrauer.extraBrauerFactor d Q) *
            DefectSupport.subgroupCentralizerRestriction K Q
              (BrauerBlockReduction.reducedPrincipalBlockElement d) := by
                rw [hBcExtra]
      _ = Bc * (SubgroupPrincipalBrauer.extraBrauerFactor d Q *
            DefectSupport.subgroupCentralizerRestriction K Q
              (BrauerBlockReduction.reducedPrincipalBlockElement d)) := by
                rw [mul_assoc]
      _ = Bc * SubgroupPrincipalBrauer.extraBrauerFactor d Q := by
                rw [hExtraAmbient]
      _ = Bc := hBcExtra
  exact ⟨b, Bc, hbPrimitive, hbAug, hbExtra,
    by simpa [Bc, C, K] using hBcCenter,
    by simpa [Bc, C, K] using hBcIdem,
    by simpa [Bc, C, K] using hBcNe,
    by simpa [Bc, C, K] using hBcAug,
    by simpa [Bc, C, K] using hBcAmbient,
    by simpa [Bc, C, K] using hBcLeft,
    by simpa [Bc, C, K] using hBcFixed⟩

/-! ## Coefficient support inside a normalizer -/

/-- Every nonzero coefficient of an element embedded from `C_G(Q)` is
indexed by an element centralizing the canonical copy of `Q` in `N_G(Q)`. -/
theorem normalizerAlgebraEmbedding_coeff_centralizes
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G)
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (n : Subgroup.normalizer (Q : Set G))
    (hn : NormalizerBrauerAction.normalizerAlgebraEmbedding R Q a n ≠ 0) :
    n ∈ Subgroup.centralizer
      ((Q.subgroupOf (Subgroup.normalizer (Q : Set G))) :
        Set (Subgroup.normalizer (Q : Set G))) := by
  let f := NormalizerBrauerAction.centralizerToNormalizer Q
  have hnRange : n ∈ Set.range f := by
    by_contra hnot
    apply hn
    change Finsupp.mapDomain f a n = 0
    exact Finsupp.mapDomain_notin_range a n hnot
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
      apply Finsupp.ext
      intro x
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
    RelativeTransferBrauer.subgroupSubtypeMap R H a (h : G) = a h := by
  change Finsupp.mapDomain H.subtype a (H.subtype h) = a h
  exact Finsupp.mapDomain_apply H.subtype_injective a h

@[simp] theorem normalizerAlgebraEmbedding_apply_image
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G)
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (c : Subgroup.centralizer (Q : Set G)) :
    NormalizerBrauerAction.normalizerAlgebraEmbedding R Q a
        (NormalizerBrauerAction.centralizerToNormalizer Q c) = a c := by
  change Finsupp.mapDomain
      (NormalizerBrauerAction.centralizerToNormalizer Q) a
      (NormalizerBrauerAction.centralizerToNormalizer Q c) = a c
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
  apply Finsupp.ext
  intro x
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
  change RelativeTransferBrauer.subgroupSubtypeMap R
      (Subgroup.normalizer (Q : Set G))
      (NormalizerBrauerAction.normalizerAlgebraEmbedding R Q
        (DefectSupport.subgroupCentralizerRestriction R Q e)) xN = e (x : G)
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

/-- The principal-corner nilpotence argument works for every subgroup
Brauer restriction, not only the involution restriction. -/
theorem eq_zero_of_subgroupRestriction_mul_eq_self_of_corner_augmentation_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q)
    (a : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G)
    (f : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (haCenter : a ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G))
    (hfactor : a * BrauerBlockReduction.reducedPrincipalBlockElement d = a)
    (haug : AugmentationScratch.augmentation
      (BrauerBlockReduction.principalResidueField d) G a = 0)
    (hrestrict :
      DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q a * f = f) :
    f = 0 := by
  let K := BrauerBlockReduction.principalResidueField d
  have hnilA : IsNilpotent a :=
    PrimitiveCorner.reducedPrincipalBlockElement_corner_augmentation_zero_isNilpotent
      d a haCenter hfactor haug
  let aZ : Subring.center (MonoidAlgebra K G) := ⟨a, haCenter⟩
  have hnilZ : IsNilpotent aZ := by
    rcases hnilA with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact hn
  let br := SubgroupBrauerMap.subgroupCentralizerRestrictionCenterHom
    2 K Q hQ
  have hnilBr : IsNilpotent (br aZ) := hnilZ.map br
  let x : MonoidAlgebra K (Subgroup.centralizer (Q : Set G)) := br aZ
  have hxmul : x * f = f := by
    simpa [x, br, aZ, K] using hrestrict
  have hxpow : ∀ n : ℕ, x ^ n * f = f := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, mul_assoc, hxmul, ih]
  rcases hnilBr with ⟨n, hn⟩
  have hxn : x ^ n = 0 := by
    exact congrArg
      (fun y : Subring.center
        (MonoidAlgebra K (Subgroup.centralizer (Q : Set G))) =>
          (y : MonoidAlgebra K (Subgroup.centralizer (Q : Set G)))) hn
  calc
    f = x ^ n * f := (hxpow n).symm
    _ = 0 := by rw [hxn, zero_mul]

/-- If the embedded normalizer orbit sum has exact maximal support `Q`, every
nonidentity `Q`-fixed transfer coset has zero `Q`-Brauer restriction. -/
theorem fixedTerm_zero_of_exact_normalizer_support
    [Fact (Nat.Prime 2)]
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (hMax : DefectSupport.IsMaximalTwoCoefficientSupport
      (NormalizerBrauerAction.normalizerAlgebraEmbedding R Q a)
      (Q.subgroupOf (Subgroup.normalizer (Q : Set G))))
    (c : G ⧸ Subgroup.normalizer (Q : Set G))
    (hcFixed : c ∈ MulAction.fixedPoints Q
      (G ⧸ Subgroup.normalizer (Q : Set G)))
    (hcNe : c ≠
      (QuotientGroup.mk (1 : G) :
        G ⧸ Subgroup.normalizer (Q : Set G))) :
    DefectSupport.subgroupCentralizerRestriction R Q
        (RelativeTransferBrauer.conjugationMap R
          (Subgroup.normalizer (Q : Set G)) c.out
          (NormalizerBrauerAction.normalizerAlgebraEmbedding R Q a)) = 0 := by
  classical
  let N := Subgroup.normalizer (Q : Set G)
  let P : Subgroup N := Q.subgroupOf N
  let E := NormalizerBrauerAction.normalizerAlgebraEmbedding R Q
  let B : MonoidAlgebra R N := E a
  let g : G := c.out
  by_contra hRestrNe
  have hfixed : ∀ q : Q, (q : G) • c = c := by
    intro q
    change q • c = c
    exact (MulAction.mem_fixedPoints.mp hcFixed) q
  have hconjMem : ∀ q : Q, g⁻¹ * (q : G) * g ∈ N := by
    intro q
    have hmk :
        (QuotientGroup.mk g : G ⧸ N) =
          (QuotientGroup.mk ((q : G) * g) : G ⧸ N) := by
      calc
        (QuotientGroup.mk g : G ⧸ N) = c := by
          simpa [g, N] using QuotientGroup.out_eq' c
        _ = (q : G) • c := (hfixed q).symm
        _ = (QuotientGroup.mk ((q : G) * g) : G ⧸ N) := by
          simpa [g, N, smul_eq_mul] using
            (MulAction.Quotient.mk_smul_out N (q : G) c).symm
    rw [QuotientGroup.eq] at hmk
    simpa only [mul_assoc] using hmk
  let φ : Q →* N :=
    { toFun := fun q ↦ ⟨g⁻¹ * (q : G) * g, hconjMem q⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro q r
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hφinj : Function.Injective φ := by
    intro q r hqr
    apply Subtype.ext
    have hqrG := congrArg (fun n : N ↦ (n : G)) hqr
    change g⁻¹ * (q : G) * g = g⁻¹ * (r : G) * g at hqrG
    have hcancel := congrArg (fun x : G ↦ g * x * g⁻¹) hqrG
    simpa [mul_assoc] using hcancel
  let Qg : Subgroup N := MonoidHom.range φ
  have hQg : IsPGroup 2 Qg :=
    hQ.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hP : IsPGroup 2 P := by
    simpa [P, N] using subgroupOf_normalizer_isPGroup Q hQ
  have hcardQgQ : Nat.card Qg = Nat.card Q := by
    let e : Q ≃ Qg := Equiv.ofBijective φ.rangeRestrict
      ⟨(fun q r h ↦ hφinj (congrArg Subtype.val h)),
        φ.rangeRestrict_surjective⟩
    exact (Nat.card_congr e).symm
  have hcardPQ : Nat.card P = Nat.card Q := by
    simpa [P, N] using
      (Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv)
  rcases (DefectSupport.subgroupCentralizerRestriction_ne_zero_iff
      (RelativeTransferBrauer.conjugationMap R N g B) Q).mp hRestrNe with
    ⟨x, hxCentral, hxCoeff⟩
  let ψ : N →* G := (MulAut.conj g).toMonoidHom.comp N.subtype
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g).injective.comp N.subtype_injective
  have hxRange : x ∈ Set.range ψ := by
    by_contra hxNot
    apply hxCoeff
    change Finsupp.mapDomain ψ B x = 0
    exact Finsupp.mapDomain_notin_range B x hxNot
  rcases hxRange with ⟨n, rfl⟩
  have hnCoeff : B n ≠ 0 := by
    change Finsupp.mapDomain ψ B (ψ n) ≠ 0 at hxCoeff
    rw [Finsupp.mapDomain_apply hψinj] at hxCoeff
    exact hxCoeff
  have hnP : n ∈ Subgroup.centralizer (P : Set N) := by
    simpa [B, E, P, N] using
      normalizerAlgebraEmbedding_coeff_centralizes Q a n hnCoeff
  have hnQg : n ∈ Subgroup.centralizer (Qg : Set N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    rcases hr with ⟨q, rfl⟩
    apply Subtype.ext
    change (g⁻¹ * (q : G) * g) * (n : G) =
      (n : G) * (g⁻¹ * (q : G) * g)
    have hcomm :=
      Subgroup.mem_centralizer_iff.mp hxCentral (q : G) q.property
    change (q : G) * (g * (n : G) * g⁻¹) =
      (g * (n : G) * g⁻¹) * (q : G) at hcomm
    calc
      (g⁻¹ * (q : G) * g) * (n : G) =
          g⁻¹ * ((q : G) * (g * (n : G) * g⁻¹)) * g := by
            group
      _ = g⁻¹ * ((g * (n : G) * g⁻¹) * (q : G)) * g := by
            rw [hcomm]
      _ = (n : G) * (g⁻¹ * (q : G) * g) := by
            group
  letI : P.Normal := inferInstance
  have hSupP : IsPGroup 2 (P ⊔ Qg : Subgroup N) :=
    IsPGroup.to_sup_of_normal_left hP hQg
  have hnSup : n ∈ Subgroup.centralizer ((P ⊔ Qg : Subgroup N) : Set N) := by
    have hPcn : P ≤ Subgroup.centralizer ({n} : Set N) := by
      intro p hp
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hnP p hp
    have hQgcn : Qg ≤ Subgroup.centralizer ({n} : Set N) := by
      intro q hq
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hnQg q hq
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (sup_le hPcn hQgcn hr)
  have hSupSupport : DefectSupport.HasTwoCoefficientSupport B (P ⊔ Qg) :=
    ⟨hSupP, n, hnSup, hnCoeff⟩
  have hcardSup : Nat.card (P ⊔ Qg : Subgroup N) ≤ Nat.card P :=
    hMax.2 (P ⊔ Qg) hSupSupport
  have hPSup : P = P ⊔ Qg :=
    Subgroup.eq_of_le_of_card_ge le_sup_left hcardSup
  have hQgLeP : Qg ≤ P := by
    rw [hPSup]
    exact le_sup_right
  have hcardP_le_Qg : Nat.card P ≤ Nat.card Qg := by
    rw [hcardPQ, hcardQgQ]
  have hQgEqP : Qg = P :=
    Subgroup.eq_of_le_of_card_ge hQgLeP hcardP_le_Qg
  have hgInvN : g⁻¹ ∈ N := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.ext
    intro y
    constructor
    · intro hy
      rcases Subgroup.mem_map.mp hy with ⟨q, hq, rfl⟩
      let qQ : Q := ⟨q, hq⟩
      have hqQg : φ qQ ∈ Qg := ⟨qQ, rfl⟩
      have hqP : φ qQ ∈ P := by
        rw [← hQgEqP]
        exact hqQg
      change (((φ qQ : N) : G)) ∈ Q at hqP
      simpa [φ, qQ] using hqP
    · intro hy
      let yN : N := ⟨y, Q.le_normalizer hy⟩
      have hyP : yN ∈ P := hy
      have hyQg : yN ∈ Qg := by
        rw [hQgEqP]
        exact hyP
      rcases hyQg with ⟨q, hqy⟩
      apply Subgroup.mem_map.mpr
      refine ⟨(q : G), q.property, ?_⟩
      have hqyG := congrArg (fun m : N ↦ (m : G)) hqy
      simpa [φ, yN] using hqyG
  have hgN : g ∈ N := by
    simpa using N.inv_mem hgInvN
  apply hcNe
  calc
    c = (QuotientGroup.mk g : G ⧸ N) := by
      simpa [g, N] using (QuotientGroup.out_eq' c).symm
    _ = (QuotientGroup.mk (1 : G) : G ⧸ N) := by
      rw [QuotientGroup.eq]
      simpa using N.inv_mem hgN

/-- Exact normalizer support is impossible for a nonzero fixed
augmentation-zero factor under the direct principal Brauer image. -/
theorem false_of_exact_normalizer_support
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q)
    (Bc : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (hBcIdem : IsIdempotentElem Bc)
    (hBcNe : Bc ≠ 0)
    (hBcAug : AugmentationScratch.augmentation
      (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)) Bc = 0)
    (hBcAmbient : Bc * DefectSupport.subgroupCentralizerRestriction
      (BrauerBlockReduction.principalResidueField d) Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d) = Bc)
    (hBcFixed : ∀ n : Subgroup.normalizer (Q : Set G),
      NormalizerBrauerAction.normalizerConjugate
        (BrauerBlockReduction.principalResidueField d) Q n Bc = Bc)
    (hMax : DefectSupport.IsMaximalTwoCoefficientSupport
      (NormalizerBrauerAction.normalizerAlgebraEmbedding
        (BrauerBlockReduction.principalResidueField d) Q Bc)
      (Q.subgroupOf (Subgroup.normalizer (Q : Set G)))) :
    False := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := BrauerBlockReduction.principalResidueField d
  let N := Subgroup.normalizer (Q : Set G)
  let E := NormalizerBrauerAction.normalizerAlgebraEmbedding K Q
  let BN : MonoidAlgebra K N := E Bc
  let T : MonoidAlgebra K G :=
    RelativeTransferBrauer.relativeTransfer K N BN
  let eG : MonoidAlgebra K G :=
    BrauerBlockReduction.reducedPrincipalBlockElement d
  let a : MonoidAlgebra K G := T * eG
  have hBNcenter : BN ∈ Set.center (MonoidAlgebra K N) := by
    exact NormalizerBrauerAction.normalizerAlgebraEmbedding_mem_center_of_fixed
      Q Bc hBcFixed
  have hBNaug : AugmentationScratch.augmentation K N BN = 0 := by
    calc
      AugmentationScratch.augmentation K N BN =
          AugmentationScratch.augmentation K
            (Subgroup.centralizer (Q : Set G)) Bc := by
              exact NormalizerBrauerAction.augmentation_normalizerAlgebraEmbedding
                Q Bc
      _ = 0 := hBcAug
  have hTcenter : T ∈ Set.center (MonoidAlgebra K G) := by
    exact RelativeTransferBrauer.relativeTransfer_mem_center N BN hBNcenter
  have hTaug : AugmentationScratch.augmentation K G T = 0 := by
    rw [show AugmentationScratch.augmentation K G T =
        (Fintype.card (G ⧸ N) : K) *
          AugmentationScratch.augmentation K N BN by
      exact RelativeTransferBrauer.augmentation_relativeTransfer N BN,
      hBNaug, mul_zero]
  have hRecovery : DefectSupport.subgroupCentralizerRestriction K Q T = Bc := by
    calc
      DefectSupport.subgroupCentralizerRestriction K Q T =
          DefectSupport.subgroupCentralizerRestriction K Q
            (RelativeTransferBrauer.subgroupSubtypeMap K N BN) := by
              apply subgroupRestriction_relativeTransfer_eq_subtype_of_fixedTerms_zero
                Q hQ N Q.le_normalizer BN hBNcenter
              intro c hcFixed hcNe
              exact fixedTerm_zero_of_exact_normalizer_support
                Q hQ Bc (by simpa [BN, E, N] using hMax) c hcFixed hcNe
      _ = Bc := by
        simpa [BN, E, N] using
          subgroupRestriction_subgroupSubtypeMap_normalizerAlgebraEmbedding
            (R := K) Q Bc
  have heGcenter : eG ∈ Set.center (MonoidAlgebra K G) := by
    exact BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d
  have heGidem : IsIdempotentElem eG := by
    exact BrauerBlockReduction.reducedPrincipalBlockElement_isIdempotent d
  have haCenter : a ∈ Set.center (MonoidAlgebra K G) :=
    Set.mul_mem_center hTcenter heGcenter
  have haFactor : a * eG = a := by
    calc
      a * eG = T * (eG * eG) := by
        simp only [a, mul_assoc]
      _ = T * eG := by rw [heGidem.eq]
      _ = a := rfl
  have haAug : AugmentationScratch.augmentation K G a = 0 := by
    rw [show AugmentationScratch.augmentation K G a =
        AugmentationScratch.augmentation K G T *
          AugmentationScratch.augmentation K G eG by
      exact map_mul (AugmentationScratch.augmentation K G) T eG,
      hTaug, zero_mul]
  have haRecovery : DefectSupport.subgroupCentralizerRestriction K Q a = Bc := by
    calc
      DefectSupport.subgroupCentralizerRestriction K Q a =
          DefectSupport.subgroupCentralizerRestriction K Q T *
            DefectSupport.subgroupCentralizerRestriction K Q eG := by
              exact SubgroupBrauerMap.subgroupCentralizerRestriction_mul_of_mem_center
                Q hQ T eG hTcenter heGcenter
      _ = Bc * DefectSupport.subgroupCentralizerRestriction K Q eG := by
            rw [hRecovery]
      _ = Bc := hBcAmbient
  have hzero : Bc = 0 :=
    eq_zero_of_subgroupRestriction_mul_eq_self_of_corner_augmentation_zero
      d Q hQ a Bc haCenter
      (by simpa [eG, a, K] using haFactor)
      (by simpa [a, K] using haAug)
      (by rw [haRecovery, hBcIdem.eq])
  exact hBcNe hzero

/-- A strictly larger maximal coefficient-support subgroup produces a
strictly larger primitive extra obstruction in the ambient group. -/
theorem exists_larger_extraObstruction_of_strict_normalizer_support
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q)
    (Bc : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (hBcIdem : IsIdempotentElem Bc)
    (hBcAug : AugmentationScratch.augmentation
      (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)) Bc = 0)
    (hBcAmbient : Bc * DefectSupport.subgroupCentralizerRestriction
      (BrauerBlockReduction.principalResidueField d) Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d) = Bc)
    (hBcFixed : ∀ n : Subgroup.normalizer (Q : Set G),
      NormalizerBrauerAction.normalizerConjugate
        (BrauerBlockReduction.principalResidueField d) Q n Bc = Bc)
    (D : Subgroup (Subgroup.normalizer (Q : Set G)))
    (hDMax : DefectSupport.IsMaximalTwoCoefficientSupport
      (NormalizerBrauerAction.normalizerAlgebraEmbedding
        (BrauerBlockReduction.principalResidueField d) Q Bc) D)
    (hPD : Q.subgroupOf (Subgroup.normalizer (Q : Set G)) < D) :
    ∃ DG : Subgroup G,
      IsExtraObstruction d DG ∧ Nat.card Q < Nat.card DG := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := BrauerBlockReduction.principalResidueField d
  let N := Subgroup.normalizer (Q : Set G)
  let P : Subgroup N := Q.subgroupOf N
  let E := NormalizerBrauerAction.normalizerAlgebraEmbedding K Q
  let BN : MonoidAlgebra K N := E Bc
  let eG : MonoidAlgebra K G :=
    BrauerBlockReduction.reducedPrincipalBlockElement d
  let eGQ : MonoidAlgebra K (Subgroup.centralizer (Q : Set G)) :=
    DefectSupport.subgroupCentralizerRestriction K Q eG
  let eNQ : MonoidAlgebra K N := E eGQ
  let DG : Subgroup G := D.map N.subtype
  have hPLeD : P ≤ D := le_of_lt hPD
  have hDp : IsPGroup 2 D := hDMax.1.1
  have hDGp : IsPGroup 2 DG := hDp.map N.subtype
  have hC : Subgroup.centralizer (DG : Set G) ≤ N := by
    simpa [DG, P, N] using
      centralizer_map_normalizerSubtype_le_normalizer Q D hPLeD
  let ED := BrauerTransitivity.centralizerMapEquiv N D hC
  let bD : MonoidAlgebra K (Subgroup.centralizer (D : Set N)) :=
    DefectSupport.subgroupCentralizerRestriction K D BN
  let eD : MonoidAlgebra K (Subgroup.centralizer (D : Set N)) :=
    DefectSupport.subgroupCentralizerRestriction K D eNQ
  let gD : MonoidAlgebra K (Subgroup.centralizer (DG : Set G)) :=
    MonoidAlgebra.mapDomainRingEquiv K ED bD
  have hBNcenter : BN ∈ Set.center (MonoidAlgebra K N) := by
    exact NormalizerBrauerAction.normalizerAlgebraEmbedding_mem_center_of_fixed
      Q Bc hBcFixed
  have hBNidem : IsIdempotentElem BN := hBcIdem.map E
  have hBNaug : AugmentationScratch.augmentation K N BN = 0 := by
    calc
      AugmentationScratch.augmentation K N BN =
          AugmentationScratch.augmentation K
            (Subgroup.centralizer (Q : Set G)) Bc := by
              exact NormalizerBrauerAction.augmentation_normalizerAlgebraEmbedding
                Q Bc
      _ = 0 := hBcAug
  have heNQcenter : eNQ ∈ Set.center (MonoidAlgebra K N) := by
    have hprops :=
      NormalizerBrauerAction.embeddedSubgroupRestriction_principalProperties
        d Q hQ
    exact hprops.1
  have hBNfactor : BN * eNQ = BN := by
    change E Bc * E eGQ = E Bc
    rw [← E.map_mul, hBcAmbient]
  have hbDcenter : bD ∈ Set.center
      (MonoidAlgebra K (Subgroup.centralizer (D : Set N))) := by
    exact SubgroupBrauerMap.subgroupCentralizerRestriction_mem_center
      D BN hBNcenter
  have hbDidem : IsIdempotentElem bD := by
    exact SubgroupBrauerMap.subgroupCentralizerRestriction_isIdempotent_of_mem_center
      D hDp BN hBNcenter hBNidem
  have hbDne : bD ≠ 0 := by
    simpa [bD] using
      (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero BN D).mp
        hDMax.1 |>.2
  have hbDaug : AugmentationScratch.augmentation K
      (Subgroup.centralizer (D : Set N)) bD = 0 := by
    rw [show AugmentationScratch.augmentation K
          (Subgroup.centralizer (D : Set N)) bD =
        AugmentationScratch.augmentation K N BN by
      exact SubgroupBrauerMap.augmentation_subgroupCentralizerRestriction
        D hDp BN hBNcenter,
      hBNaug]
  have hbDfactor : bD * eD = bD := by
    calc
      bD * eD = DefectSupport.subgroupCentralizerRestriction K D
          (BN * eNQ) := by
            symm
            exact SubgroupBrauerMap.subgroupCentralizerRestriction_mul_of_mem_center
              D hDp BN eNQ hBNcenter heNQcenter
      _ = bD := by rw [hBNfactor]
  have hgDcenter : gD ∈ Set.center
      (MonoidAlgebra K (Subgroup.centralizer (DG : Set G))) := by
    exact BrauerTransitivity.mapDomainRingEquiv_mem_center ED bD hbDcenter
  have hgDidem : IsIdempotentElem gD :=
    BrauerTransitivity.mapDomainRingEquiv_isIdempotent ED bD hbDidem
  have hgDne : gD ≠ 0 :=
    BrauerTransitivity.mapDomainRingEquiv_ne_zero ED bD hbDne
  have hgDaug : AugmentationScratch.augmentation K
      (Subgroup.centralizer (DG : Set G)) gD = 0 := by
    rw [show AugmentationScratch.augmentation K
          (Subgroup.centralizer (DG : Set G)) gD =
        AugmentationScratch.augmentation K
          (Subgroup.centralizer (D : Set N)) bD by
      simpa [gD, DG, ED] using
        BrauerTransitivity.augmentation_mapDomainRingEquiv ED bD,
      hbDaug]
  have heDtrans : MonoidAlgebra.mapDomainRingEquiv K ED eD =
      DefectSupport.subgroupCentralizerRestriction K DG eG := by
    calc
      MonoidAlgebra.mapDomainRingEquiv K ED eD =
          DefectSupport.subgroupCentralizerRestriction K DG
            (RelativeTransferBrauer.subgroupSubtypeMap K N eNQ) := by
              change
                (MonoidAlgebra.mapDomainRingHom K ED.toMonoidHom) eD =
                  DefectSupport.subgroupCentralizerRestriction K DG
                    ((MonoidAlgebra.mapDomainRingHom K N.subtype) eNQ)
              simpa [ED, eD, DG] using
                (BrauerTransitivity.mapDomain_subgroupRestriction_eq_subgroupRestriction_mapDomain
                  N D hC eNQ)
      _ = DefectSupport.subgroupCentralizerRestriction K DG eG := by
        simpa [eNQ, eGQ, E, N, DG, eG] using
          (subgroupRestriction_normalizerEmbedding_subgroupRestriction_eq
            (R := K) Q D hPLeD eG)
  have hgDfactor : gD * DefectSupport.subgroupCentralizerRestriction K DG eG =
      gD := by
    have hmap := congrArg (MonoidAlgebra.mapDomainRingEquiv K ED) hbDfactor
    rw [map_mul, heDtrans] at hmap
    exact hmap
  obtain ⟨b, hbPrimitive, hbAug, hbExtra⟩ :=
    exists_primitiveExtraFactor_of_centralIdempotent
      d DG hDGp gD hgDcenter hgDidem hgDne hgDaug
      (by simpa [eG, K] using hgDfactor)
  have hcardPD : Nat.card P < Nat.card D := by
    have hle : Nat.card P ≤ Nat.card D :=
      Subgroup.card_le_of_le hPLeD
    apply lt_of_le_of_ne hle
    intro hcard
    apply hPD.ne
    exact Subgroup.eq_of_le_of_card_ge hPLeD (le_of_eq hcard.symm)
  have hcardPQ : Nat.card P = Nat.card Q := by
    simpa [P, N] using
      (Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv)
  have hcardDGD : Nat.card DG = Nat.card D := by
    exact Subgroup.card_map_of_injective N.subtype_injective
  refine ⟨DG, ⟨hDGp, b, hbPrimitive, hbAug, hbExtra⟩, ?_⟩
  calc
    Nat.card Q = Nat.card P := hcardPQ.symm
    _ < Nat.card D := hcardPD
    _ = Nat.card DG := hcardDGD.symm

/-! ## Unconditional principal Brauer equality -/

theorem involutionPrincipalBrauerEquality
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G)
    (z : G) (hzI : IsInvolution z) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z := by
  by_contra hne
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQobs, hQmax⟩ :=
    exists_maximal_extraObstruction d
      (exists_extraObstruction_of_not_brauerEquality d z hzI hne)
  have hQ : IsPGroup 2 Q := hQobs.1
  obtain ⟨b, Bc, hbPrimitive, hbAug, hbExtra,
      hBcCenter, hBcIdem, hBcNe, hBcAug, hBcAmbient,
      hbBc, hBcFixed⟩ :=
    normalizerOrbitWitness_of_extraObstruction d Q hQobs
  let K := BrauerBlockReduction.principalResidueField d
  let N := Subgroup.normalizer (Q : Set G)
  let P : Subgroup N := Q.subgroupOf N
  let E := NormalizerBrauerAction.normalizerAlgebraEmbedding K Q
  let BN : MonoidAlgebra K N := E Bc
  have hBNne : BN ≠ 0 := by
    intro hzero
    apply hBcNe
    apply NormalizerBrauerAction.normalizerAlgebraEmbedding_injective
      (R := K) Q
    simpa [BN, E] using hzero
  obtain ⟨D, hDMax⟩ :=
    DefectSupport.exists_isMaximalTwoCoefficientSupport BN hBNne
  have hPp : IsPGroup 2 P := by
    simpa [P, N] using subgroupOf_normalizer_isPGroup Q hQ
  have hPnormal : P.Normal := by
    infer_instance
  have hcoeff : ∀ n : N, BN n ≠ 0 →
      n ∈ Subgroup.centralizer (P : Set N) := by
    intro n hn
    simpa [BN, E, P, N] using
      normalizerAlgebraEmbedding_coeff_centralizes Q Bc n hn
  have hPLeD : P ≤ D :=
    DefectSupport.normalTwoSubgroup_le_of_isMaximalTwoCoefficientSupport_of_coeff_centralizes
      BN D hDMax P hPp hPnormal hcoeff
  by_cases hDP : D = P
  · have hPMax : DefectSupport.IsMaximalTwoCoefficientSupport
        (NormalizerBrauerAction.normalizerAlgebraEmbedding K Q Bc)
        (Q.subgroupOf (Subgroup.normalizer (Q : Set G))) := by
      simpa [BN, E, P, N, hDP] using hDMax
    exact false_of_exact_normalizer_support
      d Q hQ Bc hBcIdem hBcNe hBcAug hBcAmbient hBcFixed hPMax
  · have hPD : P < D :=
      lt_of_le_of_ne hPLeD (Ne.symm hDP)
    obtain ⟨DG, hDGobs, hcard⟩ :=
      exists_larger_extraObstruction_of_strict_normalizer_support
        d Q hQ Bc hBcIdem hBcAug hBcAmbient hBcFixed
        D (by simpa [BN, E, N] using hDMax)
        (by simpa [P, N] using hPD)
    exact (Nat.not_lt_of_ge (hQmax DG hDGobs)) hcard

end BrauerThirdMain

universe v

/-- Unconditional principal Brauer equality for an involution. -/
theorem involutionPrincipalBrauerEquality
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : G) (hzI : IsInvolution z) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z :=
  BrauerThirdMain.involutionPrincipalBrauerEquality d z hzI

end Submission.ZStar
