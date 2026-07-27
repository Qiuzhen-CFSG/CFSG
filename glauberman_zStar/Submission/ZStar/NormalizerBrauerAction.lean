import Submission.ZStar.NormalizerBrauerPair
import Submission.ZStar.SubgroupBrauerMap
import Submission.ZStar.BrauerTransitivity
import Submission.ZStar.CentralPrimitiveFactor
import Submission.ZStar.SubgroupPrincipalBrauer

/-!
# Normalizer action on a Brauer centralizer

Elements of `N_G(Q)` conjugate `C_G(Q)` to itself.  We make this action
explicit and record the coefficientwise invariance of the `Q`-Brauer image
of a central ambient element.  These are the elementary orbit facts used
when passing a primitive local factor from `C_G(Q)` toward `N_G(Q)`.
-/

noncomputable section

namespace Submission.ZStar
namespace NormalizerBrauerAction

open Subgroup
open PrincipalBlockConstruction

universe u v

attribute [local instance] Fintype.ofFinite

/-- Conjugation by a normalizer element restricts to an automorphism of the
centralizer of `Q`. -/
noncomputable def centralizerConjEquiv
    {G : Type u} [Group G] (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G)) :
    Subgroup.centralizer (Q : Set G) ≃* Subgroup.centralizer (Q : Set G) := by
  let C : Subgroup G := Subgroup.centralizer (Q : Set G)
  have hNC : Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (C : Set G) := by
    letI : ((C.subgroupOf (Subgroup.normalizer (Q : Set G))).Normal) :=
      inferInstance
    exact Subgroup.le_normalizer_of_normal_subgroupOf
      (H := C) (K := Subgroup.normalizer (Q : Set G))
      (Subgroup.centralizer_le_normalizer (Q : Set G))
  have hnC : (n : G) ∈ Subgroup.normalizer (C : Set G) := hNC n.property
  have hmap : C.map (MulAut.conj (n : G)) = C :=
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnC)
  exact
    (MulAut.conj (n : G)).subgroupMap C |>.trans
      (MulEquiv.subgroupCongr hmap)

@[simp] theorem centralizerConjEquiv_coe
    {G : Type u} [Group G] (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G))
    (x : Subgroup.centralizer (Q : Set G)) :
    ((centralizerConjEquiv Q n x : Subgroup.centralizer (Q : Set G)) : G) =
      (n : G) * (x : G) * (n : G)⁻¹ := rfl

@[simp] theorem centralizerConjEquiv_symm_coe
    {G : Type u} [Group G] (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G))
    (x : Subgroup.centralizer (Q : Set G)) :
    ((centralizerConjEquiv Q n).symm x : G) =
      (n : G)⁻¹ * (x : G) * (n : G) := by
  have h := centralizerConjEquiv_coe Q n
    ((centralizerConjEquiv Q n).symm x)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  group

/-- Conjugation action of `N_G(Q)` on the group algebra of `C_G(Q)`. -/
noncomputable def normalizerConjugate
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) (n : Subgroup.normalizer (Q : Set G)) :
    MonoidAlgebra R (Subgroup.centralizer (Q : Set G)) ≃+*
      MonoidAlgebra R (Subgroup.centralizer (Q : Set G)) :=
  MonoidAlgebra.mapDomainRingEquiv R (centralizerConjEquiv Q n)

@[simp] theorem normalizerConjugate_apply
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) (n : Subgroup.normalizer (Q : Set G))
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (x : Subgroup.centralizer (Q : Set G)) :
    normalizerConjugate R Q n a x =
      a ((centralizerConjEquiv Q n).symm x) := by
  exact MonoidAlgebra.mapDomainRingEquiv_apply
    (centralizerConjEquiv Q n) a x

@[simp] theorem normalizerConjugate_one
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G)
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    normalizerConjugate R Q 1 a = a := by
  ext x
  rw [normalizerConjugate_apply]
  congr 1
  apply Subtype.ext
  rw [centralizerConjEquiv_symm_coe]
  simp

/-- The normalizer conjugation maps form a left action. -/
theorem normalizerConjugate_mul
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G)
    (n m : Subgroup.normalizer (Q : Set G))
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    normalizerConjugate R Q (n * m) a =
      normalizerConjugate R Q n (normalizerConjugate R Q m a) := by
  ext x
  rw [normalizerConjugate_apply, normalizerConjugate_apply,
    normalizerConjugate_apply]
  congr 1
  apply Subtype.ext
  simp only [centralizerConjEquiv_symm_coe, Subgroup.coe_mul]
  group

@[simp] theorem normalizerConjugate_inv_apply
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G))
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    normalizerConjugate R Q n⁻¹ (normalizerConjugate R Q n a) = a := by
  rw [← normalizerConjugate_mul, inv_mul_cancel n, normalizerConjugate_one]

@[simp] theorem normalizerConjugate_apply_inv
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G))
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    normalizerConjugate R Q n (normalizerConjugate R Q n⁻¹ a) = a := by
  rw [← normalizerConjugate_mul, mul_inv_cancel n, normalizerConjugate_one]

/-- The finite orbit of a centralizer-algebra element under `N_G(Q)`. -/
noncomputable def normalizerOrbit
    (R : Type u) {G : Type v} [CommRing R] [Group G] [Finite G]
    (Q : Subgroup G)
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    Finset (MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) := by
  classical
  exact Finset.univ.image (fun n : Subgroup.normalizer (Q : Set G) =>
    normalizerConjugate R Q n a)

theorem mem_normalizerOrbit_iff
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (Q : Subgroup G)
    (a c : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    c ∈ normalizerOrbit R Q a ↔
      ∃ n : Subgroup.normalizer (Q : Set G),
        normalizerConjugate R Q n a = c := by
  classical
  simp [normalizerOrbit]

theorem self_mem_normalizerOrbit
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (Q : Subgroup G)
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    a ∈ normalizerOrbit R Q a := by
  rw [mem_normalizerOrbit_iff]
  exact ⟨1, normalizerConjugate_one Q a⟩

/-- Conjugation permutes the finite normalizer orbit. -/
theorem image_normalizerConjugate_normalizerOrbit
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (Q : Subgroup G)
    [DecidableEq
      (MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))]
    (n : Subgroup.normalizer (Q : Set G))
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    (normalizerOrbit R Q a).image (normalizerConjugate R Q n) =
      normalizerOrbit R Q a := by
  classical
  ext c
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨b, hb, rfl⟩
    rw [mem_normalizerOrbit_iff] at hb ⊢
    rcases hb with ⟨m, rfl⟩
    exact ⟨n * m, normalizerConjugate_mul Q n m a⟩
  · intro hc
    apply Finset.mem_image.mpr
    let b := normalizerConjugate R Q n⁻¹ c
    refine ⟨b, ?_, ?_⟩
    · rw [mem_normalizerOrbit_iff] at hc ⊢
      rcases hc with ⟨m, rfl⟩
      exact ⟨n⁻¹ * m, by
        simpa [b] using normalizerConjugate_mul Q n⁻¹ m a⟩
    · exact normalizerConjugate_apply_inv Q n c

/-- The sum of the distinct normalizer conjugates. -/
noncomputable def normalizerOrbitSum
    (R : Type u) {G : Type v} [CommRing R] [Group G] [Finite G]
    (Q : Subgroup G)
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    MonoidAlgebra R (Subgroup.centralizer (Q : Set G)) :=
  ∑ b ∈ normalizerOrbit R Q a, b

/-- The orbit sum is fixed by every normalizer element. -/
theorem normalizerConjugate_orbitSum_eq_self
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G))
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    normalizerConjugate R Q n (normalizerOrbitSum R Q a) =
      normalizerOrbitSum R Q a := by
  classical
  let s := normalizerOrbit R Q a
  let f := normalizerConjugate R Q n
  have hinj : Set.InjOn f (s : Set _) := f.injective.injOn
  calc
    normalizerConjugate R Q n (normalizerOrbitSum R Q a) =
        ∑ b ∈ s, f b := by
          simp [normalizerOrbitSum, s, f, map_sum]
    _ = ∑ b ∈ s.image f, b := by
      exact (Finset.sum_image
        (f := fun b : MonoidAlgebra R
          (Subgroup.centralizer (Q : Set G)) => b) hinj).symm
    _ = ∑ b ∈ s, b := by
      rw [show s.image f = s by
        simpa [s, f] using
          image_normalizerConjugate_normalizerOrbit Q n a]
    _ = normalizerOrbitSum R Q a := by
      simp [normalizerOrbitSum, s]

private theorem finset_sum_isIdempotent_of_pairwise_orthogonal
    {A : Type u} [Ring A]
    (s : Finset A)
    (hidem : ∀ a ∈ s, IsIdempotentElem a)
    (horth : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → a * b = 0) :
    IsIdempotentElem (∑ a ∈ s, a) := by
  classical
  let I := {a : A // a ∈ s}
  let e : I → A := fun a => a.1
  have he : OrthogonalIdempotents e := by
    refine ⟨?_, ?_⟩
    · intro a
      exact hidem a.1 a.2
    · intro a b hab
      apply horth a.1 a.2 b.1 b.2
      intro h
      apply hab
      exact Subtype.ext h
  have hsum : (∑ a ∈ s.attach, (a.1 : A)) = ∑ a ∈ s, a :=
    Finset.sum_attach s (fun a : A => a)
  rw [← hsum]
  simpa [I, e] using
    (he.isIdempotentElem_sum (s := (Finset.univ : Finset I)))

/-- The `Q`-Brauer restriction of a central ambient element is fixed by the
normalizer action. -/
theorem subgroupRestriction_mapDomain_centralizerConjEquiv_eq_self
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) (n : Subgroup.normalizer (Q : Set G))
    (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G)) :
    MonoidAlgebra.mapDomainRingEquiv R (centralizerConjEquiv Q n)
        (DefectSupport.subgroupCentralizerRestriction R Q e) =
      DefectSupport.subgroupCentralizerRestriction R Q e := by
  ext x
  rw [MonoidAlgebra.mapDomainRingEquiv_apply]
  change e (((centralizerConjEquiv Q n).symm x : _) : G) = e (x : G)
  rw [centralizerConjEquiv_symm_coe]
  simpa only [inv_inv] using
    (CentralIdempotentSupport.coeff_conj_eq_of_mem_center e he
      ((n : G) ⁻¹) (x : G))

/-- Central primitivity is invariant under a ring equivalence. -/
theorem map_isCentrallyPrimitive
    {A : Type u} {B : Type v} [Ring A] [Ring B]
    (E : A ≃+* B) {e : A}
    (he : BlockPrimitivity.IsCentrallyPrimitive e) :
    BlockPrimitivity.IsCentrallyPrimitive (E e) := by
  have hcenter : E e ∈ Set.center B := by
    apply Semigroup.mem_center_iff.mpr
    intro b
    have hcomm := Semigroup.mem_center_iff.mp he.1 (E.symm b)
    have hmap := congrArg E hcomm
    simpa using hmap
  have hidem : IsIdempotentElem (E e) := he.2.1.map E
  have hne : E e ≠ 0 := by
    intro hzero
    apply he.2.2.1
    apply E.injective
    simpa using hzero
  refine ⟨hcenter, hidem, hne, ?_⟩
  intro f hfcenter hfidem hfactor hfne
  let f' : A := E.symm f
  have hf'center : f' ∈ Set.center A := by
    apply Semigroup.mem_center_iff.mpr
    intro a
    have hcomm := Semigroup.mem_center_iff.mp hfcenter (E a)
    have hmap := congrArg E.symm hcomm
    simpa [f'] using hmap
  have hf'idem : IsIdempotentElem f' := hfidem.map E.symm
  have hf'factor : f' * e = f' := by
    apply E.injective
    simpa [f'] using hfactor
  have hf'ne : f' ≠ 0 := by
    intro hzero
    apply hfne
    apply E.symm.injective
    simpa [f'] using hzero
  have hfe : f' = e :=
    he.2.2.2 f' hf'center hf'idem hf'factor hf'ne
  simpa [f'] using congrArg E hfe

/-- Conjugating the centralizer group algebra preserves augmentation. -/
theorem augmentation_mapDomain_centralizerConjEquiv
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) (n : Subgroup.normalizer (Q : Set G))
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    AugmentationScratch.augmentation R
        (Subgroup.centralizer (Q : Set G))
        (MonoidAlgebra.mapDomainRingEquiv R (centralizerConjEquiv Q n) a) =
      AugmentationScratch.augmentation R
        (Subgroup.centralizer (Q : Set G)) a := by
  exact BrauerTransitivity.augmentation_mapDomainRingEquiv
    (centralizerConjEquiv Q n) a

/-- The direct Brauer image of the ambient principal selector is fixed by
the normalizer action. -/
theorem reducedPrincipalBlockElement_subgroupRestriction_fixed
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G)) :
    MonoidAlgebra.mapDomainRingEquiv
        (BrauerBlockReduction.principalResidueField d)
        (centralizerConjEquiv Q n)
        (DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q
          (BrauerBlockReduction.reducedPrincipalBlockElement d)) =
      DefectSupport.subgroupCentralizerRestriction
        (BrauerBlockReduction.principalResidueField d) Q
        (BrauerBlockReduction.reducedPrincipalBlockElement d) := by
  exact subgroupRestriction_mapDomain_centralizerConjEquiv_eq_self
    Q n (BrauerBlockReduction.reducedPrincipalBlockElement d)
    (BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d)

/-- The compatible principal block of `C_G(Q)` is fixed by every element of
`N_G(Q)`.  Algebraically, its conjugate is again centrally primitive with
augmentation one, so it has nonzero intersection with the original
principal block and hence must coincide with it. -/
theorem localPrincipalBlockElement_mapDomain_centralizerConjEquiv_eq_self
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G)) :
    MonoidAlgebra.mapDomainRingEquiv
        (BrauerBlockReduction.principalResidueField d)
        (centralizerConjEquiv Q n)
        (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer (Q : Set G))) =
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
        (Subgroup.centralizer (Q : Set G)) := by
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let E := MonoidAlgebra.mapDomainRingEquiv K (centralizerConjEquiv Q n)
  let eLocal : MonoidAlgebra K C :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d C
  have hLocalPrimitive : BlockPrimitivity.IsCentrallyPrimitive eLocal := by
    simpa [eLocal, C, K] using
      BlockPrimitivity.localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive
        d C
  have hImagePrimitive : BlockPrimitivity.IsCentrallyPrimitive (E eLocal) :=
    map_isCentrallyPrimitive E hLocalPrimitive
  have hImageAug : AugmentationScratch.augmentation K C (E eLocal) = 1 := by
    rw [show AugmentationScratch.augmentation K C (E eLocal) =
        AugmentationScratch.augmentation K C eLocal by
      simpa [E, C, K] using
        augmentation_mapDomain_centralizerConjEquiv Q n eLocal]
    simpa [eLocal, C, K] using
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
        d C
  have hProductNe : E eLocal * eLocal ≠ 0 := by
    apply AugmentationScratch.mul_ne_zero_of_augmentation_eq_one
    · exact hImageAug
    · simpa [eLocal, C, K] using
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
          d C
  have heq : E eLocal = eLocal :=
    CentralPrimitiveFactor.eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
      hImagePrimitive hLocalPrimitive hProductNe
  simpa [E, eLocal, C, K] using heq

/-- Hence the augmentation-zero complementary factor under the direct
Brauer image is also fixed by `N_G(Q)`. -/
theorem extraBrauerFactor_mapDomain_centralizerConjEquiv_eq_self
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G)) :
    MonoidAlgebra.mapDomainRingEquiv
        (BrauerBlockReduction.principalResidueField d)
        (centralizerConjEquiv Q n)
        (SubgroupPrincipalBrauer.extraBrauerFactor d Q) =
      SubgroupPrincipalBrauer.extraBrauerFactor d Q := by
  rw [SubgroupPrincipalBrauer.extraBrauerFactor, map_sub,
    reducedPrincipalBlockElement_subgroupRestriction_fixed d Q n,
    localPrincipalBlockElement_mapDomain_centralizerConjEquiv_eq_self d Q n]

/-- Normalizer conjugation preserves every defining property of a primitive
nonprincipal factor under the direct ambient Brauer image. -/
theorem conjugate_primitiveExtraFactor
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G))
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (hbPrimitive : BlockPrimitivity.IsCentrallyPrimitive b)
    (hbAug : AugmentationScratch.augmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G)) b = 0)
    (hbExtra : b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b) :
    let b' := MonoidAlgebra.mapDomainRingEquiv
      (BrauerBlockReduction.principalResidueField d)
      (centralizerConjEquiv Q n) b
    BlockPrimitivity.IsCentrallyPrimitive b' ∧
      AugmentationScratch.augmentation
          (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer (Q : Set G)) b' = 0 ∧
      b' * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b' := by
  dsimp only
  let E := MonoidAlgebra.mapDomainRingEquiv
    (BrauerBlockReduction.principalResidueField d)
    (centralizerConjEquiv Q n)
  have hPrimitive : BlockPrimitivity.IsCentrallyPrimitive (E b) :=
    map_isCentrallyPrimitive E hbPrimitive
  have hAug : AugmentationScratch.augmentation
      (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)) (E b) = 0 := by
    rw [show AugmentationScratch.augmentation
          (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer (Q : Set G)) (E b) =
        AugmentationScratch.augmentation
          (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer (Q : Set G)) b by
      simpa [E] using augmentation_mapDomain_centralizerConjEquiv Q n b,
      hbAug]
  have hExtra : E b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = E b := by
    have hmap := congrArg E hbExtra
    rw [map_mul,
      extraBrauerFactor_mapDomain_centralizerConjEquiv_eq_self d Q n] at hmap
    exact hmap
  exact ⟨hPrimitive, hAug, hExtra⟩

/-- A centrally primitive factor and any of its normalizer conjugates are
either identical or orthogonal.  This is the block-orbit dichotomy needed
to form the normalizer orbit sum. -/
theorem mul_conjugate_eq_zero_or_conjugate_eq
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) (n : Subgroup.normalizer (Q : Set G))
    (b : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (hbPrimitive : BlockPrimitivity.IsCentrallyPrimitive b) :
    b * MonoidAlgebra.mapDomainRingEquiv R
          (centralizerConjEquiv Q n) b = 0 ∨
      MonoidAlgebra.mapDomainRingEquiv R
          (centralizerConjEquiv Q n) b = b := by
  let E := MonoidAlgebra.mapDomainRingEquiv R (centralizerConjEquiv Q n)
  have hConjPrimitive : BlockPrimitivity.IsCentrallyPrimitive (E b) :=
    map_isCentrallyPrimitive E hbPrimitive
  by_cases hzero : b * E b = 0
  · exact Or.inl hzero
  · right
    exact
      (CentralPrimitiveFactor.eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
        hbPrimitive hConjPrimitive hzero).symm

/-! Embedding the centralizer algebra into the normalizer algebra. -/

/-- The canonical inclusion `C_G(Q) ↪ N_G(Q)`. -/
noncomputable def centralizerToNormalizer
    {G : Type u} [Group G] (Q : Subgroup G) :
    Subgroup.centralizer (Q : Set G) →*
      Subgroup.normalizer (Q : Set G) := by
  let C := Subgroup.centralizer (Q : Set G)
  let N := Subgroup.normalizer (Q : Set G)
  let hCN : C ≤ N := Subgroup.centralizer_le_normalizer (Q : Set G)
  exact
    { toFun := fun c => ⟨(c : G), hCN c.property⟩
      map_one' := rfl
      map_mul' := by intro a b; rfl }

@[simp] theorem centralizerToNormalizer_coe
    {G : Type u} [Group G] (Q : Subgroup G)
    (c : Subgroup.centralizer (Q : Set G)) :
    ((centralizerToNormalizer Q c : Subgroup.normalizer (Q : Set G)) : G) =
      (c : G) := rfl

/-- The induced embedding of the centralizer group algebra into the
normalizer group algebra. -/
noncomputable def normalizerAlgebraEmbedding
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) :
    MonoidAlgebra R (Subgroup.centralizer (Q : Set G)) →+*
      MonoidAlgebra R (Subgroup.normalizer (Q : Set G)) :=
  MonoidAlgebra.mapDomainRingHom R (centralizerToNormalizer Q)

@[simp] theorem normalizerAlgebraEmbedding_single
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) (c : Subgroup.centralizer (Q : Set G)) (r : R) :
    normalizerAlgebraEmbedding R Q (MonoidAlgebra.single c r) =
      MonoidAlgebra.single (centralizerToNormalizer Q c) r := by
  simp [normalizerAlgebraEmbedding]

theorem normalizerAlgebraEmbedding_injective
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) :
    Function.Injective (normalizerAlgebraEmbedding R Q) := by
  apply Finsupp.mapDomain_injective
  intro c e hce
  apply Subtype.ext
  exact congrArg
    (fun x : Subgroup.normalizer (Q : Set G) => (x : G)) hce

/-- Conjugation by a normalizer element commutes with the subgroup-algebra
embedding. -/
theorem normalizerAlgebraEmbedding_conjugation
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) (n : Subgroup.normalizer (Q : Set G))
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n *
          normalizerAlgebraEmbedding R Q a *
          MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n⁻¹ =
      normalizerAlgebraEmbedding R Q
        (normalizerConjugate R Q n a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      rw [map_add, map_add, mul_add, add_mul, ha, hb, map_add]
  | single c r =>
      rw [normalizerAlgebraEmbedding_single]
      rw [show normalizerConjugate R Q n (MonoidAlgebra.single c r) =
          MonoidAlgebra.single (centralizerConjEquiv Q n c) r by
        simp [normalizerConjugate]]
      rw [normalizerAlgebraEmbedding_single]
      change MonoidAlgebra.single n 1 *
          MonoidAlgebra.single (centralizerToNormalizer Q c) r *
          MonoidAlgebra.single n⁻¹ 1 =
        MonoidAlgebra.single
          (centralizerToNormalizer Q (centralizerConjEquiv Q n c)) r
      rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single]
      simp only [one_mul, mul_one]
      congr 1

/-- An element fixed by all normalizer conjugations embeds as a central
element of the normalizer group algebra. -/
theorem normalizerAlgebraEmbedding_mem_center_of_fixed
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G)
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (hfixed : ∀ n : Subgroup.normalizer (Q : Set G),
      normalizerConjugate R Q n a = a) :
    normalizerAlgebraEmbedding R Q a ∈
      Set.center
        (MonoidAlgebra R (Subgroup.normalizer (Q : Set G))) := by
  rw [Semigroup.mem_center_iff]
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | single n r =>
      have hconj := normalizerAlgebraEmbedding_conjugation Q n a
      rw [hfixed n] at hconj
      have hunit :
          MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n *
              normalizerAlgebraEmbedding R Q a =
            normalizerAlgebraEmbedding R Q a *
              MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n := by
        calc
          MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n *
                normalizerAlgebraEmbedding R Q a =
              (MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n *
                  normalizerAlgebraEmbedding R Q a *
                  MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n⁻¹) *
                MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n := by
              symm
              calc
                (MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n *
                      normalizerAlgebraEmbedding R Q a *
                      MonoidAlgebra.of R
                        (Subgroup.normalizer (Q : Set G)) n⁻¹) *
                    MonoidAlgebra.of R
                      (Subgroup.normalizer (Q : Set G)) n =
                    (MonoidAlgebra.of R
                        (Subgroup.normalizer (Q : Set G)) n *
                      normalizerAlgebraEmbedding R Q a) *
                      (MonoidAlgebra.of R
                          (Subgroup.normalizer (Q : Set G)) n⁻¹ *
                        MonoidAlgebra.of R
                          (Subgroup.normalizer (Q : Set G)) n) := by
                    rw [mul_assoc]
                _ = MonoidAlgebra.of R
                      (Subgroup.normalizer (Q : Set G)) n *
                    normalizerAlgebraEmbedding R Q a := by
                  rw [← map_mul, inv_mul_cancel n, map_one, mul_one]
          _ = normalizerAlgebraEmbedding R Q a *
                MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n := by
              rw [hconj]
      have hsingle :
          (MonoidAlgebra.single n r :
              MonoidAlgebra R (Subgroup.normalizer (Q : Set G))) =
            r • MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n := by
        simp
      rw [hsingle, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      exact congrArg (fun z :
        MonoidAlgebra R (Subgroup.normalizer (Q : Set G)) => r • z) hunit

theorem augmentation_normalizerAlgebraEmbedding
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G)
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    AugmentationScratch.augmentation R
        (Subgroup.normalizer (Q : Set G))
        (normalizerAlgebraEmbedding R Q a) =
      AugmentationScratch.augmentation R
        (Subgroup.centralizer (Q : Set G)) a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | single c r => simp [normalizerAlgebraEmbedding]

/-- The direct `Q`-Brauer image of the ambient principal idempotent becomes a
central idempotent of the normalizer algebra. -/
theorem embeddedSubgroupRestriction_principalProperties
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    let K := BrauerBlockReduction.principalResidueField d
    let e := normalizerAlgebraEmbedding K Q
      (DefectSupport.subgroupCentralizerRestriction K Q
        (BrauerBlockReduction.reducedPrincipalBlockElement d))
    e ∈ Set.center (MonoidAlgebra K (Subgroup.normalizer (Q : Set G))) ∧
      IsIdempotentElem e ∧
      e ≠ 0 ∧
      AugmentationScratch.augmentation K
        (Subgroup.normalizer (Q : Set G)) e = 1 := by
  dsimp only
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let N := Subgroup.normalizer (Q : Set G)
  let eC : MonoidAlgebra K C :=
    DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d)
  let E := normalizerAlgebraEmbedding K Q
  have hfixed : ∀ n : Subgroup.normalizer (Q : Set G),
      normalizerConjugate K Q n eC = eC := by
    intro n
    simpa [normalizerConjugate, eC, K, C] using
      (reducedPrincipalBlockElement_subgroupRestriction_fixed d Q n)
  have hcenter : E eC ∈ Set.center (MonoidAlgebra K N) := by
    exact normalizerAlgebraEmbedding_mem_center_of_fixed Q eC hfixed
  have hidemC : IsIdempotentElem eC := by
    simpa [eC, K, C] using
      SubgroupPrincipalBrauer.reducedPrincipalBlockElement_subgroupRestriction_isIdempotent
        d Q hQ
  have hidem : IsIdempotentElem (E eC) := hidemC.map E
  have haugC : AugmentationScratch.augmentation K C eC = 1 := by
    simpa [eC, K, C] using
      SubgroupPrincipalBrauer.reducedPrincipalBlockElement_subgroupRestriction_augmentation_eq_one
        d Q hQ
  have haug : AugmentationScratch.augmentation K N (E eC) = 1 := by
    calc
      AugmentationScratch.augmentation K N (E eC) =
          AugmentationScratch.augmentation K C eC :=
        augmentation_normalizerAlgebraEmbedding Q eC
      _ = 1 := haugC
  have hne : E eC ≠ 0 := by
    intro hzero
    have hzeroAug := congrArg (AugmentationScratch.augmentation K N) hzero
    rw [haug, map_zero] at hzeroAug
    exact one_ne_zero hzeroAug
  exact ⟨by simpa [E, eC, K, C, N] using hcenter,
    by simpa [E, eC, K, C, N] using hidem,
    by simpa [E, eC, K, C, N] using hne,
    by simpa [E, eC, K, C, N] using haug⟩

/-! The principal selector of the normalizer is a factor of the embedded
`Q`-Brauer image.  This is the elementary principal part of the normalizer
step; it uses only central primitivity and augmentation, and makes no
Brauer-correspondence or Third Main assumption. -/

theorem normalizerLocalPrincipal_mul_embeddedSubgroupRestriction_eq_self
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    let K := BrauerBlockReduction.principalResidueField d
    let N := Subgroup.normalizer (Q : Set G)
    let E := normalizerAlgebraEmbedding K Q
    let eN := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
    let eGQ := DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d)
    eN * E eGQ = eN := by
  dsimp only
  let K := BrauerBlockReduction.principalResidueField d
  let N := Subgroup.normalizer (Q : Set G)
  let E := normalizerAlgebraEmbedding K Q
  let eN : MonoidAlgebra K N :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
  let eGQ : MonoidAlgebra K (Subgroup.centralizer (Q : Set G)) :=
    DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d)
  have hNprimitive : BlockPrimitivity.IsCentrallyPrimitive eN := by
    simpa [eN, N, K] using
      BlockPrimitivity.localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive
        d N
  have hNaug : AugmentationScratch.augmentation K N eN = 1 := by
    simpa [eN, N, K] using
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
        d N
  obtain ⟨hGQcenter, hGQidem, _hGQne, hGQaug⟩ :=
    embeddedSubgroupRestriction_principalProperties d Q hQ
  have hEcenter : E eGQ ∈ Set.center (MonoidAlgebra K N) := by
    simpa [E, eGQ, N, K] using hGQcenter
  have hEidem : IsIdempotentElem (E eGQ) := by
    simpa [E, eGQ, N, K] using hGQidem
  have hEaug : AugmentationScratch.augmentation K N (E eGQ) = 1 := by
    simpa [E, eGQ, N, K] using hGQaug
  have hprodNe : eN * E eGQ ≠ 0 := by
    apply AugmentationScratch.mul_ne_zero_of_augmentation_eq_one
    · exact hNaug
    · exact hEaug
  have hprodCenter : eN * E eGQ ∈ Set.center (MonoidAlgebra K N) :=
    Set.mul_mem_center hNprimitive.1 hEcenter
  have hcomm : Commute eN (E eGQ) :=
    (Semigroup.mem_center_iff.mp hNprimitive.1 (E eGQ)).symm
  have hprodIdem : IsIdempotentElem (eN * E eGQ) :=
    IsIdempotentElem.mul_of_commute hcomm hNprimitive.2.1 hEidem
  have hfactor : (eN * E eGQ) * eN = eN * E eGQ := by
    calc
      (eN * E eGQ) * eN = eN * (E eGQ * eN) := mul_assoc _ _ _
      _ = eN * (eN * E eGQ) := by rw [hcomm.eq]
      _ = (eN * eN) * E eGQ := (mul_assoc _ _ _).symm
      _ = eN * E eGQ := by rw [hNprimitive.2.1.eq]
  exact hNprimitive.2.2.2 (eN * E eGQ)
    hprodCenter hprodIdem hfactor hprodNe

/-! The normalizer principal selector is also a factor of the embedded
principal selector of `C_G(Q)`.  The two factor statements together isolate
the normalizer extra corner without any appeal to a block correspondence. -/

theorem normalizerLocalPrincipal_mul_embeddedCentralizerLocal_eq_self
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) :
    let K := BrauerBlockReduction.principalResidueField d
    let N := Subgroup.normalizer (Q : Set G)
    let C := Subgroup.centralizer (Q : Set G)
    let E := normalizerAlgebraEmbedding K Q
    let eN := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
    let eC := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d C
    eN * E eC = eN := by
  dsimp only
  let K := BrauerBlockReduction.principalResidueField d
  let N := Subgroup.normalizer (Q : Set G)
  let C := Subgroup.centralizer (Q : Set G)
  let E := normalizerAlgebraEmbedding K Q
  let eN : MonoidAlgebra K N :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
  let eC : MonoidAlgebra K C :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d C
  have hNprimitive : BlockPrimitivity.IsCentrallyPrimitive eN := by
    simpa [eN, N, K] using
      BlockPrimitivity.localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive
        d N
  have hNaug : AugmentationScratch.augmentation K N eN = 1 := by
    simpa [eN, N, K] using
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
        d N
  have hEcenter : E eC ∈ Set.center (MonoidAlgebra K N) := by
    apply normalizerAlgebraEmbedding_mem_center_of_fixed Q eC
    intro n
    simpa [normalizerConjugate, E, eC, K, C] using
      localPrincipalBlockElement_mapDomain_centralizerConjEquiv_eq_self d Q n
  have hEidem : IsIdempotentElem (E eC) := by
    exact (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_isIdempotent
      d C).map E
  have hEaug : AugmentationScratch.augmentation K N (E eC) = 1 := by
    calc
      AugmentationScratch.augmentation K N (E eC) =
          AugmentationScratch.augmentation K C eC :=
        augmentation_normalizerAlgebraEmbedding Q eC
      _ = 1 := by
        simpa [eC, C, K] using
          CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
            d C
  have hprodNe : eN * E eC ≠ 0 := by
    apply AugmentationScratch.mul_ne_zero_of_augmentation_eq_one
    · exact hNaug
    · exact hEaug
  have hprodCenter : eN * E eC ∈ Set.center (MonoidAlgebra K N) :=
    Set.mul_mem_center hNprimitive.1 hEcenter
  have hcomm : Commute eN (E eC) :=
    (Semigroup.mem_center_iff.mp hNprimitive.1 (E eC)).symm
  have hprodIdem : IsIdempotentElem (eN * E eC) :=
    IsIdempotentElem.mul_of_commute hcomm hNprimitive.2.1 hEidem
  have hfactor : (eN * E eC) * eN = eN * E eC := by
    calc
      (eN * E eC) * eN = eN * (E eC * eN) := mul_assoc _ _ _
      _ = eN * (eN * E eC) := by rw [hcomm.eq]
      _ = (eN * eN) * E eC := (mul_assoc _ _ _).symm
      _ = eN * E eC := by rw [hNprimitive.2.1.eq]
  exact hNprimitive.2.2.2 (eN * E eC)
    hprodCenter hprodIdem hfactor hprodNe

theorem embeddedExtraFactor_mul_normalizerLocalPrincipal_eq_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    let K := BrauerBlockReduction.principalResidueField d
    let N := Subgroup.normalizer (Q : Set G)
    let E := normalizerAlgebraEmbedding K Q
    let eN := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
    E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) * eN = 0 := by
  dsimp only
  let K := BrauerBlockReduction.principalResidueField d
  let N := Subgroup.normalizer (Q : Set G)
  let C := Subgroup.centralizer (Q : Set G)
  let E := normalizerAlgebraEmbedding K Q
  let eN : MonoidAlgebra K N :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
  let eC : MonoidAlgebra K C :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d C
  have hNfactor : eN * E eC = eN := by
    simpa [eN, eC, N, C, E, K] using
      normalizerLocalPrincipal_mul_embeddedCentralizerLocal_eq_self d Q
  have horthC : SubgroupPrincipalBrauer.extraBrauerFactor d Q * eC = 0 := by
    simpa [eC, C, K] using
      SubgroupPrincipalBrauer.extraBrauerFactor_mul_local_eq_zero d Q hQ
  have hExtraCenter :
      E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) ∈
        Set.center (MonoidAlgebra K N) := by
    apply normalizerAlgebraEmbedding_mem_center_of_fixed Q
      (SubgroupPrincipalBrauer.extraBrauerFactor d Q)
    intro n
    exact extraBrauerFactor_mapDomain_centralizerConjEquiv_eq_self d Q n
  have hExtraComm :
      Commute (E (SubgroupPrincipalBrauer.extraBrauerFactor d Q)) eN :=
    (Semigroup.mem_center_iff.mp hExtraCenter eN).symm
  calc
    E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) * eN =
        E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) * (eN * E eC) := by
          rw [hNfactor]
    _ = (E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) * eN) * E eC := by
          rw [mul_assoc]
    _ = (eN * E (SubgroupPrincipalBrauer.extraBrauerFactor d Q)) * E eC := by
          rw [hExtraComm.eq]
    _ = eN * (E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) * E eC) := by
          rw [mul_assoc]
    _ = eN * E (SubgroupPrincipalBrauer.extraBrauerFactor d Q * eC) := by
          rw [← E.map_mul]
    _ = 0 := by rw [horthC, map_zero, mul_zero]

/-- The complementary `Q`-Brauer factor remains a central idempotent after
embedding in the normalizer algebra.  It has augmentation zero, is
orthogonal to the normalizer principal block, and is still a factor of the
embedded direct ambient Brauer image. -/
theorem embeddedExtraFactor_properties
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    let K := BrauerBlockReduction.principalResidueField d
    let N := Subgroup.normalizer (Q : Set G)
    let E := normalizerAlgebraEmbedding K Q
    let eExtra := E (SubgroupPrincipalBrauer.extraBrauerFactor d Q)
    let eN := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
    let eGQ := DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d)
    eExtra ∈ Set.center (MonoidAlgebra K N) ∧
      IsIdempotentElem eExtra ∧
      AugmentationScratch.augmentation K N eExtra = 0 ∧
      eExtra * eN = 0 ∧
      eExtra * E eGQ = eExtra := by
  dsimp only
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let N := Subgroup.normalizer (Q : Set G)
  let E := normalizerAlgebraEmbedding K Q
  let eExtraC : MonoidAlgebra K C :=
    SubgroupPrincipalBrauer.extraBrauerFactor d Q
  let eExtra : MonoidAlgebra K N := E eExtraC
  let eN : MonoidAlgebra K N :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d N
  let eGQ : MonoidAlgebra K C :=
    DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d)
  have hcenter : eExtra ∈ Set.center (MonoidAlgebra K N) := by
    apply normalizerAlgebraEmbedding_mem_center_of_fixed Q eExtraC
    intro n
    simpa [normalizerConjugate, eExtraC, K, C] using
      extraBrauerFactor_mapDomain_centralizerConjEquiv_eq_self d Q n
  have hidem : IsIdempotentElem eExtra := by
    exact (SubgroupPrincipalBrauer.extraBrauerFactor_isIdempotent d Q hQ).map E
  have haug : AugmentationScratch.augmentation K N eExtra = 0 := by
    calc
      AugmentationScratch.augmentation K N eExtra =
          AugmentationScratch.augmentation K C eExtraC := by
        exact augmentation_normalizerAlgebraEmbedding Q eExtraC
      _ = 0 := by
        simpa [eExtraC, C, K] using
          SubgroupPrincipalBrauer.extraBrauerFactor_augmentation_eq_zero d Q hQ
  have horth : eExtra * eN = 0 := by
    simpa [eExtra, eExtraC, eN, E, N, K] using
      embeddedExtraFactor_mul_normalizerLocalPrincipal_eq_zero d Q hQ
  have hfactorC : eExtraC * eGQ = eExtraC := by
    simpa [eExtraC, eGQ, C, K] using
      SubgroupPrincipalBrauer.extraBrauerFactor_mul_subgroupRestriction_eq_self
        d Q hQ
  have hfactor : eExtra * E eGQ = eExtra := by
    change E eExtraC * E eGQ = E eExtraC
    rw [← E.map_mul, hfactorC]
  exact ⟨by simpa [eExtra, eExtraC, E, N, K] using hcenter,
    by simpa [eExtra, eExtraC, E, N, K] using hidem,
    by simpa [eExtra, eExtraC, E, N, K] using haug,
    by simpa [eExtra, eExtraC, eN, E, N, K] using horth,
    by simpa [eExtra, eExtraC, eGQ, E, N, K] using hfactor⟩

/-- Every nonzero central factor of the embedded orbit sum has nonzero
intersection with the embedded base orbit member. -/
theorem mul_baseEmbedding_ne_zero_of_factor_embeddedOrbitSum
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (Q : Subgroup G)
    (b : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (a : MonoidAlgebra R (Subgroup.normalizer (Q : Set G)))
    (haCenter : a ∈ Set.center
      (MonoidAlgebra R (Subgroup.normalizer (Q : Set G))))
    (haNe : a ≠ 0)
    (haFactor : a *
        normalizerAlgebraEmbedding R Q (normalizerOrbitSum R Q b) = a) :
    a * normalizerAlgebraEmbedding R Q b ≠ 0 := by
  classical
  intro hbase
  let E := normalizerAlgebraEmbedding R Q
  let s := normalizerOrbit R Q b
  let Bc := normalizerOrbitSum R Q b
  have hterm : ∀ c ∈ s, a * E c = 0 := by
    intro c hc
    rcases (mem_normalizerOrbit_iff (R := R) Q b c).mp hc with ⟨n, rfl⟩
    let un := MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n
    let uinv := MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n⁻¹
    have hconj := normalizerAlgebraEmbedding_conjugation Q n b
    change un * E b * uinv = E (normalizerConjugate R Q n b) at hconj
    rw [← hconj]
    have hcomm : un * a = a * un :=
      Semigroup.mem_center_iff.mp haCenter un
    calc
      a * (un * E b * uinv) = (a * un) * E b * uinv := by
        simp only [mul_assoc]
      _ = (un * a) * E b * uinv := by rw [hcomm]
      _ = un * (a * E b) * uinv := by simp only [mul_assoc]
      _ = 0 := by
        change un * (a * normalizerAlgebraEmbedding R Q b) * uinv = 0
        rw [hbase, mul_zero, zero_mul]
  have hzero : a * E Bc = 0 := by
    change a * E (∑ c ∈ s, c) = 0
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro c hc
    exact hterm c hc
  apply haNe
  calc
    a = a * E Bc := by simpa [E, Bc] using haFactor.symm
    _ = 0 := hzero

/-! The orbit sum packages the obstruction into one normalizer-fixed
central idempotent.  The statement is deliberately local: it uses only the
primitive-factor hypotheses already extracted from the failed Brauer
equality, and does not assume any block-theoretic conclusion. -/

/-- The normalizer orbit sum of a primitive augmentation-zero extra factor is
central, idempotent, nonzero, augmentation-zero, remains under the same extra
factor, contains the original primitive factor as a left factor, and is fixed
by the normalizer action. -/
theorem normalizerOrbitSum_primitiveExtraFactor_properties
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (hbPrimitive : BlockPrimitivity.IsCentrallyPrimitive b)
    (hbAug : AugmentationScratch.augmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G)) b = 0)
    (hbExtra : b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b) :
    let B := normalizerOrbitSum
      (BrauerBlockReduction.principalResidueField d) Q b
    B ∈ Set.center
        (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer (Q : Set G))) ∧
      IsIdempotentElem B ∧
      B ≠ 0 ∧
      AugmentationScratch.augmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G)) B = 0 ∧
      B * SubgroupPrincipalBrauer.extraBrauerFactor d Q = B ∧
      b * B = b ∧
      ∀ n : Subgroup.normalizer (Q : Set G),
        normalizerConjugate
          (BrauerBlockReduction.principalResidueField d) Q n B = B := by
  dsimp only
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let A := MonoidAlgebra K C
  let s : Finset A := normalizerOrbit K Q b
  let B : A := normalizerOrbitSum K Q b
  have horbit : ∀ c ∈ s,
      BlockPrimitivity.IsCentrallyPrimitive c ∧
        AugmentationScratch.augmentation K C c = 0 ∧
        c * SubgroupPrincipalBrauer.extraBrauerFactor d Q = c := by
    intro c hc
    rcases (mem_normalizerOrbit_iff (R := K) Q b c).mp hc with ⟨n, rfl⟩
    simpa [normalizerConjugate, K, C] using
      (conjugate_primitiveExtraFactor d Q n b hbPrimitive hbAug hbExtra)
  have hcenter : B ∈ Set.center A := by
    apply (Semigroup.mem_center_iff).2
    intro a
    change a * (∑ c ∈ s, c) = (∑ c ∈ s, c) * a
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c hc
    exact (Semigroup.mem_center_iff.mp (horbit c hc).1.1) a
  have horth : ∀ c ∈ s, ∀ e ∈ s, c ≠ e → c * e = 0 := by
    intro c hc e he hne
    have hcprim := (horbit c hc).1
    have heprim := (horbit e he).1
    by_contra hnezero
    have hce : c = e :=
      CentralPrimitiveFactor.eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
        hcprim heprim hnezero
    exact hne hce
  have hidem : IsIdempotentElem B := by
    change IsIdempotentElem (∑ c ∈ s, c)
    exact finset_sum_isIdempotent_of_pairwise_orthogonal s
      (fun c hc => (horbit c hc).1.2.1)
      horth
  have hne : B ≠ 0 := by
    intro hzero
    apply hbPrimitive.2.2.1
    have hmem : b ∈ s := by
      exact self_mem_normalizerOrbit (R := K) Q b
    have hleft : b * B = b := by
      change b * (∑ c ∈ s, c) = b
      rw [Finset.mul_sum]
      rw [Finset.sum_eq_single b]
      · exact hbPrimitive.2.1.eq
      · intro c hc hcb
        by_contra hnonzero
        have hcprim := (horbit c hc).1
        have hce : b = c :=
          CentralPrimitiveFactor.eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
            hbPrimitive hcprim hnonzero
        exact hcb hce.symm
      · intro hnot
        exact (hnot hmem).elim
    rw [hzero, mul_zero] at hleft
    exact hleft.symm
  have haug : AugmentationScratch.augmentation K C B = 0 := by
    change AugmentationScratch.augmentation K C (∑ c ∈ s, c) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro c hc
    exact (horbit c hc).2.1
  have hextra : B * SubgroupPrincipalBrauer.extraBrauerFactor d Q = B := by
    change (∑ c ∈ s, c) * SubgroupPrincipalBrauer.extraBrauerFactor d Q =
      ∑ c ∈ s, c
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c hc
    exact (horbit c hc).2.2
  have hleft : b * B = b := by
    have hmem : b ∈ s := by
      exact self_mem_normalizerOrbit (R := K) Q b
    change b * (∑ c ∈ s, c) = b
    rw [Finset.mul_sum]
    rw [Finset.sum_eq_single b]
    · exact hbPrimitive.2.1.eq
    · intro c hc hcb
      by_contra hnonzero
      have hcprim := (horbit c hc).1
      have hce : b = c :=
        CentralPrimitiveFactor.eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
          hbPrimitive hcprim hnonzero
      exact hcb hce.symm
    · intro hnot
      exact (hnot hmem).elim
  have hfixed : ∀ n : Subgroup.normalizer (Q : Set G),
      normalizerConjugate K Q n B = B := by
    intro n
    exact normalizerConjugate_orbitSum_eq_self Q n b
  exact ⟨by simpa [A, B, K, C] using hcenter,
    by simpa [A, B, K, C] using hidem,
    by simpa [A, B, K, C] using hne,
    by simpa [A, B, K, C] using haug,
    by simpa [A, B, K, C] using hextra,
    by simpa [A, B, K, C] using hleft,
    by simpa [A, B, K, C] using hfixed⟩

/-- The orbit sum viewed in `K[N_G(Q)]` is a nonzero central idempotent in
the same augmentation-zero extra corner. -/
theorem embeddedNormalizerOrbitSum_primitiveExtraFactor_properties
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (hbPrimitive : BlockPrimitivity.IsCentrallyPrimitive b)
    (hbAug : AugmentationScratch.augmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G)) b = 0)
    (hbExtra : b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b) :
    let K := BrauerBlockReduction.principalResidueField d
    let B := normalizerAlgebraEmbedding K Q
      (normalizerOrbitSum K Q b)
    B ∈ Set.center
        (MonoidAlgebra K (Subgroup.normalizer (Q : Set G))) ∧
      IsIdempotentElem B ∧
      B ≠ 0 ∧
      AugmentationScratch.augmentation K
        (Subgroup.normalizer (Q : Set G)) B = 0 ∧
      B * normalizerAlgebraEmbedding K Q
          (SubgroupPrincipalBrauer.extraBrauerFactor d Q) = B ∧
      normalizerAlgebraEmbedding K Q b * B =
        normalizerAlgebraEmbedding K Q b := by
  dsimp only
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let N := Subgroup.normalizer (Q : Set G)
  let E := normalizerAlgebraEmbedding K Q
  let Bc := normalizerOrbitSum K Q b
  have hOrbit := normalizerOrbitSum_primitiveExtraFactor_properties
    d Q b hbPrimitive hbAug hbExtra
  rcases hOrbit with
    ⟨hBcCenter, hBcIdem, hBcNe, hBcAug, hBcExtra, hBcLeft, hBcFixed⟩
  have hBNcenter : E Bc ∈ Set.center (MonoidAlgebra K N) := by
    apply normalizerAlgebraEmbedding_mem_center_of_fixed Q Bc
    intro n
    exact hBcFixed n
  have hBNidem : IsIdempotentElem (E Bc) := by
    exact hBcIdem.map E
  have hEinj : Function.Injective E :=
    normalizerAlgebraEmbedding_injective (R := K) Q
  have hBNne : E Bc ≠ 0 := by
    intro hzero
    apply hBcNe
    apply hEinj
    simpa using hzero
  have hBNaug :
      AugmentationScratch.augmentation K N (E Bc) = 0 := by
    calc
      AugmentationScratch.augmentation K N (E Bc) =
          AugmentationScratch.augmentation K C Bc := by
        exact augmentation_normalizerAlgebraEmbedding Q Bc
      _ = 0 := hBcAug
  have hBNextra :
      E Bc * E (SubgroupPrincipalBrauer.extraBrauerFactor d Q) = E Bc := by
    rw [← E.map_mul, hBcExtra]
  have hBNleft : E b * E Bc = E b := by
    rw [← E.map_mul, hBcLeft]
  exact ⟨by simpa [E, Bc, K, C, N] using hBNcenter,
    by simpa [E, Bc, K, C, N] using hBNidem,
    by simpa [E, Bc, K, C, N] using hBNne,
    by simpa [E, Bc, K, C, N] using hBNaug,
    by simpa [E, Bc, K, C, N] using hBNextra,
    by simpa [E, Bc, K, C, N] using hBNleft⟩

end NormalizerBrauerAction
end Submission.ZStar
