module

public import Theory.Character.ModularBlock.BrauerTransitivity
public import Theory.Character.ModularBlock.PrimitiveCentralIdempotent

/-!
# Normalizer conjugation on centralizer group algebras

The normalizer of a subgroup acts by conjugation on its centralizer and hence
on the centralizer group algebra. For a finite ambient group this action has
a finite orbit and fixes the sum of its distinct orbit members. Conjugation
preserves augmentation and central primitivity; distinct primitive conjugates
are orthogonal. Restrictions of central ambient elements are fixed.

These are the generic action and orbit parts of
`c3503435:glauberman_zStar/Submission/ZStar/NormalizerBrauerAction.lean`.
The coefficient formula gives the action laws and restriction invariance;
ring equivalences transport central-idempotent factors, while primitivity
collapses any nonzero intersection. Definitions are intentionally exposed for
the downstream embedding and principal-selector constructions.
-/

public section
noncomputable section
namespace ModularBlock.NormalizerBrauerAction
open Subgroup
universe u v
attribute [local instance] Fintype.ofFinite

/-- Conjugation by a normalizer element restricts to an automorphism of the
centralizer of `Q`. -/
@[expose] noncomputable def centralizerConjEquiv
    {G : Type u} [Group G] (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G)) :
    Subgroup.centralizer (Q : Set G) ≃* Subgroup.centralizer (Q : Set G) := by
  let C : Subgroup G := Subgroup.centralizer (Q : Set G)
  have hNC : Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (C : Set G) := by
    let : ((C.subgroupOf (Subgroup.normalizer (Q : Set G))).Normal) :=
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
@[expose] noncomputable def normalizerConjugate
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
    (normalizerConjugate R Q n a).coeff x =
      a.coeff ((centralizerConjEquiv Q n).symm x) := by
  rw [normalizerConjugate, MonoidAlgebra.coeff_mapDomainRingEquiv]
  rfl

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
@[expose] noncomputable def normalizerOrbit
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
@[expose] noncomputable def normalizerOrbitSum
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
  rw [MonoidAlgebra.coeff_mapDomainRingEquiv]
  change e.coeff (((centralizerConjEquiv Q n).symm x : _) : G) = e.coeff (x : G)
  rw [centralizerConjEquiv_symm_coe]
  simpa only [inv_inv] using
    (CentralIdempotentSupport.coeff_conj_eq_of_mem_center e he
      ((n : G) ⁻¹) (x : G))

/-- Central primitivity is invariant under a ring equivalence. -/
theorem map_isCentrallyPrimitive
    {A : Type u} {B : Type v} [Ring A] [Ring B]
    (E : A ≃+* B) {e : A}
    (he : IsCentrallyPrimitive e) :
    IsCentrallyPrimitive (E e) := by
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
    groupAlgebraAugmentation R
        (Subgroup.centralizer (Q : Set G))
        (MonoidAlgebra.mapDomainRingEquiv R (centralizerConjEquiv Q n) a) =
      groupAlgebraAugmentation R
        (Subgroup.centralizer (Q : Set G)) a := by
  exact BrauerTransitivity.augmentation_mapDomainRingEquiv
    (centralizerConjEquiv Q n) a


/-- A centrally primitive factor and any of its normalizer conjugates are
either identical or orthogonal.  This is the block-orbit dichotomy needed
to form the normalizer orbit sum. -/
theorem mul_conjugate_eq_zero_or_conjugate_eq
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) (n : Subgroup.normalizer (Q : Set G))
    (b : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (hbPrimitive : IsCentrallyPrimitive b) :
    b * MonoidAlgebra.mapDomainRingEquiv R
          (centralizerConjEquiv Q n) b = 0 ∨
      MonoidAlgebra.mapDomainRingEquiv R
          (centralizerConjEquiv Q n) b = b := by
  let E := MonoidAlgebra.mapDomainRingEquiv R (centralizerConjEquiv Q n)
  have hConjPrimitive : IsCentrallyPrimitive (E b) :=
    map_isCentrallyPrimitive E hbPrimitive
  by_cases hzero : b * E b = 0
  · exact Or.inl hzero
  · right
    exact
      (CentralPrimitiveFactor.eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
        hbPrimitive hConjPrimitive hzero).symm

end ModularBlock.NormalizerBrauerAction
