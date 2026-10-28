module

public import Theory.Character.ModularBlock.PrincipalReduction
public import Theory.Character.ModularBlock.CompatibleCongruence
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Compatible characteristic-zero lifts of odd-order modular roots

The splitting coefficient field is the algebraic closure of the residue field
of the actual prime in `PrincipalCongruenceBlockData`. Its field instance is
exactly `Ideal.Quotient.field`, as in `PrincipalReduction`; reduction is the
quotient map followed by the canonical embedding into that closure. Thus the
coefficient field is algebraically closed and has characteristic two.

For every odd divisor `n` of the group order, this reduction induces a
multiplicative equivalence on `n`-th roots of unity. The proof first establishes
a general ring-map lemma: a primitive root maps to a root of the same
cyclotomic polynomial, and remains primitive when `n` is nonzero in the target
field. Powers then give surjectivity on roots; equality of the two finite root
cardinalities gives injectivity. The required source primitive root is the
appropriate power of the chosen group-order root. No injectivity of the ring
reduction is assumed, and no completeness or Hensel lifting is needed.

Inverse equivalences supply roots in the actual cyclotomic order, hence in
the complex numbers. Uniqueness under reduction proves coherence when root
orders enlarge. For subgroup comparisons, the contracted-prime residue map
lands in the same ambient closure, rather than a separately chosen closure.
The cyclotomic inclusions commute with these maps by their definitions;
localization's universal property extends the same compatibility to fractions.

This supplies the coefficient foundation for genuine Brauer characters, used
as established modular-character theory in ABG III.6, printed pp.88–89.
The actual-prime conventions come from `Congruence`, `CompatibleCongruence`,
and `PrincipalReduction`. The proof uses the vendored cyclotomic-polynomial
and roots-of-unity APIs, not a block-theoretic or character-basis assertion.
-/

public section
noncomputable section

namespace ModularBlock.BrauerCoefficientExtension

/-- Reduction preserves primitivity when the root order is nonzero in the target. -/
theorem primitive_map {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    (reduction : R →+* K) {n : ℕ} [NeZero n] [NeZero (n : K)]
    {root : R} (hroot : IsPrimitiveRoot root n) :
    IsPrimitiveRoot (reduction root) n := by
  apply Polynomial.isRoot_cyclotomic_iff.mp
  simpa only [Polynomial.map_cyclotomic] using
    (hroot.isRoot_cyclotomic (NeZero.pos n)).map (f := reduction)

/-- The actual ring map bijects roots; it need not be injective on the ring. -/
theorem roots_reduction_bijective {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    (reduction : R →+* K) {n : ℕ} [NeZero n] [NeZero (n : K)]
    {root : R} (hroot : IsPrimitiveRoot root n) :
    Function.Bijective (restrictRootsOfUnity reduction n) := by
  have himage := primitive_map reduction hroot
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, hroot.card_rootsOfUnity.trans himage.card_rootsOfUnity.symm⟩
  intro target
  obtain ⟨power, _, hpower⟩ := himage.eq_pow_of_pow_eq_one
    ((mem_rootsOfUnity' n target.val).mp target.property)
  let source : rootsOfUnity n R :=
    ⟨(hroot.isUnit (NeZero.ne n)).unit ^ power, by
      rw [mem_rootsOfUnity, ← pow_mul, Nat.mul_comm, pow_mul,
        (hroot.isUnit_unit (NeZero.ne n)).pow_eq_one, one_pow]⟩
  refine ⟨source, ?_⟩
  apply Subtype.ext
  apply Units.ext
  simpa [source] using hpower

open PrincipalBlockConstruction BrauerBlockReduction CompatibleLocalBlock

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Retain the precise quotient-field instance used by the localization reduction. -/
instance residueField (d : PrincipalCongruenceBlockData G) :
    Field (principalResidueField d) := Ideal.Quotient.field d.primeIdeal

/-- One ambient algebraic closure for both ambient and subgroup root comparisons. -/
abbrev splittingField (d : PrincipalCongruenceBlockData G) :=
  AlgebraicClosure (principalResidueField d)

@[expose] def residueInclusion (d : PrincipalCongruenceBlockData G) :
    principalResidueField d →+* splittingField d := algebraMap _ _

@[expose] def reduction (d : PrincipalCongruenceBlockData G) :
    cyclotomicOrder d.eta →+* splittingField d :=
  (residueInclusion d).comp (Ideal.Quotient.mk d.primeIdeal)

/-- Construct the root equivalence for any characteristic-two coefficient map. -/
def rootEquivIn {K : Type*} [Field K] [CharP K 2]
    (d : PrincipalCongruenceBlockData G) (hom : cyclotomicOrder d.eta →+* K)
    (n : ℕ) (hodd : Odd n) (hdiv : n ∣ Nat.card G) :
    rootsOfUnity n (cyclotomicOrder d.eta) ≃* rootsOfUnity n K := by
  have hn : n ≠ 0 := by intro hzero; simp [hzero] at hodd
  letI : NeZero n := ⟨hn⟩
  letI : NeZero (n : K) := ⟨by
    rw [natCast_eq_one_of_odd_of_two_eq_zero hodd (CharP.cast_eq_zero K 2)]
    exact one_ne_zero⟩
  let root : cyclotomicOrder d.eta :=
    ⟨d.eta ^ (Nat.card G / n), pow_mem_cyclotomicOrder
      (eta_mem_cyclotomicOrder d.eta) _⟩
  have hroot : IsPrimitiveRoot root n := by
    apply IsPrimitiveRoot.of_map_of_injective (f := (cyclotomicOrder d.eta).subtype)
      _ Subtype.val_injective
    exact d.eta_spec.pow Nat.card_pos (Nat.div_mul_cancel hdiv).symm
  exact MulEquiv.ofBijective (restrictRootsOfUnity hom n)
    (roots_reduction_bijective hom hroot)

theorem rootEquivIn_apply {K : Type*} [Field K] [CharP K 2]
    (d : PrincipalCongruenceBlockData G) (hom : cyclotomicOrder d.eta →+* K)
    (n : ℕ) (hodd : Odd n) (hdiv : n ∣ Nat.card G)
    (root : rootsOfUnity n (cyclotomicOrder d.eta)) :
    rootEquivIn d hom n hodd hdiv root = restrictRootsOfUnity hom n root := by rfl

/-- The equivalence induced by reduction at the actual chosen modular prime. -/
def rootEquiv (d : PrincipalCongruenceBlockData G)
    (n : ℕ) (hodd : Odd n) (hdiv : n ∣ Nat.card G) :
    rootsOfUnity n (cyclotomicOrder d.eta) ≃* rootsOfUnity n (splittingField d) :=
  rootEquivIn d (reduction d) n hodd hdiv

theorem rootEquiv_apply (d : PrincipalCongruenceBlockData G)
    (n : ℕ) (hodd : Odd n) (hdiv : n ∣ Nat.card G)
    (root : rootsOfUnity n (cyclotomicOrder d.eta)) :
    rootEquiv d n hodd hdiv root = restrictRootsOfUnity (reduction d) n root := by
  exact rootEquivIn_apply d (reduction d) n hodd hdiv root

theorem rootEquiv_symm_reduction (d : PrincipalCongruenceBlockData G)
    (n : ℕ) (hodd : Odd n) (hdiv : n ∣ Nat.card G)
    (root : rootsOfUnity n (splittingField d)) :
    reduction d (((rootEquiv d n hodd hdiv).symm root).val : cyclotomicOrder d.eta) =
      (root.val : splittingField d) := by
  have heq := (rootEquiv d n hodd hdiv).apply_symm_apply root
  rw [rootEquiv_apply] at heq
  exact congrArg (fun value : rootsOfUnity n (splittingField d) => (value.val : splittingField d)) heq

@[expose] def enlargeRoots {R : Type*} [CommMonoid R] {n m : ℕ} (hdiv : n ∣ m) :
    rootsOfUnity n R →* rootsOfUnity m R :=
  Subgroup.inclusion (rootsOfUnity_le_of_dvd hdiv)

theorem rootEquiv_symm_enlarge (d : PrincipalCongruenceBlockData G)
    {n m : ℕ} (hn : Odd n) (hm : Odd m) (hnm : n ∣ m) (hmG : m ∣ Nat.card G)
    (root : rootsOfUnity n (splittingField d)) :
    (rootEquiv d m hm hmG).symm (enlargeRoots hnm root) =
      enlargeRoots hnm ((rootEquiv d n hn (hnm.trans hmG)).symm root) := by
  apply (rootEquiv d m hm hmG).injective
  rw [MulEquiv.apply_symm_apply, rootEquiv_apply]
  apply Subtype.ext
  apply Units.ext
  exact (rootEquiv_symm_reduction d n hn (hnm.trans hmG) root).symm

@[expose] def subgroupResidueInclusion (d : PrincipalCongruenceBlockData G)
    (H : Subgroup G) :
    principalResidueField (compatibleSubgroupPrincipalCongruenceBlockData d H) →+*
      splittingField d :=
  (residueInclusion d).comp (compatibleSubgroupResidueFieldInclusion d H)

@[expose] def subgroupReduction (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    cyclotomicOrder (compatibleSubgroupPrincipalCongruenceBlockData d H).eta →+*
      splittingField d :=
  (subgroupResidueInclusion d H).comp
    (Ideal.Quotient.mk (compatibleSubgroupPrincipalCongruenceBlockData d H).primeIdeal)

theorem subgroupReduction_apply (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (value : cyclotomicOrder (compatibleSubgroupPrincipalCongruenceBlockData d H).eta) :
    subgroupReduction d H value =
      reduction d (cyclotomicOrderInclusion (subgroupRoot_mem d H) value) := by
  rfl

/-- Subgroup roots reduce into the ambient splitting field, not a new closure. -/
def subgroupRootEquiv (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (n : ℕ) (hodd : Odd n) (hdiv : n ∣ Nat.card H) :
    rootsOfUnity n (cyclotomicOrder (compatibleSubgroupPrincipalCongruenceBlockData d H).eta) ≃*
      rootsOfUnity n (splittingField d) :=
  rootEquivIn (compatibleSubgroupPrincipalCongruenceBlockData d H)
    (subgroupReduction d H) n hodd hdiv

theorem subgroupRootEquiv_apply (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (n : ℕ) (hodd : Odd n) (hdiv : n ∣ Nat.card H)
    (root : rootsOfUnity n
      (cyclotomicOrder (compatibleSubgroupPrincipalCongruenceBlockData d H).eta)) :
    subgroupRootEquiv d H n hodd hdiv root =
      restrictRootsOfUnity (subgroupReduction d H) n root := by
  exact rootEquivIn_apply _ _ _ _ _ _

theorem subgroupRootEquiv_symm_compatible (d : PrincipalCongruenceBlockData G)
    (H : Subgroup G) (n : ℕ) (hodd : Odd n) (hdiv : n ∣ Nat.card H)
    (root : rootsOfUnity n (splittingField d)) :
    restrictRootsOfUnity (cyclotomicOrderInclusion (subgroupRoot_mem d H)) n
        ((subgroupRootEquiv d H n hodd hdiv).symm root) =
      (rootEquiv d n hodd (hdiv.trans H.card_subgroup_dvd_card)).symm root := by
  apply (rootEquiv d n hodd (hdiv.trans H.card_subgroup_dvd_card)).injective
  rw [MulEquiv.apply_symm_apply, rootEquiv_apply]
  have heq := (subgroupRootEquiv d H n hodd hdiv).apply_symm_apply root
  rw [subgroupRootEquiv_apply] at heq
  exact heq

@[expose] def localizedReduction (d : PrincipalCongruenceBlockData G) :
    Localization.AtPrime d.primeIdeal →+* splittingField d :=
  (residueInclusion d).comp (localizationToResidue d)

theorem localizedReduction_algebraMap (d : PrincipalCongruenceBlockData G)
    (value : cyclotomicOrder d.eta) :
    localizedReduction d (algebraMap _ (Localization.AtPrime d.primeIdeal) value) =
      reduction d value := by
  exact congrArg (residueInclusion d) (localizationToResidue_algebraMap d value)

theorem subgroup_localization_compatible (d : PrincipalCongruenceBlockData G)
    (H : Subgroup G) :
    (localizedReduction d).comp (compatibleSubgroupLocalizationInclusion d H) =
      (subgroupResidueInclusion d H).comp
        (localizationToResidue (compatibleSubgroupPrincipalCongruenceBlockData d H)) := by
  apply IsLocalization.ringHom_ext
    (compatibleSubgroupPrincipalCongruenceBlockData d H).primeIdeal.primeCompl
  ext value
  change localizedReduction d
      (compatibleSubgroupLocalizationInclusion d H (algebraMap _ _ value)) =
    subgroupResidueInclusion d H
      (localizationToResidue _ (algebraMap _ _ value))
  rw [compatibleSubgroupLocalizationInclusion_algebraMap,
    localizedReduction_algebraMap, localizationToResidue_algebraMap]
  exact (subgroupReduction_apply d H value).symm

/-- Embed the genuine cyclotomic-order inverse lifts into the complex roots. -/
def complexLift (d : PrincipalCongruenceBlockData G)
    (n : ℕ) (hodd : Odd n) (hdiv : n ∣ Nat.card G) :
    rootsOfUnity n (splittingField d) →* rootsOfUnity n ℂ :=
  (restrictRootsOfUnity (cyclotomicOrder d.eta).subtype n).comp
    (rootEquiv d n hodd hdiv).symm.toMonoidHom

theorem complexLift_apply (d : PrincipalCongruenceBlockData G)
    (n : ℕ) (hodd : Odd n) (hdiv : n ∣ Nat.card G)
    (root : rootsOfUnity n (splittingField d)) :
    ((complexLift d n hodd hdiv root).val : ℂ) =
      ((((rootEquiv d n hodd hdiv).symm root).val : cyclotomicOrder d.eta) : ℂ) := by
  rfl

theorem complexLift_mem (d : PrincipalCongruenceBlockData G)
    (n : ℕ) (hodd : Odd n) (hdiv : n ∣ Nat.card G)
    (root : rootsOfUnity n (splittingField d)) :
    ((complexLift d n hodd hdiv root).val : ℂ) ∈ cyclotomicOrder d.eta := by
  exact (((rootEquiv d n hodd hdiv).symm root).val : cyclotomicOrder d.eta).property

theorem complexLift_enlarge (d : PrincipalCongruenceBlockData G)
    {n m : ℕ} (hn : Odd n) (hm : Odd m) (hnm : n ∣ m) (hmG : m ∣ Nat.card G)
    (root : rootsOfUnity n (splittingField d)) :
    complexLift d m hm hmG (enlargeRoots hnm root) =
      enlargeRoots hnm (complexLift d n hn (hnm.trans hmG) root) := by
  change restrictRootsOfUnity _ m
      ((rootEquiv d m hm hmG).symm (enlargeRoots hnm root)) = _
  rw [rootEquiv_symm_enlarge]
  rfl

/-- Genuine inverse lifts, compatible with root-order enlargement and subgroup
cyclotomic inclusions. The associated residue and localization squares are
`subgroupReduction_apply` and `subgroup_localization_compatible`. -/
theorem exists_compatible_brauer_root_lifts (d : PrincipalCongruenceBlockData G) :
    ∃ lifts : ∀ (n : ℕ), Odd n → n ∣ Nat.card G →
        rootsOfUnity n (splittingField d) ≃* rootsOfUnity n (cyclotomicOrder d.eta),
      (∀ n hodd hdiv root,
        restrictRootsOfUnity (reduction d) n (lifts n hodd hdiv root) = root) ∧
      (∀ (n m : ℕ) (hn : Odd n) (hm : Odd m) (hnm : n ∣ m)
          (hmG : m ∣ Nat.card G) (root : rootsOfUnity n (splittingField d)),
        lifts m hm hmG (enlargeRoots hnm root) =
          enlargeRoots hnm (lifts n hn (hnm.trans hmG) root)) ∧
      (∀ (H : Subgroup G) (n : ℕ) (hn : Odd n) (hnH : n ∣ Nat.card H)
          (root : rootsOfUnity n (splittingField d)),
        restrictRootsOfUnity (cyclotomicOrderInclusion (subgroupRoot_mem d H)) n
            ((subgroupRootEquiv d H n hn hnH).symm root) =
          lifts n hn (hnH.trans H.card_subgroup_dvd_card) root) := by
  refine ⟨fun n hodd hdiv => (rootEquiv d n hodd hdiv).symm, ?_, ?_, ?_⟩
  · intro n hodd hdiv root
    rw [← rootEquiv_apply d n hodd hdiv, MulEquiv.apply_symm_apply]
  · intro n m hn hm hnm hmG root
    exact rootEquiv_symm_enlarge d hn hm hnm hmG root
  · intro H n hn hnH root
    exact subgroupRootEquiv_symm_compatible d H n hn hnH root

end ModularBlock.BrauerCoefficientExtension
