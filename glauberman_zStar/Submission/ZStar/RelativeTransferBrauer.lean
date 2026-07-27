import Submission.ZStar.PrimitiveCorner
import Submission.ZStar.NagaoComplement
import Submission.ZStar.OddCommutators
import Mathlib.GroupTheory.Coset.Basic

/-!
# Relative transfer and involution Brauer restriction

This file develops the elementary group-algebra calculation behind the
relative-transfer approach to the principal Brauer selector.  The genuinely
block-theoretic input is kept separate: the cross terms in the Brauer image of
a transferred local block factor are exactly the remaining correspondence
obstruction.
-/

noncomputable section

open scoped BigOperators

namespace Submission.ZStar
namespace RelativeTransferBrauer

universe u v

attribute [local instance] Fintype.ofFinite

/-- Embed a subgroup algebra into the ambient group algebra. -/
noncomputable def subgroupSubtypeMap
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (H : Subgroup G) :
    MonoidAlgebra R H →+* MonoidAlgebra R G :=
  MonoidAlgebra.mapDomainRingHom R H.subtype

/-- Conjugate an element of a subgroup algebra into the ambient group
algebra.  The image is supported on `g H g⁻¹`. -/
noncomputable def conjugationMap
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (H : Subgroup G) (g : G) :
    MonoidAlgebra R H →+* MonoidAlgebra R G :=
  MonoidAlgebra.mapDomainRingHom R
    ((MulAut.conj g).toMonoidHom.comp H.subtype)

@[simp] theorem subgroupSubtypeMap_single
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (H : Subgroup G) (h : H) (r : R) :
    subgroupSubtypeMap R H (MonoidAlgebra.single h r) =
      MonoidAlgebra.single (h : G) r := by
  simp [subgroupSubtypeMap, MonoidAlgebra.mapDomainRingHom_apply]

@[simp] theorem subgroupSubtypeMap_of
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (H : Subgroup G) (h : H) :
    subgroupSubtypeMap R H (MonoidAlgebra.of R H h) =
      MonoidAlgebra.of R G (h : G) := by
  simpa [MonoidAlgebra.of] using subgroupSubtypeMap_single H h (1 : R)

@[simp] theorem conjugationMap_single
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (H : Subgroup G) (g : G) (h : H) (r : R) :
    conjugationMap R H g (MonoidAlgebra.single h r) =
      MonoidAlgebra.single (g * (h : G) * g⁻¹) r := by
  simp [conjugationMap, MonoidAlgebra.mapDomainRingHom_apply]

/-- Coefficients on the conjugated subgroup are transported without change. -/
@[simp] theorem conjugationMap_apply_image
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (H : Subgroup G) (g : G) (b : MonoidAlgebra R H) (h : H) :
    conjugationMap R H g b (g * (h : G) * g⁻¹) = b h := by
  change Finsupp.mapDomain
      ((MulAut.conj g).toMonoidHom.comp H.subtype) b
        (((MulAut.conj g).toMonoidHom.comp H.subtype) h) = b h
  exact Finsupp.mapDomain_apply
    ((MulAut.conj g).injective.comp H.subtype_injective) b h

/-- Coefficient form after restriction to an involution centralizer. -/
@[simp] theorem centralizerRestriction_conjugationMap_apply_image
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (H : Subgroup G) (z g : G) (b : MonoidAlgebra R H) (h : H)
    (hmem : g * (h : G) * g⁻¹ ∈
      Subgroup.centralizer ({z} : Set G)) :
    BrauerMapScratch.centralizerRestriction R z
        (conjugationMap R H g b)
        ⟨g * (h : G) * g⁻¹, hmem⟩ = b h := by
  rw [BrauerMapScratch.centralizerRestriction_apply]
  exact conjugationMap_apply_image H g b h

/-- Conjugation in the group algebra agrees with multiplication by the two
group elements representing the conjugator and its inverse. -/
theorem conjugationMap_apply
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (H : Subgroup G) (g : G) (b : MonoidAlgebra R H) :
    conjugationMap R H g b =
      MonoidAlgebra.of R G g * subgroupSubtypeMap R H b *
        MonoidAlgebra.of R G g⁻¹ := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp [hb, hc, mul_add, add_mul]
  | single h r =>
      simp [MonoidAlgebra.single_mul_single]

theorem conjugationMap_mul_subgroup_eq
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (H : Subgroup G) (g : G) (h : H)
    (b : MonoidAlgebra R H)
    (hb : b ∈ Set.center (MonoidAlgebra R H)) :
    conjugationMap R H (g * (h : G)) b =
      conjugationMap R H g b := by
  rw [conjugationMap_apply, conjugationMap_apply]
  have hcommLocal :
      MonoidAlgebra.of R H h * b = b * MonoidAlgebra.of R H h :=
    Semigroup.mem_center_iff.mp hb (MonoidAlgebra.of R H h)
  have hcomm := congrArg (subgroupSubtypeMap R H) hcommLocal
  rw [map_mul, map_mul, subgroupSubtypeMap_of] at hcomm
  calc
    MonoidAlgebra.of R G (g * (h : G)) * subgroupSubtypeMap R H b *
          MonoidAlgebra.of R G (g * (h : G))⁻¹ =
        MonoidAlgebra.of R G g *
          (MonoidAlgebra.of R G (h : G) * subgroupSubtypeMap R H b *
            MonoidAlgebra.of R G (h : G)⁻¹) *
          MonoidAlgebra.of R G g⁻¹ := by
      simp only [map_mul, mul_assoc, mul_inv_rev]
    _ = MonoidAlgebra.of R G g *
          (subgroupSubtypeMap R H b *
            (MonoidAlgebra.of R G (h : G) *
              MonoidAlgebra.of R G (h : G)⁻¹)) *
          MonoidAlgebra.of R G g⁻¹ := by
      rw [hcomm]
      simp only [mul_assoc]
    _ = MonoidAlgebra.of R G g * subgroupSubtypeMap R H b *
          MonoidAlgebra.of R G g⁻¹ := by
      rw [← map_mul, mul_inv_cancel, map_one, mul_one]

/-- The representative chosen by `Quotient.out` gives the same conjugate as
any representative of the corresponding right coset. -/
theorem conjugationMap_out_eq_of_mk_eq
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (H : Subgroup G) (q : G ⧸ H) (g : G)
    (hq : (QuotientGroup.mk g : G ⧸ H) = q)
    (b : MonoidAlgebra R H)
    (hb : b ∈ Set.center (MonoidAlgebra R H)) :
    conjugationMap R H q.out b = conjugationMap R H g b := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  have hout : q.out = g * (h : G) := by
    rw [← hq]
    exact hh
  rw [hout, conjugationMap_mul_subgroup_eq H g h b hb]

/-- Relative transfer from `H` to `G`, written using the finite quotient of
right cosets.  Centrality of `b` makes the expression independent of the
chosen quotient representatives. -/
noncomputable def relativeTransfer
    (R : Type u) {G : Type v} [CommRing R] [Group G] [Finite G]
    (H : Subgroup G) (b : MonoidAlgebra R H) :
    MonoidAlgebra R G := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  exact ∑ q : G ⧸ H, conjugationMap R H q.out b

@[simp] theorem relativeTransfer_zero
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (H : Subgroup G) :
    relativeTransfer R H 0 = 0 := by
  simp [relativeTransfer]

theorem relativeTransfer_add
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (H : Subgroup G) (b c : MonoidAlgebra R H) :
    relativeTransfer R H (b + c) =
      relativeTransfer R H b + relativeTransfer R H c := by
  simp [relativeTransfer, map_add, Finset.sum_add_distrib]

theorem relativeTransfer_conjugation_invariant
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (H : Subgroup G) (b : MonoidAlgebra R H)
    (hb : b ∈ Set.center (MonoidAlgebra R H)) (x : G) :
    MonoidAlgebra.of R G x * relativeTransfer R H b *
        MonoidAlgebra.of R G x⁻¹ =
      relativeTransfer R H b := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  calc
    MonoidAlgebra.of R G x * relativeTransfer R H b *
          MonoidAlgebra.of R G x⁻¹ =
        ∑ q : G ⧸ H,
          MonoidAlgebra.of R G x *
            conjugationMap R H q.out b *
              MonoidAlgebra.of R G x⁻¹ := by
      simp only [relativeTransfer, Finset.mul_sum, Finset.sum_mul]
    _ = ∑ q : G ⧸ H,
          conjugationMap R H (x * q.out) b := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [conjugationMap_apply H q.out b,
        conjugationMap_apply H (x * q.out) b]
      simp only [map_mul, mul_assoc, mul_inv_rev]
    _ = ∑ q : G ⧸ H,
          conjugationMap R H (x • q).out b := by
      apply Finset.sum_congr rfl
      intro q hq
      apply (conjugationMap_out_eq_of_mk_eq H (x • q) (x * q.out) ?_ b hb).symm
      simpa only [smul_eq_mul] using
        (MulAction.Quotient.mk_smul_out (H := H) x q)
    _ = relativeTransfer R H b := by
      simpa [relativeTransfer] using
        (Equiv.sum_comp (MulAction.toPerm x)
          (fun q : G ⧸ H => conjugationMap R H q.out b))

/-- The relative transfer of a central subgroup element is central in the
ambient group algebra. -/
theorem relativeTransfer_mem_center
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (H : Subgroup G) (b : MonoidAlgebra R H)
    (hb : b ∈ Set.center (MonoidAlgebra R H)) :
    relativeTransfer R H b ∈ Set.center (MonoidAlgebra R G) := by
  classical
  apply (Semigroup.mem_center_iff).2
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a c ha hc => simp [add_mul, mul_add, ha, hc]
  | single x r =>
      have hconj := relativeTransfer_conjugation_invariant H b hb x
      have hcomm :
          MonoidAlgebra.of R G x * relativeTransfer R H b =
            relativeTransfer R H b * MonoidAlgebra.of R G x := by
        calc
          MonoidAlgebra.of R G x * relativeTransfer R H b =
              MonoidAlgebra.of R G x * relativeTransfer R H b * 1 :=
            (mul_one _).symm
          _ = MonoidAlgebra.of R G x * relativeTransfer R H b *
                (MonoidAlgebra.of R G x⁻¹ * MonoidAlgebra.of R G x) := by
            rw [← map_mul, inv_mul_cancel, map_one]
          _ = (MonoidAlgebra.of R G x * relativeTransfer R H b *
                MonoidAlgebra.of R G x⁻¹) * MonoidAlgebra.of R G x := by
            simp only [mul_assoc]
          _ = relativeTransfer R H b * MonoidAlgebra.of R G x := by
            rw [hconj]
      rw [← MonoidAlgebra.smul_of x r, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm]
      exact congrArg (fun y => r • y) hcomm

/-- Augmentation is unchanged by conjugating a subgroup-algebra element into
the ambient group algebra. -/
theorem augmentation_conjugationMap
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (H : Subgroup G) (g : G) (b : MonoidAlgebra R H) :
    AugmentationScratch.augmentation R G (conjugationMap R H g b) =
      AugmentationScratch.augmentation R H b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp [map_add, hb, hc]
  | single h r => simp [conjugationMap_single,
      AugmentationScratch.augmentation_single]

/-- The augmentation of a relative transfer is the subgroup index times the
augmentation of the transferred element. -/
theorem augmentation_relativeTransfer
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (H : Subgroup G) (b : MonoidAlgebra R H) :
    AugmentationScratch.augmentation R G (relativeTransfer R H b) =
      (Fintype.card (G ⧸ H) : R) *
        AugmentationScratch.augmentation R H b := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  rw [relativeTransfer, map_sum]
  simp_rw [augmentation_conjugationMap]
  simp

/-- Relative transfer commutes with change of coefficient ring. -/
theorem mapRingHom_relativeTransfer
    {R : Type u} {S : Type*} {G : Type v}
    [CommRing R] [CommRing S] [Group G] [Finite G]
    (phi : R →+* S) (H : Subgroup G) (b : MonoidAlgebra R H) :
    MonoidAlgebra.mapRingHom G phi (relativeTransfer R H b) =
      relativeTransfer S H (MonoidAlgebra.mapRingHom H phi b) := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  rw [relativeTransfer, relativeTransfer, map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp [map_add, hb, hc]
  | single h r => simp [conjugationMap_single]

/-- An element orthogonal to an augmentation-one element has augmentation
zero.  In particular, every nonprincipal local block factor is killed by the
augmentation once its orthogonality to the local principal selector is known.
-/
theorem augmentation_eq_zero_of_mul_eq_zero_of_right_eq_one
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (b e : MonoidAlgebra R G)
    (hbe : b * e = 0)
    (he : AugmentationScratch.augmentation R G e = 1) :
    AugmentationScratch.augmentation R G b = 0 := by
  have h := congrArg (AugmentationScratch.augmentation R G) hbe
  simpa [map_mul, he] using h

open PrincipalBlockConstruction

/-- A local centralizer factor orthogonal to the compatible local principal
selector has augmentation zero. -/
theorem centralizerFactor_augmentation_eq_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)))
    (horth : b *
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) = 0) :
    AugmentationScratch.augmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G)) b = 0 := by
  exact augmentation_eq_zero_of_mul_eq_zero_of_right_eq_one b _ horth
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
      d (Subgroup.centralizer ({z} : Set G)))

/-- Consequently the ambient relative transfer of a nonprincipal local
factor also has augmentation zero. -/
theorem centralizerFactor_relativeTransfer_augmentation_eq_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)))
    (horth : b *
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) = 0) :
    AugmentationScratch.augmentation
        (BrauerBlockReduction.principalResidueField d) G
        (relativeTransfer (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer ({z} : Set G)) b) = 0 := by
  rw [augmentation_relativeTransfer,
    centralizerFactor_augmentation_eq_zero d z b horth, mul_zero]

@[simp] theorem conjugationMap_one
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (H : Subgroup G) (b : MonoidAlgebra R H) :
    conjugationMap R H 1 b = subgroupSubtypeMap R H b := by
  rw [conjugationMap_apply, inv_one, map_one, one_mul, mul_one]

/-- The sum of all transfer terms except the distinguished identity coset. -/
noncomputable def relativeTransferRemainder
    (R : Type u) {G : Type v} [CommRing R] [Group G] [Finite G]
    (H : Subgroup G) (b : MonoidAlgebra R H) :
    MonoidAlgebra R G := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  exact ∑ q ∈ (Finset.univ.erase
      (QuotientGroup.mk (1 : G) : G ⧸ H)),
    conjugationMap R H q.out b

/-- The identity coset contributes exactly the embedded local element; all
other cosets form the explicit transfer remainder. -/
theorem relativeTransfer_eq_subtypeMap_add_remainder
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (H : Subgroup G) (b : MonoidAlgebra R H)
    (hb : b ∈ Set.center (MonoidAlgebra R H)) :
    relativeTransfer R H b =
      subgroupSubtypeMap R H b + relativeTransferRemainder R H b := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let q0 : G ⧸ H := QuotientGroup.mk (1 : G)
  have hterm :
      conjugationMap R H (Quotient.out q0) b =
        subgroupSubtypeMap R H b := by
    calc
      conjugationMap R H (Quotient.out q0) b =
          conjugationMap R H 1 b :=
        conjugationMap_out_eq_of_mk_eq H q0 1 rfl b hb
      _ = subgroupSubtypeMap R H b := conjugationMap_one H b
  have hsum := Finset.sum_erase_add
    (Finset.univ : Finset (G ⧸ H))
    (fun q : G ⧸ H => conjugationMap R H q.out b)
    (Finset.mem_univ q0)
  rw [hterm] at hsum
  simpa [relativeTransfer, relativeTransferRemainder, q0, add_comm] using hsum.symm

/-- Restriction back to a centralizer is a left inverse to the subgroup
algebra embedding. -/
@[simp] theorem centralizerRestriction_subgroupSubtypeMap
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))) :
    BrauerMapScratch.centralizerRestriction R z
        (subgroupSubtypeMap R (Subgroup.centralizer ({z} : Set G)) b) = b := by
  classical
  ext h
  simp [BrauerMapScratch.centralizerRestriction_apply, subgroupSubtypeMap,
    MonoidAlgebra.mapDomainRingHom_apply]

/-- Exact elementary part of the transfer/Brauer calculation: the identity
coset gives `b`, and every unresolved contribution lies in the displayed
nonidentity-coset remainder. -/
theorem centralizerRestriction_relativeTransfer_eq_add_remainder
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (z : G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)))
    (hb : b ∈ Set.center
      (MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)))) :
    BrauerMapScratch.centralizerRestriction R z
        (relativeTransfer R (Subgroup.centralizer ({z} : Set G)) b) =
      b + BrauerMapScratch.centralizerRestriction R z
        (relativeTransferRemainder R
          (Subgroup.centralizer ({z} : Set G)) b) := by
  rw [relativeTransfer_eq_subtypeMap_add_remainder _ b hb, map_add,
    centralizerRestriction_subgroupSubtypeMap]

/-- For an idempotent local factor, the desired self-recovery under
`Brauer ∘ transfer` is equivalent to annihilation of all nonidentity-coset
cross terms.  This is the exact point where defect/block correspondence is
needed. -/
theorem mul_centralizerRestriction_relativeTransfer_eq_self_iff_crossTerms
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (z : G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)))
    (hbCenter : b ∈ Set.center
      (MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))))
    (hbIdem : IsIdempotentElem b) :
    b * BrauerMapScratch.centralizerRestriction R z
          (relativeTransfer R (Subgroup.centralizer ({z} : Set G)) b) = b ↔
      b * BrauerMapScratch.centralizerRestriction R z
          (relativeTransferRemainder R
            (Subgroup.centralizer ({z} : Set G)) b) = 0 := by
  rw [centralizerRestriction_relativeTransfer_eq_add_remainder z b hbCenter,
    mul_add, hbIdem.eq, add_eq_left]

/-- The ambient principal-corner witness obtained by multiplying a relative
transfer by the reduced ambient principal selector. -/
noncomputable def principalCornerTransfer
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G))) :
    MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G :=
  BrauerBlockReduction.reducedPrincipalBlockElement d *
    relativeTransfer (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)) b

theorem principalCornerTransfer_mem_center
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)))
    (hb : b ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G)))) :
    principalCornerTransfer d z b ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G) := by
  exact Set.mul_mem_center
    (BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d)
    (relativeTransfer_mem_center _ b hb)

theorem principalCornerTransfer_mul_reducedPrincipalBlockElement
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G))) :
    principalCornerTransfer d z b *
        BrauerBlockReduction.reducedPrincipalBlockElement d =
      principalCornerTransfer d z b := by
  let e := BrauerBlockReduction.reducedPrincipalBlockElement d
  let T := relativeTransfer (BrauerBlockReduction.principalResidueField d)
    (Subgroup.centralizer ({z} : Set G)) b
  have heCenter : e ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G) :=
    BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d
  have hcomm : T * e = e * T :=
    Semigroup.mem_center_iff.mp heCenter T
  have heIdem : IsIdempotentElem e :=
    BrauerBlockReduction.reducedPrincipalBlockElement_isIdempotent d
  change (e * T) * e = e * T
  calc
    (e * T) * e = e * (T * e) := mul_assoc _ _ _
    _ = e * (e * T) := by rw [hcomm]
    _ = (e * e) * T := (mul_assoc _ _ _).symm
    _ = e * T := by rw [heIdem.eq]

theorem principalCornerTransfer_augmentation_eq_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)))
    (horth : b *
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) = 0) :
    AugmentationScratch.augmentation
        (BrauerBlockReduction.principalResidueField d) G
        (principalCornerTransfer d z b) = 0 := by
  rw [principalCornerTransfer, map_mul,
    AugmentationScratch.reducedPrincipalBlockElement_augmentation_eq_one,
    centralizerFactor_relativeTransfer_augmentation_eq_zero d z b horth,
    one_mul]

/-- If a local factor is a factor of the ambient Brauer selector and is
recovered by `Brauer ∘ transfer`, then the principal-corner transfer witness
acts as the identity on that local factor. -/
theorem centralizerRestriction_principalCornerTransfer_mul_eq_self
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)))
    (hbCenter : b ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G))))
    (hbBrauer : b *
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z = b)
    (hrecover : b * BrauerMapScratch.centralizerRestriction
        (BrauerBlockReduction.principalResidueField d) z
        (relativeTransfer (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer ({z} : Set G)) b) = b) :
    BrauerMapScratch.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z
          (principalCornerTransfer d z b) * b = b := by
  let e := BrauerBlockReduction.reducedPrincipalBlockElement d
  let T := relativeTransfer (BrauerBlockReduction.principalResidueField d)
    (Subgroup.centralizer ({z} : Set G)) b
  have heCenter : e ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G) :=
    BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d
  have hTCenter : T ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G) :=
    relativeTransfer_mem_center _ b hbCenter
  have hBr :
      BrauerMapScratch.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z
          (principalCornerTransfer d z b) =
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z *
          BrauerMapScratch.centralizerRestriction
            (BrauerBlockReduction.principalResidueField d) z T := by
    change BrauerMapScratch.centralizerRestriction
        (BrauerBlockReduction.principalResidueField d) z (e * T) = _
    exact BrauerMapScratch.centralizerRestriction_mul_of_mem_center
      z hz e T heCenter hTCenter
  rw [hBr]
  have hbComm := Semigroup.mem_center_iff.mp hbCenter
    (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z *
      BrauerMapScratch.centralizerRestriction
        (BrauerBlockReduction.principalResidueField d) z T)
  calc
    (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z *
          BrauerMapScratch.centralizerRestriction
            (BrauerBlockReduction.principalResidueField d) z T) * b =
        b * (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z *
          BrauerMapScratch.centralizerRestriction
            (BrauerBlockReduction.principalResidueField d) z T) := hbComm
    _ = (b * BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z) *
          BrauerMapScratch.centralizerRestriction
            (BrauerBlockReduction.principalResidueField d) z T :=
      (mul_assoc _ _ _).symm
    _ = b * BrauerMapScratch.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z T := by rw [hbBrauer]
    _ = b := hrecover

/-- The complete transfer contradiction, with the sole remaining input
isolated as self-recovery of the local factor under `Brauer ∘ transfer`. -/
theorem centralizerFactor_eq_zero_of_relativeTransfer_recovery
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)))
    (hbCenter : b ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G))))
    (horth : b *
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) = 0)
    (hbBrauer : b *
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z = b)
    (hrecover : b * BrauerMapScratch.centralizerRestriction
        (BrauerBlockReduction.principalResidueField d) z
        (relativeTransfer (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer ({z} : Set G)) b) = b) :
    b = 0 := by
  apply PrimitiveCorner.eq_zero_of_brauerRestriction_mul_eq_self_of_corner_augmentation_zero
    d z hz (principalCornerTransfer d z b) b
  · exact principalCornerTransfer_mem_center d z b hbCenter
  · exact principalCornerTransfer_mul_reducedPrincipalBlockElement d z b
  · exact principalCornerTransfer_augmentation_eq_zero d z b horth
  · exact centralizerRestriction_principalCornerTransfer_mul_eq_self
      d z hz b hbCenter hbBrauer hrecover

/-- The extra local factor of the ambient involution Brauer selector.  It is
the complementary central idempotent to the compatible local principal
factor once the latter is known to be a factor. -/
noncomputable def extraBrauerFactor
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)) :=
  BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer ({z} : Set G))

theorem extraBrauerFactor_mem_center
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    extraBrauerFactor d z ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G))) := by
  apply (Semigroup.mem_center_iff).2
  intro a
  rw [extraBrauerFactor, mul_sub, sub_mul]
  rw [Semigroup.mem_center_iff.mp
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement_mem_center d z) a,
    Semigroup.mem_center_iff.mp
      (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_mem_center
        d (Subgroup.centralizer ({z} : Set G))) a]

theorem extraBrauerFactor_isIdempotent
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1) :
    IsIdempotentElem (extraBrauerFactor d z) := by
  let eB := BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  let eL := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
    (Subgroup.centralizer ({z} : Set G))
  have hfactor : eL * eB = eL := by
    exact BlockPrimitivity.localPrincipalBlockElement_mul_involutionBrauer_eq_self
      d z hz
  have hcomm : eB * eL = eL := by
    have hc := Semigroup.mem_center_iff.mp
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement_mem_center d z) eL
    rw [← hc, hfactor]
  exact IsIdempotentElem.sub
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_isIdempotent
      d (Subgroup.centralizer ({z} : Set G)))
    (BrauerBlockReduction.involutionBrauerPrincipalBlockElement_isIdempotent d z hz)
    hfactor hcomm

theorem extraBrauerFactor_mul_local_eq_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1) :
    extraBrauerFactor d z *
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) = 0 := by
  let eB := BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  let eL := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
    (Subgroup.centralizer ({z} : Set G))
  have hfactor : eL * eB = eL := by
    exact BlockPrimitivity.localPrincipalBlockElement_mul_involutionBrauer_eq_self
      d z hz
  have hcomm : eB * eL = eL := by
    have hc := Semigroup.mem_center_iff.mp
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement_mem_center d z) eL
    rw [← hc, hfactor]
  change (eB - eL) * eL = 0
  rw [sub_mul, hcomm,
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_isIdempotent
      d (Subgroup.centralizer ({z} : Set G)), sub_self]

theorem extraBrauerFactor_mul_brauer_eq_self
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1) :
    extraBrauerFactor d z *
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
      extraBrauerFactor d z := by
  let eB := BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  let eL := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
    (Subgroup.centralizer ({z} : Set G))
  have hfactor : eL * eB = eL := by
    exact BlockPrimitivity.localPrincipalBlockElement_mul_involutionBrauer_eq_self
      d z hz
  change (eB - eL) * eB = eB - eL
  rw [sub_mul,
    BrauerBlockReduction.involutionBrauerPrincipalBlockElement_isIdempotent d z hz,
    hfactor]

/-- If every nonidentity-coset cross term annihilates the extra factor, then
the ambient and compatible local principal Brauer selectors coincide. -/
theorem involutionPrincipalBrauerEquality_of_extraFactor_crossTerms_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1)
    (hcross :
      extraBrauerFactor d z * BrauerMapScratch.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z
          (relativeTransferRemainder
            (BrauerBlockReduction.principalResidueField d)
            (Subgroup.centralizer ({z} : Set G)) (extraBrauerFactor d z)) = 0) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z := by
  let b := extraBrauerFactor d z
  have hbCenter := extraBrauerFactor_mem_center d z
  have hbIdem := extraBrauerFactor_isIdempotent d z hz
  have hrecover : b * BrauerMapScratch.centralizerRestriction
      (BrauerBlockReduction.principalResidueField d) z
      (relativeTransfer (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G)) b) = b :=
    (mul_centralizerRestriction_relativeTransfer_eq_self_iff_crossTerms
      z b hbCenter hbIdem).2 hcross
  have hzero : b = 0 :=
    centralizerFactor_eq_zero_of_relativeTransfer_recovery d z hz b hbCenter
      (by exact extraBrauerFactor_mul_local_eq_zero d z hz)
      (by exact extraBrauerFactor_mul_brauer_eq_self d z hz)
      hrecover
  change CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer ({z} : Set G)) =
    BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  exact (sub_eq_zero.mp hzero).symm

/-- A nonidentity right coset has no representative in the subgroup. -/
theorem quotientOut_not_mem_of_ne_identityCoset
    {G : Type v} [Group G] (H : Subgroup G) (q : G ⧸ H)
    (hq : q ≠ (QuotientGroup.mk (1 : G) : G ⧸ H)) :
    q.out ∉ H := by
  intro hout
  apply hq
  calc
    q = QuotientGroup.mk q.out := (QuotientGroup.out_eq' q).symm
    _ = QuotientGroup.mk (1 : G) := by
      simpa using (QuotientGroup.mk_mul_of_mem (1 : G) hout)

/-- Outside the involution centralizer, a conjugate cannot commute with the
involution under the standard isolation hypothesis. -/
theorem conjugate_not_commute_of_not_mem_centralizer
    {G : Type v} [Group G] (z g : G)
    (hisolated : ∀ x : G,
      (x * z * x⁻¹) * z = z * (x * z * x⁻¹) → x * z * x⁻¹ = z)
    (hg : g ∉ Subgroup.centralizer ({z} : Set G)) :
    ¬ (g * z * g⁻¹) * z = z * (g * z * g⁻¹) := by
  intro hcomm
  apply hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have heq := hisolated g hcomm
  have h := congrArg (fun x : G => x * g) heq
  simpa [mul_assoc] using h

/-- Hence every nonidentity transfer representative conjugates the isolated
involution to a noncommuting involution. -/
theorem nonidentity_transferRepresentative_conjugate_not_commute
    {G : Type v} [Group G] (z : G)
    (hisolated : ∀ x : G,
      (x * z * x⁻¹) * z = z * (x * z * x⁻¹) → x * z * x⁻¹ = z)
    (q : G ⧸ Subgroup.centralizer ({z} : Set G))
    (hq : q ≠ (QuotientGroup.mk (1 : G) :
      G ⧸ Subgroup.centralizer ({z} : Set G))) :
    ¬ (q.out * z * q.out⁻¹) * z = z * (q.out * z * q.out⁻¹) := by
  exact conjugate_not_commute_of_not_mem_centralizer z q.out hisolated
    (quotientOut_not_mem_of_ne_identityCoset
      (Subgroup.centralizer ({z} : Set G)) q hq)

/-- The preceding noncommutation conclusion under the actual local Z-star
hypotheses. -/
theorem nonidentity_transferRepresentative_conjugate_not_commute_of_weaklyClosed
    {G : Type v} [Group G] [Finite G]
    (S : Sylow 2 G) (z : G)
    (hzI : IsInvolution z)
    (hzCentral : ∀ s, s ∈ (S : Subgroup G) → s * z = z * s)
    (hzWeak : IsWeaklyClosedInSylow z (S : Subgroup G))
    (q : G ⧸ Subgroup.centralizer ({z} : Set G))
    (hq : q ≠ (QuotientGroup.mk (1 : G) :
      G ⧸ Subgroup.centralizer ({z} : Set G))) :
    ¬ (q.out * z * q.out⁻¹) * z = z * (q.out * z * q.out⁻¹) := by
  exact nonidentity_transferRepresentative_conjugate_not_commute z
    (isolated_of_central_weaklyClosed
      S z hzI hzCentral hzWeak) q hq

/-- Termwise annihilation implies annihilation of the full nonidentity-coset
Brauer remainder.  Thus the remaining block-theoretic input can be supplied
one coset at a time. -/
theorem mul_centralizerRestriction_remainder_eq_zero_of_each
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (z : G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)))
    (hterm : ∀ q : G ⧸ Subgroup.centralizer ({z} : Set G),
      q ≠ (QuotientGroup.mk (1 : G) :
        G ⧸ Subgroup.centralizer ({z} : Set G)) →
      b * BrauerMapScratch.centralizerRestriction R z
        (conjugationMap R (Subgroup.centralizer ({z} : Set G)) q.out b) = 0) :
    b * BrauerMapScratch.centralizerRestriction R z
        (relativeTransferRemainder R
          (Subgroup.centralizer ({z} : Set G)) b) = 0 := by
  classical
  let H := Subgroup.centralizer ({z} : Set G)
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let q0 : G ⧸ H := QuotientGroup.mk (1 : G)
  change b * BrauerMapScratch.centralizerRestriction R z
      (∑ q ∈ (Finset.univ.erase q0), conjugationMap R H q.out b) = 0
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro q hq
  apply hterm q
  exact (Finset.mem_erase.mp hq).1

/-- Per-coset cross-term orthogonality is sufficient for principal Brauer
equality.  Feit's defect/admissibility argument is needed precisely to build
the hypothesis below from the noncommutation fact above. -/
theorem involutionPrincipalBrauerEquality_of_extraFactor_each_crossTerm_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) (hz : z * z = 1)
    (hterm : ∀ q : G ⧸ Subgroup.centralizer ({z} : Set G),
      q ≠ (QuotientGroup.mk (1 : G) :
        G ⧸ Subgroup.centralizer ({z} : Set G)) →
      extraBrauerFactor d z * BrauerMapScratch.centralizerRestriction
        (BrauerBlockReduction.principalResidueField d) z
        (conjugationMap (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer ({z} : Set G)) q.out
          (extraBrauerFactor d z)) = 0) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z := by
  apply involutionPrincipalBrauerEquality_of_extraFactor_crossTerms_zero d z hz
  exact mul_centralizerRestriction_remainder_eq_zero_of_each z
    (extraBrauerFactor d z) hterm

/-! ## Exact recovery for an isolated involution

For an isolated involution, left multiplication by the involution pairs all
nonidentity centralizer cosets.  In characteristic two the paired Brauer
terms cancel, so relative transfer followed by centralizer restriction is
exactly the identity.  This supplies the missing recovery hypothesis above
without any block-correspondence input. -/

/-- Conjugating a subgroup-algebra element by `z * g` or by `g` has the same
restriction to `C_G(z)`. -/
lemma centralizerRestriction_conjugationMap_z_mul
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z g : G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))) :
    BrauerMapScratch.centralizerRestriction R z
        (conjugationMap R (Subgroup.centralizer ({z} : Set G)) (z * g) b) =
      BrauerMapScratch.centralizerRestriction R z
        (conjugationMap R (Subgroup.centralizer ({z} : Set G)) g b) := by
  rw [conjugationMap_apply, conjugationMap_apply]
  simp only [map_mul, mul_inv_rev]
  let a := MonoidAlgebra.of R G g *
    subgroupSubtypeMap R (Subgroup.centralizer ({z} : Set G)) b *
      MonoidAlgebra.of R G g⁻¹
  suffices hmain : BrauerMapScratch.centralizerRestriction R z
      (MonoidAlgebra.of R G z * a * MonoidAlgebra.of R G z⁻¹) =
        BrauerMapScratch.centralizerRestriction R z a by
    simpa only [a, mul_assoc] using hmain
  apply Finsupp.ext
  intro h
  have hh : (h : G) * z = z * (h : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp h.property
  change
    (MonoidAlgebra.of R G z * a * MonoidAlgebra.of R G z⁻¹) (h : G) =
      a (h : G)
  rw [show MonoidAlgebra.of R G z⁻¹ =
      MonoidAlgebra.single z⁻¹ 1 by rfl,
    MonoidAlgebra.mul_single_apply,
    show MonoidAlgebra.of R G z = MonoidAlgebra.single z 1 by rfl,
    MonoidAlgebra.single_mul_apply]
  simp only [one_mul, mul_one]
  congr 1
  calc
    z⁻¹ * ((h : G) * (z⁻¹)⁻¹) = z⁻¹ * ((h : G) * z) := by simp
    _ = z⁻¹ * (z * (h : G)) := by rw [hh]
    _ = (h : G) := by simp

/-- Under the representative form of isolation, the only right centralizer
coset fixed by left multiplication by `z` is the identity coset. -/
lemma fixedCoset_eq_one_of_isolated
    {G : Type u} [Group G]
    (z : G) (hz : z * z = 1)
    (hiso : ∀ g : G,
      g⁻¹ * z * g ∈ Subgroup.centralizer ({z} : Set G) →
        g ∈ Subgroup.centralizer ({z} : Set G))
    (q : G ⧸ Subgroup.centralizer ({z} : Set G))
    (hq : z • q = q) :
    q = (1 : G) := by
  let H := Subgroup.centralizer ({z} : Set G)
  have hmk : (z * q.out : G ⧸ H) = (q.out : G ⧸ H) := by
    calc
      (z * q.out : G ⧸ H) = z • q := by
        simpa only [smul_eq_mul] using
          (MulAction.Quotient.mk_smul_out H z q)
      _ = q := hq
      _ = (q.out : G ⧸ H) := (QuotientGroup.out_eq' q).symm
  have hmem : q.out⁻¹ * z * q.out ∈ H := by
    have hrel := QuotientGroup.eq.mp hmk
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
    simpa [hzinv, mul_assoc] using hrel
  have hout : q.out ∈ H := hiso q.out hmem
  rw [← QuotientGroup.out_eq' q]
  apply (QuotientGroup.eq).2
  simpa using H.inv_mem hout

/-- For an isolated involution in characteristic two, restriction to its
centralizer is a left inverse to relative transfer on central elements. -/
theorem centralizerRestriction_relativeTransfer_eq_self_of_isolated
    {R : Type u} {G : Type v}
    [CommRing R] [CharP R 2] [Group G] [Finite G]
    (z : G) (hz : z * z = 1)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)))
    (hb : b ∈ Set.center
      (MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))))
    (hiso : ∀ g : G,
      g⁻¹ * z * g ∈ Subgroup.centralizer ({z} : Set G) →
        g ∈ Subgroup.centralizer ({z} : Set G)) :
    BrauerMapScratch.centralizerRestriction R z
        (relativeTransfer R (Subgroup.centralizer ({z} : Set G)) b) = b := by
  classical
  let H := Subgroup.centralizer ({z} : Set G)
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  letI : CharP (MonoidAlgebra R H) 2 :=
    charP_of_injective_algebraMap' R 2
  let q0 : G ⧸ H := (1 : G)
  have hzH : z ∈ H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hzq0 : z • q0 = q0 := by
    change (z * (1 : G) : G ⧸ H) = (1 : G)
    apply (QuotientGroup.eq).2
    simpa using hzH
  have hterm (q : G ⧸ H) :
      BrauerMapScratch.centralizerRestriction R z
          (conjugationMap R H (z • q).out b) =
        BrauerMapScratch.centralizerRestriction R z
          (conjugationMap R H q.out b) := by
    have hout : conjugationMap R H (z • q).out b =
        conjugationMap R H (z * q.out) b := by
      apply conjugationMap_out_eq_of_mk_eq H (z • q) (z * q.out)
      · simpa only [smul_eq_mul] using
          (MulAction.Quotient.mk_smul_out H z q)
      · exact hb
    rw [hout]
    exact centralizerRestriction_conjugationMap_z_mul z q.out b
  have hrem :
      BrauerMapScratch.centralizerRestriction R z
          (relativeTransferRemainder R H b) = 0 := by
    rw [relativeTransferRemainder, map_sum]
    let s : Finset (G ⧸ H) := Finset.univ.erase q0
    have hsum : (∑ q ∈ s,
        BrauerMapScratch.centralizerRestriction R z
          (conjugationMap R H q.out b)) = 0 := by
      refine Finset.sum_involution
        (g := fun q _hq => z • q)
        (hg₁ := ?_) (hg₃ := ?_) (g_mem := ?_) (hg₄ := ?_)
      · intro q hq
        rw [hterm]
        exact CharTwo.add_self_eq_zero _
      · intro q hq _hne hfix
        have hq0 : q = q0 := by
          exact fixedCoset_eq_one_of_isolated z hz (by simpa [H] using hiso)
            q hfix
        exact (Finset.mem_erase.mp hq).1 hq0
      · intro q hq
        apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_univ _⟩
        intro hq0
        have hrecover : q = z • (z • q) := by
          rw [← mul_smul, hz, one_smul]
        have hneq : q ≠ q0 := (Finset.mem_erase.mp hq).1
        apply hneq
        calc
          q = z • (z • q) := hrecover
          _ = z • q0 := by rw [hq0]
          _ = q0 := hzq0
      · intro q hq
        rw [← mul_smul, hz, one_smul]
    simpa only [s, q0] using hsum
  rw [centralizerRestriction_relativeTransfer_eq_add_remainder z b hb]
  change b + BrauerMapScratch.centralizerRestriction R z
      (relativeTransferRemainder R H b) = b
  rw [hrem, add_zero]

/-- Glauberman's usual isolation condition implies the representative form
used by the transfer pairing. -/
theorem representativeIsolation_of_isolated
    {G : Type v} [Group G] (z : G)
    (hisolated : ∀ x : G,
      (x * z * x⁻¹) * z = z * (x * z * x⁻¹) → x * z * x⁻¹ = z) :
    ∀ g : G, g⁻¹ * z * g ∈ Subgroup.centralizer ({z} : Set G) →
      g ∈ Subgroup.centralizer ({z} : Set G) := by
  intro g hg
  have hcomm :
      (g⁻¹ * z * (g⁻¹)⁻¹) * z = z * (g⁻¹ * z * (g⁻¹)⁻¹) := by
    simpa using (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have heq : g⁻¹ * z * g = z := by
    simpa using hisolated g⁻¹ hcomm
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := congrArg (fun x : G => g * x) heq
  simpa [mul_assoc] using h.symm

/-- Principal Brauer equality at an isolated involution, obtained solely from
the characteristic-two relative-transfer pairing and the primitive-corner
argument. -/
theorem involutionPrincipalBrauerEquality_of_isolated
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hzI : IsInvolution z)
    (hisolated : ∀ x : G,
      (x * z * x⁻¹) * z = z * (x * z * x⁻¹) → x * z * x⁻¹ = z) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z := by
  let b := extraBrauerFactor d z
  have hz : z * z = 1 := by simpa [pow_two] using hzI.2
  have hbCenter : b ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G))) := by
    simpa [b] using extraBrauerFactor_mem_center d z
  have hbIdem : IsIdempotentElem b := by
    simpa [b] using extraBrauerFactor_isIdempotent d z hz
  have hrestriction :
      BrauerMapScratch.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z
          (relativeTransfer (BrauerBlockReduction.principalResidueField d)
            (Subgroup.centralizer ({z} : Set G)) b) = b :=
    centralizerRestriction_relativeTransfer_eq_self_of_isolated z hz b hbCenter
      (representativeIsolation_of_isolated z hisolated)
  have hrecover : b * BrauerMapScratch.centralizerRestriction
      (BrauerBlockReduction.principalResidueField d) z
      (relativeTransfer (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G)) b) = b := by
    rw [hrestriction, hbIdem.eq]
  have hzero : b = 0 :=
    centralizerFactor_eq_zero_of_relativeTransfer_recovery d z hz b hbCenter
      (by simpa [b] using extraBrauerFactor_mul_local_eq_zero d z hz)
      (by simpa [b] using extraBrauerFactor_mul_brauer_eq_self d z hz)
      hrecover
  change CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer ({z} : Set G)) =
    BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  have hextra : extraBrauerFactor d z = 0 := by simpa [b] using hzero
  exact (sub_eq_zero.mp hextra).symm

/-- In particular, the local Z-star hypotheses force principal Brauer
equality at the distinguished weakly closed involution. -/
theorem involutionPrincipalBrauerEquality_of_weaklyClosed
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (S : Sylow 2 G) (z : G)
    (hzI : IsInvolution z)
    (hzCentral : ∀ s, s ∈ (S : Subgroup G) → s * z = z * s)
    (hzWeak : IsWeaklyClosedInSylow z (S : Subgroup G)) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z := by
  exact involutionPrincipalBrauerEquality_of_isolated d z hzI
    (isolated_of_central_weaklyClosed S z hzI hzCentral hzWeak)

end RelativeTransferBrauer
end Submission.ZStar
