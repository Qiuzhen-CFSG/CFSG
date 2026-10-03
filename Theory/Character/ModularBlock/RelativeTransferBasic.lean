module
public import Theory.Character.ModularBlock.BrauerMap
public import Theory.Character.ModularBlock.Basic
public import Mathlib.GroupTheory.Coset.Basic

/-!
# Relative transfer of central subgroup-algebra elements

Relative transfer sums the conjugates of a subgroup-algebra element over
the finite coset space. For a central subgroup element, conjugation by an
element of the subgroup leaves it unchanged, so each summand depends only
on its coset. Reindexing cosets shows that the transferred element is
central in the ambient group algebra.

The module also records the coefficient transport for subgroup embeddings
and conjugation, preservation of augmentation by conjugation, the
index-times-augmentation formula, and compatibility with coefficient-ring
maps. The conjugation maps and finite sum are exposed because subsequent
Brauer restriction calculations use their actual coefficients and summands.

Ported from the generic transfer algebra at the start of
`Submission/ZStar/RelativeTransferBrauer.lean` at revision `c3503435`
of `public/lean-eval/glauberman_zStar`. No principal-block or weak-closure
hypotheses enter these generic results. Theorem statements use the current
group-algebra coefficient interface.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ModularBlock.RelativeTransferBrauer
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
  simp [MonoidAlgebra.of]

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
    (conjugationMap R H g b).coeff (g * (h : G) * g⁻¹) = b.coeff h := by
  change Finsupp.mapDomain
      ((MulAut.conj g).toMonoidHom.comp H.subtype) b.coeff
        (((MulAut.conj g).toMonoidHom.comp H.subtype) h) = b.coeff h
  exact Finsupp.mapDomain_apply
    ((MulAut.conj g).injective.comp H.subtype_injective) b.coeff h

/-- Coefficient form after restriction to an involution centralizer. -/
@[simp] theorem centralizerRestriction_conjugationMap_apply_image
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (H : Subgroup G) (z g : G) (b : MonoidAlgebra R H) (h : H)
    (hmem : g * (h : G) * g⁻¹ ∈
      Subgroup.centralizer ({z} : Set G)) :
    (BrauerMap.centralizerRestriction R z
        (conjugationMap R H g b)).coeff
        ⟨g * (h : G) * g⁻¹, hmem⟩ = b.coeff h := by
  rw [BrauerMap.centralizerRestriction_apply]
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
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
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
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
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
    groupAlgebraAugmentation R G (conjugationMap R H g b) =
      groupAlgebraAugmentation R H b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp [map_add, hb, hc]
  | single h r => simp [conjugationMap_single,
      groupAlgebraAugmentation_single]

/-- The augmentation of a relative transfer is the subgroup index times the
augmentation of the transferred element. -/
theorem augmentation_relativeTransfer
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (H : Subgroup G) (b : MonoidAlgebra R H) :
    groupAlgebraAugmentation R G (relativeTransfer R H b) =
      (Fintype.card (G ⧸ H) : R) *
        groupAlgebraAugmentation R H b := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
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
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  rw [relativeTransfer, relativeTransfer, map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp [map_add, hb, hc]
  | single h r => simp [conjugationMap_single]


end ModularBlock.RelativeTransferBrauer

