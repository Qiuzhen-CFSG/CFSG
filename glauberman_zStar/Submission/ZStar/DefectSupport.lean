import Mathlib

/-!
# Maximal 2-subgroup coefficient support

This file records the elementary part of the defect-group setup used in the
principal-block proof.  For a group-algebra element `e`, a 2-subgroup `Q` has
coefficient support when some coefficient of `e` is indexed by an element
centralized by `Q`.  A maximal such subgroup contains every central
2-subgroup.

This is deliberately only a coefficient-support statement.  It does not
identify support with a block defect group, and it does not assert any
Brauer-correspondence or principal-block equality.
-/

noncomputable section

namespace Submission.ZStar
namespace DefectSupport

open Subgroup

universe u v

attribute [local instance] Fintype.ofFinite

/-- Coefficient restriction from `R[G]` to the group algebra of the
centralizer of a subgroup.  Multiplicativity on central elements is the
separate Brauer-homomorphism theorem; this additive map is enough to express
defect support. -/
def subgroupCentralizerRestriction
    (R : Type u) {G : Type v} [Semiring R] [Group G]
    (Q : Subgroup G) :
    MonoidAlgebra R G →+ MonoidAlgebra R
      (Subgroup.centralizer (Q : Set G)) :=
  Finsupp.comapDomain.addMonoidHom
    (Subgroup.centralizer (Q : Set G)).subtype_injective

@[simp] theorem subgroupCentralizerRestriction_apply
    {R : Type u} {G : Type v} [Semiring R] [Group G]
    (Q : Subgroup G) (e : MonoidAlgebra R G)
    (x : Subgroup.centralizer (Q : Set G)) :
    subgroupCentralizerRestriction R Q e x = e (x : G) := rfl

/-- A 2-subgroup `Q` is visible in the coefficient support of `e` if a
nonzero coefficient of `e` is indexed by an element centralized by `Q`. -/
def HasTwoCoefficientSupport
    {R : Type u} {G : Type v} [Semiring R] [Group G] [Finite G]
    (e : MonoidAlgebra R G) (Q : Subgroup G) : Prop :=
  IsPGroup 2 Q ∧
    ∃ x : G, x ∈ Subgroup.centralizer (Q : Set G) ∧ e x ≠ 0

/-- Maximality is measured by the cardinality of the supporting 2-subgroup. -/
def IsMaximalTwoCoefficientSupport
    {R : Type u} {G : Type v} [Semiring R] [Group G] [Finite G]
    (e : MonoidAlgebra R G) (Q : Subgroup G) : Prop :=
  HasTwoCoefficientSupport e Q ∧
    ∀ Q' : Subgroup G, HasTwoCoefficientSupport e Q' →
      Nat.card Q' ≤ Nat.card Q

/-- Coefficient support is transported by an equivalence of the indexing
groups. -/
theorem hasTwoCoefficientSupport_mapDomainRingEquiv
    {R : Type u} {G : Type v} {H : Type*}
    [Semiring R] [Group G] [Group H] [Finite G] [Finite H]
    (E : G ≃* H) (e : MonoidAlgebra R G) (Q : Subgroup G)
    (hQ : HasTwoCoefficientSupport e Q) :
    HasTwoCoefficientSupport
      (MonoidAlgebra.mapDomainRingEquiv R E e)
      (Q.map E.toMonoidHom) := by
  rcases hQ with ⟨hQp, x, hxcentral, hxcoeff⟩
  refine ⟨hQp.map E.toMonoidHom, E x, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
    simpa using congrArg E
      (Subgroup.mem_centralizer_iff.mp hxcentral q hq)
  · simpa [MonoidAlgebra.mapDomainRingEquiv_apply] using hxcoeff

/-- Maximal coefficient support, and hence the coefficient-theoretic defect
group, is invariant under an equivalence of the indexing groups. -/
theorem isMaximalTwoCoefficientSupport_mapDomainRingEquiv
    {R : Type u} {G : Type v} {H : Type*}
    [Semiring R] [Group G] [Group H] [Finite G] [Finite H]
    (E : G ≃* H) (e : MonoidAlgebra R G) (Q : Subgroup G)
    (hQ : IsMaximalTwoCoefficientSupport e Q) :
    IsMaximalTwoCoefficientSupport
      (MonoidAlgebra.mapDomainRingEquiv R E e)
      (Q.map E.toMonoidHom) := by
  refine ⟨hasTwoCoefficientSupport_mapDomainRingEquiv E e Q hQ.1, ?_⟩
  intro D hD
  let D' : Subgroup G := D.map E.symm.toMonoidHom
  have hD' : HasTwoCoefficientSupport e D' := by
    have hback := hasTwoCoefficientSupport_mapDomainRingEquiv
      E.symm (MonoidAlgebra.mapDomainRingEquiv R E e) D hD
    simpa only [D', ← MonoidAlgebra.symm_mapDomainRingEquiv,
      RingEquiv.symm_apply_apply] using hback
  have hbound : Nat.card D' ≤ Nat.card Q := hQ.2 D' hD'
  calc
    Nat.card D = Nat.card D' := Nat.card_congr
      (E.symm.subgroupMap D).toEquiv
    _ ≤ Nat.card Q := hbound
    _ = Nat.card (Q.map E.toMonoidHom) := Nat.card_congr
      (E.subgroupMap Q).toEquiv

private theorem bot_has_support
    {G : Type v} [Group G] [Finite G]
    (x : G) :
    x ∈ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : y = 1 := Subgroup.mem_bot.mp hy
  simp [hy']

private theorem exists_nonzero_coeff
    {R : Type u} {G : Type v} [Semiring R] [Group G]
    (e : MonoidAlgebra R G) (he : e ≠ 0) :
    ∃ x : G, e x ≠ 0 := by
  by_contra h
  push Not at h
  apply he
  ext x
  exact h x

/-- Nonvanishing of subgroup coefficient restriction is exactly the
existence of a nonzero coefficient centralized by the subgroup. -/
theorem subgroupCentralizerRestriction_ne_zero_iff
    {R : Type u} {G : Type v} [Semiring R] [Group G]
    (e : MonoidAlgebra R G) (Q : Subgroup G) :
    subgroupCentralizerRestriction R Q e ≠ 0 ↔
      ∃ x : G, x ∈ Subgroup.centralizer (Q : Set G) ∧ e x ≠ 0 := by
  constructor
  · intro hne
    obtain ⟨x, hx⟩ := exists_nonzero_coeff
      (subgroupCentralizerRestriction R Q e) hne
    exact ⟨x, x.2, by simpa using hx⟩
  · rintro ⟨x, hxcentral, hx⟩ hzero
    let xCentral : Subgroup.centralizer (Q : Set G) := ⟨x, hxcentral⟩
    have hcoeff := congrArg
      (fun a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)) =>
        a xCentral) hzero
    change e x = 0 at hcoeff
    exact hx hcoeff

/-- Coefficient support can equivalently be stated as nonvanishing of the
subgroup Brauer restriction. -/
theorem hasTwoCoefficientSupport_iff_restriction_ne_zero
    {R : Type u} {G : Type v} [Semiring R] [Group G] [Finite G]
    (e : MonoidAlgebra R G) (Q : Subgroup G) :
    HasTwoCoefficientSupport e Q ↔
      IsPGroup 2 Q ∧ subgroupCentralizerRestriction R Q e ≠ 0 := by
  rw [HasTwoCoefficientSupport,
    subgroupCentralizerRestriction_ne_zero_iff]

/-- Every nonzero group-algebra element has a maximal supporting 2-subgroup. -/
theorem exists_isMaximalTwoCoefficientSupport
    {R : Type u} {G : Type v} [Semiring R] [Group G] [Finite G]
    (e : MonoidAlgebra R G) (he : e ≠ 0) :
    ∃ Q : Subgroup G, IsMaximalTwoCoefficientSupport e Q := by
  classical
  letI : Fintype (Subgroup G) := Fintype.ofFinite (Subgroup G)
  obtain ⟨x, hx⟩ := exists_nonzero_coeff e he
  let candidates : Finset (Subgroup G) :=
    Finset.univ.filter (HasTwoCoefficientSupport e)
  have hbot : (⊥ : Subgroup G) ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨IsPGroup.of_bot, x, bot_has_support x, hx⟩
  have hcand : candidates.Nonempty := ⟨⊥, hbot⟩
  obtain ⟨Q, hQcand, hQmax⟩ :=
    Finset.exists_max_image candidates (fun K : Subgroup G => Nat.card K)
      hcand
  refine ⟨Q, ?_⟩
  refine ⟨?_, ?_⟩
  · exact (Finset.mem_filter.mp hQcand).2
  · intro Q' hQ'
    exact hQmax Q' ((Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ'⟩))

private theorem central_subgroup_normalizes
    {G : Type v} [Group G]
    {Z Q : Subgroup G} (hZ : Z ≤ Subgroup.center G) :
    Z ≤ Subgroup.normalizer Q := by
  intro z hz
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor <;> intro hq
  · have hcomm : z * q = q * z :=
      (Subgroup.mem_center_iff.mp (hZ hz) q).symm
    simpa [hcomm] using hq
  · have hcomm : z * q = q * z :=
      (Subgroup.mem_center_iff.mp (hZ hz) q).symm
    simpa [hcomm] using hq

private theorem central_subgroup_preserves_support
    {R : Type u} {G : Type v} [Semiring R] [Group G] [Finite G]
    (e : MonoidAlgebra R G) (Q Z : Subgroup G)
    (hQ : HasTwoCoefficientSupport e Q)
    (hZp : IsPGroup 2 Z) (hZcenter : Z ≤ Subgroup.center G) :
    HasTwoCoefficientSupport e (Q ⊔ Z) := by
  rcases hQ with ⟨hQp, x, hxcentral, hxcoeff⟩
  have hQcx : Q ≤ Subgroup.centralizer ({x} : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hxcentral q hq
  have hZcx : Z ≤ Subgroup.centralizer ({x} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp (hZcenter hz) x).symm
  have hsupcx : Q ⊔ Z ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le hQcx hZcx
  have hnorm : Z ≤ Subgroup.normalizer Q :=
    central_subgroup_normalizes hZcenter
  have hsupP : IsPGroup 2 (Q ⊔ Z : Subgroup G) := by
    have hsupP' : IsPGroup 2 (Z ⊔ Q : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hZp hQp hnorm
    rw [sup_comm]
    exact hsupP'
  refine ⟨hsupP, x, ?_, hxcoeff⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hsupcx hy)

/-- Every central 2-subgroup is contained in a maximal coefficient-support
2-subgroup. -/
theorem centralTwoSubgroup_le_of_isMaximalTwoCoefficientSupport
    {R : Type u} {G : Type v} [Semiring R] [Group G] [Finite G]
    (e : MonoidAlgebra R G) (Q : Subgroup G)
    (hQ : IsMaximalTwoCoefficientSupport e Q)
    (Z : Subgroup G) (hZp : IsPGroup 2 Z)
    (hZcenter : Z ≤ Subgroup.center G) :
    Z ≤ Q := by
  have hsup := central_subgroup_preserves_support e Q Z hQ.1 hZp hZcenter
  have hcard : Nat.card (Q ⊔ Z : Subgroup G) ≤ Nat.card Q :=
    hQ.2 (Q ⊔ Z) hsup
  have hle : Q ≤ Q ⊔ Z := le_sup_left
  have heq : Q = Q ⊔ Z :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  intro z hz
  rw [heq]
  exact (le_sup_right : Z ≤ Q ⊔ Z) hz

/-- A normal `2`-subgroup is contained in a maximal coefficient-support
subgroup whenever every nonzero coefficient is indexed by an element
centralizing that normal subgroup.

This is the support-theoretic form needed for an element of `K[C_G(P)]`
embedded in a larger group algebra: adjoining `P` to a supporting subgroup
preserves the same nonzero coefficient. -/
theorem normalTwoSubgroup_le_of_isMaximalTwoCoefficientSupport_of_coeff_centralizes
    [Fact (Nat.Prime 2)]
    {R : Type u} {G : Type v} [Semiring R] [Group G] [Finite G]
    (e : MonoidAlgebra R G) (D : Subgroup G)
    (hD : IsMaximalTwoCoefficientSupport e D)
    (P : Subgroup G) (hPp : IsPGroup 2 P) (hPnormal : P.Normal)
    (hcoeff : ∀ x : G, e x ≠ 0 →
      x ∈ Subgroup.centralizer (P : Set G)) :
    P ≤ D := by
  rcases hD.1 with ⟨hDp, x, hxD, hxcoeff⟩
  letI : P.Normal := hPnormal
  have hPcx : P ≤ Subgroup.centralizer ({x} : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hcoeff x hxcoeff) p hp
  have hDcx : D ≤ Subgroup.centralizer ({x} : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hxD d hd
  have hsupP : IsPGroup 2 (P ⊔ D : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left hPp hDp
  have hsupSupport : HasTwoCoefficientSupport e (P ⊔ D) := by
    refine ⟨hsupP, x, ?_, hxcoeff⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (sup_le hPcx hDcx hy)
  have hcard : Nat.card (P ⊔ D : Subgroup G) ≤ Nat.card D :=
    hD.2 (P ⊔ D) hsupSupport
  have hle : D ≤ P ⊔ D := le_sup_right
  have heq : D = P ⊔ D :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  intro p hp
  rw [heq]
  exact (le_sup_left : P ≤ P ⊔ D) hp

/-- In particular, a central involution belongs to every maximal supporting
2-subgroup. -/
theorem centralInvolution_mem_of_isMaximalTwoCoefficientSupport
    {R : Type u} {G : Type v} [Semiring R] [Group G] [Finite G]
    (e : MonoidAlgebra R G) (Q : Subgroup G)
    (hQ : IsMaximalTwoCoefficientSupport e Q)
    (z : G) (hzne : z ≠ 1) (hzsq : z * z = 1)
    (hzcenter : z ∈ Subgroup.center G) :
    z ∈ Q := by
  have hzorder : orderOf z = 2 := by
    apply orderOf_eq_prime (p := 2)
    · simpa [pow_two] using hzsq
    · exact hzne
  let Z : Subgroup G := Subgroup.zpowers z
  have hZp : IsPGroup 2 Z := by
    apply IsPGroup.of_card (p := 2) (G := Z) (n := 1)
    change Nat.card (Subgroup.zpowers z) = 2 ^ 1
    rw [Nat.card_zpowers, hzorder]
    norm_num
  have hZcenter : Z ≤ Subgroup.center G := by
    exact Subgroup.zpowers_le.mpr hzcenter
  have hZQ : Z ≤ Q :=
    centralTwoSubgroup_le_of_isMaximalTwoCoefficientSupport
      e Q hQ Z hZp hZcenter
  exact hZQ (Subgroup.mem_zpowers z)

/-- For `H = C_G(z)`, maximal coefficient support supplies the admissibility
inequality `C_G(Q) ≤ H` after the supporting subgroup is mapped to `G`.

This is the elementary admissibility step in the Juhász proof of Brauer's
Third Main Theorem. -/
theorem ambientCentralizer_le_involutionCentralizer_of_maximalSupport
    {R : Type u} {G : Type v} [Semiring R] [Group G] [Finite G]
    (z : G) (hzne : z ≠ 1) (hzsq : z * z = 1)
    (e : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)))
    (Q : Subgroup (Subgroup.centralizer ({z} : Set G)))
    (hQ : IsMaximalTwoCoefficientSupport e Q) :
    Subgroup.centralizer
        ((Q.map (Subgroup.centralizer ({z} : Set G)).subtype :
          Subgroup G) : Set G) ≤
      Subgroup.centralizer ({z} : Set G) := by
  let H : Subgroup G := Subgroup.centralizer ({z} : Set G)
  have hzHmem : z ∈ H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  let zH : H := ⟨z, hzHmem⟩
  have hzHne : zH ≠ 1 := by
    intro h
    apply hzne
    exact congrArg Subtype.val h
  have hzHsq : zH * zH = 1 := by
    apply Subtype.ext
    exact hzsq
  have hzHcenter : zH ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp h.2
  have hzHQ : zH ∈ Q :=
    centralInvolution_mem_of_isMaximalTwoCoefficientSupport
      (G := H) e Q hQ zH hzHne hzHsq hzHcenter
  have hzmap : z ∈ Q.map H.subtype := by
    exact Subgroup.mem_map.mpr ⟨zH, hzHQ, rfl⟩
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hg z hzmap).symm

end DefectSupport
end Submission.ZStar
