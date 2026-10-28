module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.ToddQuotient
public import Theory.GroupTheory.SolvableRadical

/-!
# Intrinsic overlap kernels and the actual quotient correction

The original core equals [O2(I),Rad(I)]. For the upper inclusion, the
solvable radical has trivial image in S6, so both commutator factors map
into the abelian translations of the parity affine quotient. The
commutator therefore lies in Q A and in O2(I), hence in Q. The lower
inclusion is the earlier [O2(I),A]=Q, since Q A is solvable and normal.
This proves that Q is characteristic without a preserved-cubic input.

Every automorphic image of the cubic remains in Rad(I) and has exponent
three. Its binary affine image vanishes, proving that Q A is characteristic
as well. Thus every automorphism of the original I descends to its literal
quotient, where its factorization uses the constructed Todd correction.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606.
The remaining lift from Q A to Q, the automorphism kernel on Q, and the
full local-map/edge alignment are not asserted here.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups
open Sporadic.Mathieu MathieuCode Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)

include a in
private theorem cubicLift_solvable : Group.IsSolvable (twoThreeCore (centralizer z)) := by
  let : Group.IsNilpotent (core z) := (IsPGroup.of_card (p := 2) (n := 13) h.core_card).isNilpotent
  let : Group.IsNilpotent (cubicSylowImage a.e a.X) :=
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using cubicSylowImage_card h a.e a.X)).isNilpotent
  rw [←cubicLift_eq_twoThreeCore h a.e,←core_sup_cubicSylow a.e h a.X]
  exact Group.isSolvable_sup_of_normal_left _ _

private theorem cubicLift_le_radical :
    (twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a) ≤ solvableRadical (PlaneOverlap a) := by
  let := cubicLift_solvable a
  have hs : Group.IsSolvable ((twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (overlap_cubicLift_le a)).toMonoidHom)
      (subgroupOfEquivOfLe (overlap_cubicLift_le a)).injective
  exact le_solvableRadical _ inferInstance hs

private theorem overlapPartProjection_radical :
    solvableRadical (PlaneOverlap a) ≤ (overlapPartProjection a).ker := by
  classical
  let R := (solvableRadical (PlaneOverlap a)).map (overlapPartProjection a)
  let : R.Normal := Subgroup.Normal.map inferInstance _ (overlapPartProjection_surjective a)
  let : Group.IsSolvable R := Group.isSolvable_of_surjective
    ((overlapPartProjection a).subgroupMap_surjective _)
  have he : R = ⊥ := by
    by_contra hn
    have hl := Equiv.Perm.alternatingGroup_le_of_normal
      (by rw [Nat.card_eq_fintype_card,card_sextetPart]; decide :
        5 ≤ Nat.card (SextetPart a.sextet)) ((nontrivial_iff_ne_bot R).mpr hn)
    let : Group.IsPerfect (alternatingGroup (SextetPart a.sextet)) :=
      ⟨commutator_alternatingGroup_eq_top
        (by rw [Nat.card_eq_fintype_card,card_sextetPart]; decide)⟩
    let : Nontrivial (SextetPart a.sextet) := Fintype.one_lt_card_iff_nontrivial.mp
      (by rw [card_sextetPart]; decide)
    let : IsSimpleGroup (alternatingGroup (SextetPart a.sextet)) :=
      alternatingGroup.isSimpleGroup
        (by rw [Nat.card_eq_fintype_card,card_sextetPart]; decide)
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (SextetPart a.sextet))
      (Group.isSolvable_of_isSolvable_injective (inclusion_injective hl))
  exact (Subgroup.map_eq_bot_iff _).mp he

/-- The core is an intrinsic commutator, with no preserved-cubic hypothesis.
This makes it available to every automorphism in the Section 8 argument. -/
theorem overlap_core_eq_radical_commutator :
    ⁅pCore 2 (PlaneOverlap a),solvableRadical (PlaneOverlap a)⁆ =
      (core z).subgroupOf (PlaneOverlap a) := by
  let I := PlaneOverlap a
  let K := (twoThreeCore (centralizer z)).subgroupOf I
  let S := pCore 2 I
  let R := solvableRadical I
  have hsR : S ≤ R := by
    let : Group.IsNilpotent S := pCore_isPGroup.isNilpotent
    exact le_solvableRadical _ inferInstance inferInstance
  have hcomm : ⁅S,R⁆ ≤ K := by
    change ⁅S,R⁆ ≤ (twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a)
    rw [←overlapAffineProjection_ker a]
    apply commutator_le.mpr
    intro x hx y hy
    have hrx : (overlapAffineProjection a x).right = 1 :=
      overlapPartProjection_radical a (hsR hx)
    have hry : (overlapAffineProjection a y).right = 1 := overlapPartProjection_radical a hy
    have hc : Commute (overlapAffineProjection a x) (overlapAffineProjection a y) := by
      change overlapAffineProjection a x * overlapAffineProjection a y =
        overlapAffineProjection a y * overlapAffineProjection a x
      apply SemidirectProduct.ext
      · simp only [SemidirectProduct.mul_left,hrx,hry,map_one,MulAut.one_apply]
        exact mul_comm _ _
      · simp only [SemidirectProduct.mul_right,hrx,hry]
    change overlapAffineProjection a ⁅x,y⁆ = 1
    rw [map_commutatorElement]
    exact hc.commutator_eq
  apply le_antisymm
  · intro x hx
    have hk := hcomm hx
    let y : K := ⟨x,hk⟩
    have hy : y ∈ pCore 2 K := by
      rw [←(inferInstance : K.Normal).isSubnormal.pCore_subgroupOf 2]
      change x ∈ pCore 2 I
      exact commutator_le_left _ _ hx
    let e : K ≃* twoThreeCore (centralizer z) := subgroupOfEquivOfLe (overlap_cubicLift_le a)
    have he : e y ∈ pCore 2 (twoThreeCore (centralizer z)) := by
      rw [←pCore_map_iso 2 e]
      exact mem_map_of_mem e.toMonoidHom hy
    rw [twoCore_twoThreeCore h] at he
    exact he
  · rw [←overlap_core_eq_commutator a]
    apply commutator_mono le_rfl
    apply le_trans ?_ (cubicLift_le_radical a)
    intro x hx
    have hl : cubicSylowImage a.e a.X ≤ twoThreeCore (centralizer z) := by
      rw [←cubicLift_eq_twoThreeCore h a.e,←core_sup_cubicSylow a.e h a.X]
      exact le_sup_right
    exact hl hx

instance overlap_core_characteristic : ((core z).subgroupOf (PlaneOverlap a)).Characteristic := by
  rw [←overlap_core_eq_radical_commutator a]
  infer_instance

/-- Every overlap automorphism preserves Q, before choosing any cubic correction. -/
theorem overlap_automorphism_preserves_core (f : MulAut (PlaneOverlap a)) :
    ((core z).subgroupOf (PlaneOverlap a)).map f.toMonoidHom =
      (core z).subgroupOf (PlaneOverlap a) :=
  characteristic_iff_map_eq.mp (overlap_core_characteristic a) f

private theorem overlapAffineProjection_radical_cube (x : PlaneOverlap a)
    (hx : x ∈ solvableRadical (PlaneOverlap a)) (h3 : x^3=1) :
    overlapAffineProjection a x = 1 := by
  have hr : (overlapAffineProjection a x).right = 1 := overlapPartProjection_radical a hx
  have h2 : (overlapAffineProjection a x)^2=1 := by
    have he : overlapAffineProjection a x =
        SemidirectProduct.inl (overlapAffineProjection a x).left := by
      apply SemidirectProduct.ext <;> simp [hr]
    rw [he,←map_pow]
    have hh : (overlapAffineProjection a x).left^2=1 := by
      rw [pow_two]
      change Multiplicative.ofAdd ((overlapAffineProjection a x).left.toAdd +
        (overlapAffineProjection a x).left.toAdd) = 1
      rw [←two_smul (ZMod 2),show (2 : ZMod 2)=0 from rfl,zero_smul]
      rfl
    rw [hh,map_one]
  have h3' : (overlapAffineProjection a x)^3=1 := by rw [←map_pow,h3,map_one]
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
    (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3'))

instance overlap_cubicLift_characteristic :
    ((twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a)).Characteristic := by
  apply characteristic_iff_map_le.mpr
  intro f
  let I := PlaneOverlap a
  have hA : cubicSylowImage a.e a.X ≤ I := by
    apply le_trans ?_ (overlap_cubicLift_le a)
    rw [←cubicLift_eq_twoThreeCore h a.e,←core_sup_cubicSylow a.e h a.X]
    exact le_sup_right
  have hsum : (twoThreeCore (centralizer z)).subgroupOf I =
      (core z).subgroupOf I ⊔ (cubicSylowImage a.e a.X).subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le (overlap_cubicLift_le a),Subgroup.map_sup,
      map_subgroupOf_eq_of_le ((core_le_twoThreeCore h).trans (overlap_cubicLift_le a)),
      map_subgroupOf_eq_of_le hA,core_sup_cubicSylow a.e h a.X,cubicLift_eq_twoThreeCore h a.e]
  change ((twoThreeCore (centralizer z)).subgroupOf I).map f.toMonoidHom ≤ _
  rw [hsum,Subgroup.map_sup,overlap_automorphism_preserves_core]
  apply sup_le le_sup_left
  rw [←hsum]
  rintro _ ⟨x,hx,rfl⟩
  rw [←overlapAffineProjection_ker a]
  apply overlapAffineProjection_radical_cube a (f x)
  · apply characteristic_iff_le_comap.mp (inferInstance : (solvableRadical I).Characteristic) f
    apply cubicLift_le_radical a
    have hl : cubicSylowImage a.e a.X ≤ twoThreeCore (centralizer z) := by
      rw [←cubicLift_eq_twoThreeCore h a.e,←core_sup_cubicSylow a.e h a.X]
      exact le_sup_right
    exact hl hx
  · have h3 : x^3=1 := by
      have he : (⟨x.val,hx⟩ : cubicSylowImage a.e a.X)^Nat.card (cubicSylowImage a.e a.X)=1 :=
        pow_card_eq_one'
      rw [cubicSylowImage_card h a.e a.X] at he
      exact Subtype.ext (congrArg (fun t : cubicSylowImage a.e a.X => t.val) he)
    rw [←map_pow,h3,map_one]

theorem overlap_automorphism_preserves_cubicLift (f : MulAut (PlaneOverlap a)) :
    ((twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a)).map f.toMonoidHom =
      (twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a) :=
  characteristic_iff_map_eq.mp (overlap_cubicLift_characteristic a) f

/-- Descent of an arbitrary overlap automorphism through the literal Q A.
Preservation of this kernel is proved above, rather than required as data. -/
noncomputable def overlapQuotientAut (f : MulAut (PlaneOverlap a)) :
    MulAut (OverlapCohomology.Original a.P) :=
  QuotientGroup.congr _ _ f (overlap_automorphism_preserves_cubicLift a f)

theorem overlapQuotientAut_mk (f : MulAut (PlaneOverlap a)) (x : PlaneOverlap a) :
    overlapQuotientAut a f (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ (f x) := rfl

/-- Every original overlap automorphism has, modulo Q A, an inner part
and at most the constructed point-group Todd correction. -/
theorem overlap_automorphism_quotient_factorization (f : MulAut (PlaneOverlap a)) :
    ∃ x : PlaneOverlap a,
      (∀ y : PlaneOverlap a, QuotientGroup.mk' ((twoThreeCore (centralizer z)).subgroupOf
        (PlaneOverlap a)) (f y) = QuotientGroup.mk' _ (x*y*x⁻¹)) ∨
      (∀ y : PlaneOverlap a, QuotientGroup.mk' ((twoThreeCore (centralizer z)).subgroupOf
        (PlaneOverlap a)) (f y) = QuotientGroup.mk' _
          (x * planeOverlapToddTwist a (cubicFixedWord a) y * x⁻¹)) := by
  obtain ⟨x,hx⟩ := original_all_automorphisms_todd a (overlapQuotientAut a f)
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective
    ((twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a)) x
  refine ⟨x,?_⟩
  rcases hx with hx | hx
  · left
    intro y
    have he := MulEquiv.congr_fun hx (QuotientGroup.mk' _ y)
    simpa only [overlapQuotientAut_mk,MulAut.conj_apply,map_mul,map_inv] using he
  · right
    intro y
    have he := MulEquiv.congr_fun hx (QuotientGroup.mk' _ y)
    simpa only [overlapQuotientAut_mk,MulAut.mul_apply,MulAut.conj_apply,
      cubicToddQuotientTwist_mk,map_mul,map_inv] using he
end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
