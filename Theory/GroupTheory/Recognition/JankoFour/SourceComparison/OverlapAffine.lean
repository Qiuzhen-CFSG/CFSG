module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCore
public import Theory.Representation.BinaryPermutationMulAction
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# Tetrad parity and the literal overlap quotient

The same Todd coordinates and sextet part action define a surjective map
from I = H intersect M to the affine natural group 2^4:S6. The original
Q A has trivial normal image in S6 by its order. Its cubic then vanishes
in the binary translation group, and [O2(I),A]=Q kills its whole core.
Equal finite orders identify the resulting quotient map as an isomorphism.
Thus its kernel is exactly the original Q A, with both scalar and core
retained and with explicit formulas on the actual Todd factors.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606.
This parity marking detects the Todd outer class in ToddQuotient and
identifies characteristic kernels in OverlapCharacteristic.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups
open Sporadic.Mathieu MathieuCode Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)

abbrev PlaneOverlap := a.P.M.subgroupOf (centralizer z)

noncomputable def overlapToddCoordinates : PlaneOverlap a →* ToddGroup :=
  a.P.toddEquiv.symm.toMonoidHom.comp ((pointOverlap a).subtype.comp
    (overlapPlacement a).symm.toMonoidHom)

noncomputable def overlapSextetProjection : PlaneOverlap a →* sextetStabilizer a.sextet where
  toFun x := ⟨(overlapToddCoordinates a x).right,
    (a.point_plane_todd_overlap ⟨x.val.val,x.property⟩).mp x.val.property⟩
  map_one' := by apply Subtype.ext; exact congrArg SemidirectProduct.right (map_one _)
  map_mul' x y := by apply Subtype.ext; exact congrArg SemidirectProduct.right (map_mul _ x y)

noncomputable def overlapPartProjection : PlaneOverlap a →* Equiv.Perm (SextetPart a.sextet) :=
  (sextetPartPerm a.sextet).comp (overlapSextetProjection a)

noncomputable def overlapToddComplement (s : sextetStabilizer a.sextet) : PlaneOverlap a :=
  ⟨⟨a.P.toddEquiv (SemidirectProduct.inr s.val),by
      apply (a.point_plane_todd_overlap _).mpr
      change (a.P.toddEquiv.symm (a.P.toddEquiv (SemidirectProduct.inr s.val))).right ∈ sextetStabilizer a.sextet
      rw [a.P.toddEquiv.symm_apply_apply]
      exact s.property⟩,(a.P.toddEquiv (SemidirectProduct.inr s.val)).property⟩

theorem overlapToddCoordinates_complement (s : sextetStabilizer a.sextet) :
    overlapToddCoordinates a (overlapToddComplement a s) = SemidirectProduct.inr s.val :=
  a.P.toddEquiv.symm_apply_apply _

theorem overlapSextetProjection_surjective : Function.Surjective (overlapSextetProjection a) := by
  intro s
  refine ⟨overlapToddComplement a s,Subtype.ext ?_⟩
  exact congrArg SemidirectProduct.right (overlapToddCoordinates_complement a s)

theorem overlapPartProjection_surjective : Function.Surjective (overlapPartProjection a) :=
  (SextetLayers.CoordinateTransport.nativePartPerm_surjective a.sextet).comp
    (overlapSextetProjection_surjective a)

theorem overlapPartProjection_cubicLift :
    (twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a) ≤
      (overlapPartProjection a).ker := by
  classical
  let K := (twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a)
  let R := K.map (overlapPartProjection a)
  let : R.Normal := Subgroup.Normal.map inferInstance _ (overlapPartProjection_surjective a)
  have hK : Nat.card K = 3*2^13 :=
    (Nat.card_congr (subgroupOfEquivOfLe (overlap_cubicLift_le a)).toEquiv).trans
      (twoThreeCore_card h)
  let : Nontrivial (SextetPart a.sextet) := Fintype.one_lt_card_iff_nontrivial.mp
    (by rw [card_sextetPart]; decide)
  have hr : R = ⊥ := by
    by_contra hn
    have hl := Equiv.Perm.alternatingGroup_le_of_normal
      (by rw [Nat.card_eq_fintype_card,card_sextetPart]; decide :
        5 ≤ Nat.card (SextetPart a.sextet)) ((nontrivial_iff_ne_bot R).mpr hn)
    have ha : Nat.card (alternatingGroup (SextetPart a.sextet)) = 360 := by
      rw [nat_card_alternatingGroup,Nat.card_eq_fintype_card,card_sextetPart]
      decide
    have hd := (card_dvd_of_le hl).trans
      (K.card_map_dvd (overlapPartProjection a))
    rw [ha,hK] at hd
    norm_num at hd
  exact (Subgroup.map_eq_bot_iff _).mp hr

abbrev OverlapAffine := Multiplicative (BinaryPermutation.natural (SextetPart a.sextet))
  ⋊[BinaryPermutation.naturalMulAction (SextetPart a.sextet)] Equiv.Perm (SextetPart a.sextet)

noncomputable def overlapAffineProjection : PlaneOverlap a →* OverlapAffine a where
  toFun x := ⟨Multiplicative.ofAdd
    (sextetCocodeParity a.sextet (overlapToddCoordinates a x).left.toAdd),
    overlapPartProjection a x⟩
  map_one' := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (sextetCocodeParity a.sextet
        (overlapToddCoordinates a 1).left.toAdd) = 1
      rw [map_one]
      exact congrArg Multiplicative.ofAdd (map_zero _)
    · exact map_one _
  map_mul' x y := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (sextetCocodeParity a.sextet
        (overlapToddCoordinates a (x*y)).left.toAdd) = _
      rw [map_mul]
      change Multiplicative.ofAdd (sextetCocodeParity a.sextet
        ((overlapToddCoordinates a x).left.toAdd +
          cocodeRepresentation (overlapSextetProjection a x).val
            (overlapToddCoordinates a y).left.toAdd)) = _
      rw [map_add,sextetCocodeParity_equivariant]
      rfl
    · exact map_mul _ x y

theorem overlapAffineProjection_right (x : PlaneOverlap a) :
    (overlapAffineProjection a x).right = overlapPartProjection a x := rfl

theorem overlapAffineProjection_cubic :
    (cubicSylowImage a.e a.X).subgroupOf (PlaneOverlap a) ≤ (overlapAffineProjection a).ker := by
  intro x hx
  have hA : cubicSylowImage a.e a.X ≤ twoThreeCore (centralizer z) := by
    rw [←cubicLift_eq_twoThreeCore h a.e,←core_sup_cubicSylow a.e h a.X]
    exact le_sup_right
  have hr : (overlapAffineProjection a x).right = 1 := overlapPartProjection_cubicLift a (hA hx)
  have h3 : x^3=1 := by
    have he : (⟨x.val,hx⟩ : cubicSylowImage a.e a.X)^Nat.card (cubicSylowImage a.e a.X)=1 := pow_card_eq_one'
    rw [cubicSylowImage_card h a.e a.X] at he
    apply Subtype.ext
    exact congrArg (fun t : cubicSylowImage a.e a.X => t.val) he
  have h2 : (overlapAffineProjection a x)^2=1 := by
    have he : overlapAffineProjection a x =
        SemidirectProduct.inl (overlapAffineProjection a x).left := by
      apply SemidirectProduct.ext <;> simp [hr]
    rw [he,←map_pow]
    have hh : (overlapAffineProjection a x).left^2=1 := by
      rw [pow_two]
      change Multiplicative.ofAdd ((overlapAffineProjection a x).left.toAdd +
        (overlapAffineProjection a x).left.toAdd) = 1
      have hn (v : BinaryPermutation.natural (SextetPart a.sextet)) : -v=v := by
        rw [←neg_one_smul (ZMod 2) v,show (-1 : ZMod 2)=1 from rfl,one_smul]
      nth_rw 1 [←hn (overlapAffineProjection a x).left.toAdd]
      rw [neg_add_cancel]
      rfl
    rw [hh,map_one]
  have h3' : (overlapAffineProjection a x)^3=1 := by rw [←map_pow,h3,map_one]
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
    (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3'))

theorem overlapAffineProjection_core :
    (core z).subgroupOf (PlaneOverlap a) ≤ (overlapAffineProjection a).ker := by
  rw [←overlap_core_eq_commutator a]
  apply (commutator_mono le_top (overlapAffineProjection_cubic a)).trans
  exact commutator_le_right _ _

theorem overlapAffineProjection_cubicLift :
    (twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a) ≤ (overlapAffineProjection a).ker := by
  have hA : cubicSylowImage a.e a.X ≤ PlaneOverlap a := by
    apply le_trans ?_ (overlap_cubicLift_le a)
    rw [←cubicLift_eq_twoThreeCore h a.e,←core_sup_cubicSylow a.e h a.X]
    exact le_sup_right
  have he : (twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a) =
      (core z).subgroupOf (PlaneOverlap a) ⊔ (cubicSylowImage a.e a.X).subgroupOf (PlaneOverlap a) := by
    apply Subgroup.map_injective (PlaneOverlap a).subtype_injective
    rw [map_subgroupOf_eq_of_le (overlap_cubicLift_le a),Subgroup.map_sup,
      map_subgroupOf_eq_of_le ((core_le_twoThreeCore h).trans (overlap_cubicLift_le a)),
      map_subgroupOf_eq_of_le hA,core_sup_cubicSylow a.e h a.X,cubicLift_eq_twoThreeCore h a.e]
  rw [he]
  exact sup_le (overlapAffineProjection_core a) (overlapAffineProjection_cubic a)

noncomputable def overlapToddVector (v : Cocode) : PlaneOverlap a :=
  ⟨⟨a.P.vectorEmbedding (Multiplicative.ofAdd v), by
      apply (a.point_plane_todd_overlap _).mpr
      change (a.P.toddEquiv.symm (a.P.toddEquiv
        (SemidirectProduct.inl (Multiplicative.ofAdd v)))).right • _ = _
      rw [a.P.toddEquiv.symm_apply_apply]
      exact one_smul _ _⟩,(a.P.toddEquiv (SemidirectProduct.inl (Multiplicative.ofAdd v))).property⟩

theorem overlapToddCoordinates_vector (v : Cocode) :
    overlapToddCoordinates a (overlapToddVector a v) =
      SemidirectProduct.inl (Multiplicative.ofAdd v) := a.P.toddEquiv.symm_apply_apply _

theorem overlapAffineProjection_vector (v : Cocode) :
    overlapAffineProjection a (overlapToddVector a v) =
      SemidirectProduct.inl (Multiplicative.ofAdd (sextetCocodeParity a.sextet v)) := by
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd (sextetCocodeParity a.sextet
      (overlapToddCoordinates a (overlapToddVector a v)).left.toAdd) = _
    rw [overlapToddCoordinates_vector]
    rfl
  · change sextetPartPerm a.sextet (overlapSextetProjection a (overlapToddVector a v)) = 1
    have he : overlapSextetProjection a (overlapToddVector a v) = 1 :=
      Subtype.ext (congrArg SemidirectProduct.right (overlapToddCoordinates_vector a v))
    rw [he,map_one]

theorem overlapToddCoordinates_twist (w : Full) (y : PlaneOverlap a) :
    overlapToddCoordinates a (planeOverlapToddTwist a w y) =
      toddTwist w (overlapToddCoordinates a y) := pointTwist_coordinates a w _

theorem planeOverlapToddTwist_vector (w : Full) (v : Cocode) :
    planeOverlapToddTwist a w (overlapToddVector a v) = overlapToddVector a v := by
  apply (overlapPlacement a).symm.injective
  apply Subtype.ext
  apply a.P.toddEquiv.symm.injective
  change overlapToddCoordinates a (planeOverlapToddTwist a w (overlapToddVector a v)) =
    overlapToddCoordinates a (overlapToddVector a v)
  rw [overlapToddCoordinates_twist,overlapToddCoordinates_vector,toddTwist_vector]

noncomputable def cubicAffineProjection : OverlapCohomology.Original a.P →* OverlapAffine a :=
  QuotientGroup.lift _ (overlapAffineProjection a) (overlapAffineProjection_cubicLift a)

theorem cubicAffineProjection_mk (x : PlaneOverlap a) :
    cubicAffineProjection a (QuotientGroup.mk' _ x) = overlapAffineProjection a x := rfl

theorem overlapAffineProjection_complement (s : sextetStabilizer a.sextet) :
    overlapAffineProjection a (overlapToddComplement a s) =
      SemidirectProduct.inr (sextetPartPerm a.sextet s) := by
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd (sextetCocodeParity a.sextet
      (overlapToddCoordinates a (overlapToddComplement a s)).left.toAdd) = 1
    rw [overlapToddCoordinates_complement]
    exact congrArg Multiplicative.ofAdd (map_zero _)
  · change sextetPartPerm a.sextet (overlapSextetProjection a (overlapToddComplement a s)) = _
    congr 1
    exact Subtype.ext (congrArg SemidirectProduct.right (overlapToddCoordinates_complement a s))

theorem overlapAffineProjection_surjective : Function.Surjective (overlapAffineProjection a) := by
  intro x
  obtain ⟨v,hv⟩ := sextetCocodeParity_surjective a.sextet x.left.toAdd
  obtain ⟨s,hs⟩ := SextetLayers.CoordinateTransport.nativePartPerm_surjective a.sextet x.right
  refine ⟨overlapToddVector a v * overlapToddComplement a s,?_⟩
  rw [map_mul,overlapAffineProjection_vector,overlapAffineProjection_complement,hv,hs]
  change SemidirectProduct.inl x.left * SemidirectProduct.inr x.right = x
  exact SemidirectProduct.inl_left_mul_inr_right x

theorem cubicAffineProjection_surjective : Function.Surjective (cubicAffineProjection a) := by
  intro x
  obtain ⟨y,rfl⟩ := overlapAffineProjection_surjective a x
  exact ⟨QuotientGroup.mk' _ y,rfl⟩

private theorem overlap_affine_card : Nat.card (OverlapAffine a) = 11520 := by
  let : Nonempty (SextetPart a.sextet) := Fintype.card_pos_iff.mp (by rw [card_sextetPart]; decide)
  have hv : Nat.card (Multiplicative (BinaryPermutation.natural (SextetPart a.sextet))) = 16 := by
    change Nat.card (BinaryPermutation.natural (SextetPart a.sextet)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      BinaryPermutation.finrank_natural_even _ (by rw [card_sextetPart]; decide),card_sextetPart]
    decide
  rw [Nat.card_congr SemidirectProduct.equivProd,Nat.card_prod,hv,Nat.card_perm,
    Nat.card_eq_fintype_card,card_sextetPart]
  decide

private theorem overlap_original_card : Nat.card (OverlapCohomology.Original a.P) = 11520 := by
  have hc : Nat.card (pCore 2 (OverlapCohomology.Original a.P)) = 16 := by
    rw [Nat.card_congr (OverlapCohomology.originalCoordinates h a.P).toEquiv]
    change Nat.card (OverlapCohomology.V) = 16
    simp [OverlapCohomology.V,Nat.card_eq_fintype_card]
  have hi : (pCore 2 (OverlapCohomology.Original a.P)).index = 720 := by
    change Nat.card (OverlapCohomology.Original a.P ⧸ pCore 2 _) = _
    rw [Nat.card_congr (OverlapCohomology.originalQuotient h a.P).toEquiv]
    rw [←Nat.card_congr HexadSymplecticComparison.PolarModel.sixToSymplectic.toEquiv,
      Nat.card_perm,Nat.card_fin]
    decide
  rw [←(pCore 2 (OverlapCohomology.Original a.P)).card_mul_index,hc,hi]

theorem cubicAffineProjection_bijective : Function.Bijective (cubicAffineProjection a) :=
  (cubicAffineProjection_surjective a).bijective_of_nat_card_le
    (by rw [overlap_original_card,overlap_affine_card])

/-- The parity affine map has exactly the original scalar-and-core kernel. -/
theorem overlapAffineProjection_ker : (overlapAffineProjection a).ker =
    (twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a) := by
  ext x
  change overlapAffineProjection a x = 1 ↔ _
  rw [←cubicAffineProjection_mk,←map_one (cubicAffineProjection a),
    (cubicAffineProjection_bijective a).1.eq_iff]
  exact QuotientGroup.eq_one_iff x

noncomputable def cubicAffineEquiv : OverlapCohomology.Original a.P ≃* OverlapAffine a :=
  MulEquiv.ofBijective (cubicAffineProjection a) (cubicAffineProjection_bijective a)

theorem cubicAffineEquiv_mk (x : PlaneOverlap a) :
    cubicAffineEquiv a (QuotientGroup.mk' _ x) = overlapAffineProjection a x := rfl
end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
