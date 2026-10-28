module

public import Theory.AlgebraicGroup.Borel.SelfNormalizer
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.TorusRigidity.Transitivity
public import Theory.AlgebraicGroup.Tori.CentralMaximalNilpotent.TorusFree
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry
public import Theory.AlgebraicGroup.Tori.Character.ConnectedKernel

/-!
# The positive fixed-torus cases of Borel self-normalization

Let an element normalize a Borel and a maximal torus inside it. The connected
component of its infinite fixed subgroup in that torus has positive dimension.
If it is central, its actual affine quotient has smaller dimension and the
image Borel lifts through a kernel contained in the original Borel. Otherwise,
its centralizer is proper and connected, and the restricted Borel is Borel.
In both cases self-normalization in strictly smaller dimension places the
original element in the original Borel.

This proves cases (i) and (ii) of Borel, *Linear Algebraic Groups*, IV, Theorem
11.16, `refs/KGroup/Bor1/Chapter4.tex`. The only induction premise is the genuine
strict-dimension predecessor statement; no self-normalization in the current
group or extra quotient or centralizer geometry is assumed.
-/

namespace Theory.AlgebraicGroup.BorelSelfNormalizer
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

omit [IsAlgClosed k] in
private theorem carrier_connected (S : ClosedSubgroup G)
    (hS : _root_.IsConnected (S : Set (Variety.Point G))) :
    Variety.IsConnected S.carrierVariety := by
  let : ConnectedSpace {x : Variety.Point G // x ∈ (S : Set (Variety.Point G))} :=
    Subtype.connectedSpace hS
  let : ConnectedSpace (Variety.Point S.carrierVariety) :=
    (Variety.closedSubvarietyPointHomeomorph S.isZariskiClosed).connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

omit [AlgebraicGroup G] in
private theorem smaller_normalizer_eq (ih : SmallerDimension G)
    {H : Variety k} [AlgebraicGroup H] (hdim : Variety.dimension H < Variety.dimension G)
    (hH : Variety.IsConnected H) (B : ClosedSubgroup H) (hB : IsBorelSubgroup B) :
    B.normalizer = B := by
  obtain ⟨T, hT, hTB⟩ := BorelIntersectionGeometry.exists_maximalTorus_le_borel_of_conjugacy
    (fun _ _ hA hB => BorelGeometricConjugacy.conjugacy hA hB) B hB
  exact ih H hdim hH B T hB hT hTB

/-- The central positive-dimensional induction kernel from Borel 11.16(i). -/
public theorem mem_borel_of_positive_central_subgroup
    (hG : Variety.IsConnected G) (ih : SmallerDimension G)
    (B S : ClosedSubgroup G) (hB : IsBorelSubgroup B) (hSB : S ≤ B)
    (hcentral : S.toSubgroup ≤ Subgroup.center (Variety.Point G))
    (hpos : 0 < Variety.dimension S.carrierVariety)
    (n : Variety.Point G) (hn : n ∈ B.normalizer.toSubgroup) : n ∈ B.toSubgroup := by
  have hnormal : S.toSubgroup.Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_center_iff.mp (hcentral hx) g, mul_inv_cancel_right]
    exact hx
  obtain ⟨d, F, hFker⟩ := S.generalLinearMorphism_exactKernel_exists hnormal
  let : AlgebraicGroup F.imageClosedSubgroup.carrierVariety :=
    F.imageClosedSubgroup.carrierAlgebraicGroup
  obtain ⟨q, hq, hqker, _⟩ := F.closedImageProjection_exists
  have hker : q.kernel = S.toSubgroup := hqker.trans hFker
  have hclosedker : q.kernelClosedSubgroup = S := by
    apply SetLike.coe_injective
    exact congrArg (fun L : Subgroup (Variety.Point G) => (L : Set (Variety.Point G))) hker
  have hkerS : Group.IsSolvable q.kernel := by
    apply Group.isSolvable_of_comm
    intro x y
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hcentral (hker ▸ x.property)) y.val).symm
  let D := (q.comp B.inclusion).imageClosedSubgroup
  have hD : IsBorelSubgroup D := TorusFree.borel_image_of_solvable_kernel q hq hkerS B hB
  have hdim : Variety.dimension F.imageClosedSubgroup.carrierVariety < Variety.dimension G := by
    apply TorusFree.quotient_dimension_lt_of_positive_kernel q hq
    rwa [hclosedker]
  have hDn := smaller_normalizer_eq ih hdim (connected_of_surjective_morphism q hG hq) D hD
  have hmap : D.toSubgroup = B.toSubgroup.map q.onPoints := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨B.inclusion.onPoints b, (B.pointEquiv b).property, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨B.pointEquiv.symm ⟨b, hb⟩, rfl⟩
  have hqn : q.onPoints n ∈ D.normalizer.toSubgroup := by
    change q.onPoints n ∈ Subgroup.normalizer (D.toSubgroup : Set (Variety.Point F.imageClosedSubgroup.carrierVariety))
    rw [hmap]
    exact Subgroup.le_normalizer_map q.onPoints ⟨n, hn, rfl⟩
  rw [hDn] at hqn
  obtain ⟨b, hb⟩ := hqn
  have hdiff : n * (B.inclusion.onPoints b)⁻¹ ∈ S.toSubgroup := by
    rw [← hker]
    change q.onPoints (n * (B.inclusion.onPoints b)⁻¹) = 1
    rw [map_mul, map_inv, ← hb]
    exact mul_inv_cancel _
  have := B.toSubgroup.mul_mem (hSB hdiff) (B.pointEquiv b).property
  change n * (B.inclusion.onPoints b)⁻¹ * B.inclusion.onPoints b ∈ B.toSubgroup at this
  simpa only [inv_mul_cancel_right] using this

/-- The noncentral subtorus reduction from Borel 11.16(ii). -/
public theorem mem_borel_of_noncentral_subtorus
    (hG : Variety.IsConnected G) (ih : SmallerDimension G)
    (B S : ClosedSubgroup G) (hB : IsBorelSubgroup B) (hS : IsSubtorus S) (hSB : S ≤ B)
    (hcentral : ¬ S.toSubgroup ≤ Subgroup.center (Variety.Point G))
    (n : Variety.Point G) (hn : n ∈ B.normalizer.toSubgroup)
    (hnS : n ∈ S.centralizer.toSubgroup) : n ∈ B.toSubgroup := by
  let C := S.centralizer
  have hCc : Variety.IsConnected C.carrierVariety :=
    SemisimpleCenterContainment.CartanGeometry.subtorus_centralizer_isConnected hG hS
  have hCne : C ≠ ClosedSubgroup.top := by
    intro heq
    apply hcentral
    intro s hs
    rw [Subgroup.mem_center_iff]
    intro x
    have hx : x ∈ S.centralizer.toSubgroup := by rw [← show C = S.centralizer from rfl, heq]; trivial
    exact (Subgroup.mem_centralizer_iff.mp hx s hs).symm
  have hCset : _root_.IsConnected (C : Set (Variety.Point G)) := by
    change _root_.IsConnected (C.toSubgroup : Set (Variety.Point G))
    rw [← C.range_inclusion]
    let : ConnectedSpace (Variety.Point C.carrierVariety) := connectedSpace_iff_univ.mpr hCc
    exact isConnected_range C.inclusion.toVariety.continuous
  have hdim : Variety.dimension C.carrierVariety < Variety.dimension G := by
    have hlt := connected_closedSubgroup_dimension_lt_of_le_of_ne C ClosedSubgroup.top
      (fun _ _ => trivial) hCne hCset hG
    have htop : Variety.dimension (ClosedSubgroup.top (G := G)).carrierVariety =
        Variety.dimension G := (closedSubgroup_dimension_eq_iff_contains_identityComponent G _).mpr
          (fun _ _ => trivial)
    exact hlt.trans_eq htop
  let D := C.inclusion.closedSubgroupPreimage B
  have hD : IsBorelSubgroup D :=
    SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.isBorel_centralizer_restriction
      hG S B hS hB hSB
  let c := C.pointEquiv.symm ⟨n, hnS⟩
  have hcn : C.inclusion.onPoints c = n := rfl
  have hc : c ∈ D.normalizer.toSubgroup := by
    exact Subgroup.le_normalizer_comap C.inclusion.onPoints (show C.inclusion.onPoints c ∈
      Subgroup.normalizer (B.toSubgroup : Set (Variety.Point G)) from hcn ▸ hn)
  rw [smaller_normalizer_eq ih hdim hCc D hD] at hc
  exact hc

private def fixedClosedSubgroup (T : ClosedSubgroup G) (n : Variety.Point G) : ClosedSubgroup G :=
  ClosedSubgroup.ofSubgroup (T.toSubgroup ⊓ Subgroup.centralizer {n}) (by
    have hclosed := Variety.Morphism.isZariskiClosed_equalizer
      (AlgebraicGroup.leftMulMorphism G n) (AlgebraicGroup.rightMulMorphism G n)
    have hset : (Subgroup.centralizer {n} : Set (Variety.Point G)) =
        {x | (AlgebraicGroup.leftMulMorphism G n).toFun x =
          (AlgebraicGroup.rightMulMorphism G n).toFun x} := by
      ext x
      change x ∈ Subgroup.centralizer {n} ↔ _
      simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
        Set.mem_ofPred_eq, AlgebraicGroup.leftMulMorphism_apply, AlgebraicGroup.rightMulMorphism_apply]
    exact isZariskiClosed_inter T.isZariskiClosed (hset ▸ hclosed))

omit [IsAlgClosed k] in
private theorem mem_fixedClosedSubgroup (T : ClosedSubgroup G) (n x : Variety.Point G) :
    x ∈ fixedClosedSubgroup T n ↔ x ∈ T.toSubgroup ∧ n * x = x * n := by
  change (x ∈ T.toSubgroup ∧ x ∈ Subgroup.centralizer {n}) ↔ _
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]

/-- The identity component of the actual fixed torus supplies the two positive
induction branches, including nonsemisimple normalizer elements. -/
public theorem mem_borel_of_infinite_fixedPoints
    (hG : Variety.IsConnected G) (ih : SmallerDimension G)
    (B T : ClosedSubgroup G) (hB : IsBorelSubgroup B) (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (n : Variety.Point G) (hnB : n ∈ B.normalizer.toSubgroup)
    (_hnT : n ∈ T.normalizer.toSubgroup) (hfixed : ¬(fixedTorusPoints T n).Finite) :
    n ∈ B.toSubgroup := by
  let F := fixedClosedSubgroup T n
  let S := F.identityComponentAmbient
  have hST : S ≤ T := fun x hx =>
    ((mem_fixedClosedSubgroup T n x).mp (F.identityComponentAmbient_le hx)).1
  have hSn : n ∈ S.centralizer.toSubgroup := by
    change n ∈ Subgroup.centralizer (S.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact ((mem_fixedClosedSubgroup T n s).mp (F.identityComponentAmbient_le hs)).2.symm
  have hSpos : 0 < Variety.dimension S.carrierVariety := by
    rw [show S = F.identityComponentAmbient from rfl, F.dimension_identityComponentAmbient]
    apply bot_lt_iff_ne_bot.mpr
    intro hzero
    have hfinite : Finite (Variety.Point F.carrierVariety) :=
      (dimension_zero_iff_finite_points _).mp hzero
    let := hfinite
    have hFfinite : (F : Set (Variety.Point G)).Finite := by
      change (F.toSubgroup : Set (Variety.Point G)).Finite
      rw [← F.range_inclusion]
      exact Set.finite_range F.inclusion.onPoints
    apply hfixed
    convert hFfinite using 1
    ext x
    exact (mem_fixedClosedSubgroup T n x).symm
  by_cases hcentral : S.toSubgroup ≤ Subgroup.center (Variety.Point G)
  · exact mem_borel_of_positive_central_subgroup hG ih B S hB (fun _ hx => hTB (hST hx))
      hcentral hSpos n hnB
  · have hS : IsSubtorus S := by
      let i := S.inclusion.codRestrictClosedSubgroup T (fun s => hST (S.pointEquiv s).property)
      have hsemi (s : Variety.Point S.carrierVariety) : IsSemisimpleElement S.carrierVariety s := by
        have ht := hT.1.all_semisimple (i.onPoints s)
        have hs := morphism_preserves_semisimpleElement T.inclusion (i.onPoints s) ht
        rw [Morphism.codRestrictClosedSubgroup_inclusion_apply] at hs
        exact (closedSubgroup_semisimpleElement_iff S (S.pointEquiv s).property).mp hs
      have hcomm : IsMulCommutative (Variety.Point S.carrierVariety) := by
        rw [isMulCommutative_iff]
        intro x y
        apply S.inclusion_injective
        have hxy := congrArg T.inclusion.onPoints (isMulCommutative_iff.mp hT.1.isMulCommutative
          (i.onPoints x) (i.onPoints y))
        simpa only [map_mul, i, Morphism.codRestrictClosedSubgroup_inclusion_apply] using hxy
      exact isTorus_of_isConnected_isMulCommutative_all_semisimple
        (carrier_connected S F.identityComponentAmbient_isConnected) hcomm hsemi
    exact mem_borel_of_noncentral_subtorus hG ih B S hB hS (fun _ hx => hTB (hST hx))
      hcentral n hnB hSn

end Theory.AlgebraicGroup.BorelSelfNormalizer
