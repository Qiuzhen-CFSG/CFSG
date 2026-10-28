module

public import Theory.AlgebraicGroup.Instance.U
public import Theory.AlgebraicGroup.Jordan.ClosedSubgroup
public import Theory.AlgebraicGroup.Jordan.Intersection
public import Theory.AlgebraicGroup.Morphism.Power
public import Theory.AlgebraicGroup.Representations.Solvable
public import Theory.AlgebraicGroup.Representations.Triangular
public import Theory.AlgebraicGroup.RightTranslation.Representation
public import Theory.AlgebraicGroup.Tori.Character.Basis

universe u

set_option linter.style.haveILetI false

/-! Presentations of algebraic groups as closed upper-triangular subgroups. -/

namespace Theory.AlgebraicGroup

open scoped commutatorElement IsMulCommutative

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Data presenting an algebraic group as a closed subgroup of a
positive-dimensional upper-triangular group. -/
public structure TriangularPresentation
    (G : Variety k) [AlgebraicGroup G] where
  n : ℕ
  positive : 0 < n
  subgroup : ClosedSubgroup (tVariety k n)
  iso : @AlgebraicGroup.Iso k _ G subgroup.carrierVariety _
    (ClosedSubgroup.carrierAlgebraicGroup subgroup)

/-- The point map from a triangularly presented group into its ambient
upper-triangular group. -/
@[expose]
public noncomputable def TriangularPresentation.toTriangularPoint
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G)
    (x : Variety.Point G) : Variety.Point (tVariety k P.n) := by
  letI : AlgebraicGroup P.subgroup.carrierVariety :=
    P.subgroup.carrierAlgebraicGroup
  exact P.subgroup.inclusion.onPoints (P.iso.hom.onPoints x)

/-- The diagonal morphism attached to a triangular presentation. -/
@[expose]
public noncomputable def TriangularPresentation.diagonalMorphism
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G) :
    AlgebraicGroup.Morphism G (dVariety k P.n) := by
  letI : AlgebraicGroup P.subgroup.carrierVariety :=
    P.subgroup.carrierAlgebraicGroup
  exact (tDiagonalMorphism P.n).comp
    (P.subgroup.inclusion.comp P.iso.hom)

/-- The closed diagonal image attached to a triangular presentation. -/
@[expose]
public noncomputable def TriangularPresentation.diagonalImage
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G) :
    ClosedSubgroup (dVariety k P.n) :=
  P.diagonalMorphism.imageClosedSubgroup

/-- The diagonal morphism with codomain restricted to its closed image. -/
@[expose]
public noncomputable def TriangularPresentation.diagonalImageMorphism
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G) :
    @AlgebraicGroup.Morphism k _ G P.diagonalImage.carrierVariety
      (inferInstance : AlgebraicGroup G)
      P.diagonalImage.carrierAlgebraicGroup := by
  letI : AlgebraicGroup P.diagonalImage.carrierVariety :=
    P.diagonalImage.carrierAlgebraicGroup
  exact P.diagonalMorphism.codRestrictClosedSubgroup P.diagonalImage fun x => by
    change P.diagonalMorphism.onPoints x ∈ P.diagonalMorphism.image
    exact ⟨x, rfl⟩

/-- In a triangular presentation, the candidate unipotent radical is the
closed kernel of the induced diagonal morphism. -/
@[expose]
public noncomputable def TriangularPresentation.unipotentRadical
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G) :
    ClosedSubgroup G :=
  P.diagonalMorphism.kernelClosedSubgroup

/-- The inclusion of the identity component of the unipotent radical into
the ambient group. -/
@[expose]
public noncomputable def TriangularPresentation.kernelIdentityComponentMorphism
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G) :
    let K := P.unipotentRadical
    let K0 := @identityComponentClosedSubgroup k _
      K.carrierVariety K.carrierAlgebraicGroup
    @AlgebraicGroup.Morphism k _ K0.carrierVariety G
      K0.carrierAlgebraicGroup (inferInstance) := by
  let K := P.unipotentRadical
  letI : AlgebraicGroup K.carrierVariety := K.carrierAlgebraicGroup
  let K0 := identityComponentClosedSubgroup K.carrierVariety
  letI : AlgebraicGroup K0.carrierVariety := K0.carrierAlgebraicGroup
  exact K.inclusion.comp K0.inclusion

/-- The identity component of the unipotent radical, regarded as a closed
subgroup of the ambient group. -/
@[expose]
public noncomputable def TriangularPresentation.kernelIdentityComponent
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G) :
    ClosedSubgroup G := by
  let K := P.unipotentRadical
  letI : AlgebraicGroup K.carrierVariety := K.carrierAlgebraicGroup
  let K0 := identityComponentClosedSubgroup K.carrierVariety
  letI : AlgebraicGroup K0.carrierVariety := K0.carrierAlgebraicGroup
  exact P.kernelIdentityComponentMorphism.imageClosedSubgroup

/-- The embedded identity component of the unipotent radical lies in that
radical. -/
public lemma TriangularPresentation.kernelIdentityComponent_le_unipotentRadical
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G) :
    P.kernelIdentityComponent ≤ P.unipotentRadical := by
  let K := P.unipotentRadical
  letI : AlgebraicGroup K.carrierVariety := K.carrierAlgebraicGroup
  let K0 := identityComponentClosedSubgroup K.carrierVariety
  letI : AlgebraicGroup K0.carrierVariety := K0.carrierAlgebraicGroup
  intro x hx
  change x ∈ P.kernelIdentityComponentMorphism.image at hx
  rcases hx with ⟨z, rfl⟩
  change P.unipotentRadical.inclusion.onPoints _ ∈ P.unipotentRadical
  exact (P.unipotentRadical.pointEquiv _).property

/-- Membership in the triangular-presentation unipotent radical is exactly
the equation that the ambient triangular point has diagonal image one. -/
public lemma TriangularPresentation.mem_unipotentRadical_iff_diagonal
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G)
    (x : Variety.Point G) :
    x ∈ P.unipotentRadical ↔
      (tDiagonalMorphism P.n).onPoints (P.toTriangularPoint x) = 1 := by
  letI : AlgebraicGroup P.subgroup.carrierVariety :=
    P.subgroup.carrierAlgebraicGroup
  simp only [TriangularPresentation.unipotentRadical,
    TriangularPresentation.diagonalMorphism,
    TriangularPresentation.toTriangularPoint]
  rfl

/-- The unipotent radical attached to a triangular presentation is a normal
subgroup. -/
public lemma TriangularPresentation.unipotentRadical_normal
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G) :
    P.unipotentRadical.toSubgroup.Normal :=
  P.diagonalMorphism.kernelClosedSubgroup_isNormal

/-- Every commutator lies in the embedded identity component of the
unipotent radical. -/
public theorem TriangularPresentation.commutator_le_kernelIdentityComponent
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G)
    (hG : Variety.IsConnected G) :
    commutator (Variety.Point G) ≤ P.kernelIdentityComponent.toSubgroup := by
  let K := P.unipotentRadical
  letI : AlgebraicGroup K.carrierVariety := K.carrierAlgebraicGroup
  let K0 := identityComponentClosedSubgroup K.carrierVariety
  letI : AlgebraicGroup K0.carrierVariety := K0.carrierAlgebraicGroup
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro _ ⟨x, y, rfl⟩
  let cG : Variety.Morphism G G :=
    (AlgebraicGroup.rightMulMorphism G y⁻¹).comp
      (AlgebraicGroup.conjugateMorphism G y)
  have hcG (z : Variety.Point G) : cG.toFun z = ⁅z, y⁆ := by
    simp [cG, Variety.Morphism.comp,
      AlgebraicGroup.rightMulMorphism_apply,
      AlgebraicGroup.conjugateMorphism_apply,
      commutatorElement_def, mul_assoc]
  have hcK (z : Variety.Point G) : cG.toFun z ∈ P.unipotentRadical := by
    change P.diagonalMorphism.onPoints (cG.toFun z) = 1
    rw [hcG, map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    apply (dPointEquiv P.n).injective
    exact mul_comm _ _
  let cK : Variety.Morphism G P.unipotentRadical.carrierVariety :=
    { toFun := fun z => P.unipotentRadical.pointEquiv.symm
          ⟨cG.toFun z, hcK z⟩
      regular := by
        intro i
        rcases cG.regular i with ⟨q, hq⟩
        exact ⟨q, fun z => by
          change (P.unipotentRadical.pointEquiv
            (P.unipotentRadical.pointEquiv.symm
              ⟨cG.toFun z, hcK z⟩)).val.val i = _
          rw [P.unipotentRadical.pointEquiv.apply_symm_apply]
          exact hq z⟩ }
  let : ConnectedSpace (Variety.Point G) :=
    connectedSpace_iff_univ.mpr hG
  have hcRange : _root_.IsConnected (Set.range cK.toFun) :=
    isConnected_range cK.continuous
  have hcOne : (1 : Variety.Point P.unipotentRadical.carrierVariety) ∈
      Set.range cK.toFun := by
    refine ⟨1, ?_⟩
    apply P.unipotentRadical.inclusion_injective
    change cG.toFun 1 = P.unipotentRadical.inclusion.onPoints 1
    rw [hcG]
    simp
  have hcx0 : cK.toFun x ∈
      AlgebraicGroup.identityComponent P.unipotentRadical.carrierVariety :=
    (hcRange.subset_connectedComponent hcOne) ⟨x, rfl⟩
  let z0 : Variety.Point K0.carrierVariety :=
    K0.pointEquiv.symm ⟨cK.toFun x, hcx0⟩
  change ⁅x, y⁆ ∈ P.kernelIdentityComponentMorphism.image
  refine ⟨z0, ?_⟩
  change P.unipotentRadical.inclusion.onPoints
      (K0.inclusion.onPoints z0) = ⁅x, y⁆
  have hK0 : K0.inclusion.onPoints z0 = cK.toFun x := by
    change (K0.pointEquiv z0).val = cK.toFun x
    simp [z0]
  rw [hK0]
  change cG.toFun x = ⁅x, y⁆
  exact hcG x

/-- Every element of the triangular unipotent radical has order dividing
`p ^ n` in characteristic `p`. -/
public theorem TriangularPresentation.unipotentRadical_pow_primePower_eq_one
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G)
    (p : ℕ) [CharP k p] [Fact p.Prime]
    (x : Variety.Point G) (hx : x ∈ P.unipotentRadical) :
    x ^ p ^ P.n = 1 := by
  letI : AlgebraicGroup P.subgroup.carrierVariety :=
    P.subgroup.carrierAlgebraicGroup
  let UT := tUnipotentKernel (k := k) P.n
  letI : AlgebraicGroup UT.carrierVariety := UT.carrierAlgebraicGroup
  have htri : P.toTriangularPoint x ∈ UT := by
    change (tDiagonalMorphism P.n).onPoints (P.toTriangularPoint x) = 1
    exact (P.mem_unipotentRadical_iff_diagonal x).mp hx
  let y : Variety.Point UT.carrierVariety :=
    UT.pointEquiv.symm ⟨P.toTriangularPoint x, htri⟩
  let e := uVarietyIsoTUnipotentKernel (k := k) P.n
  let z : Variety.Point (uVariety k P.n) := e.inv.onPoints y
  have hz : z ^ p ^ P.n = 1 :=
    uPoint_pow_primePower_eq_one p P.n z
  have hy : y ^ p ^ P.n = 1 := by
    calc
      y ^ p ^ P.n = (e.hom.onPoints z) ^ p ^ P.n := by
        exact congrArg (fun w => w ^ p ^ P.n) (e.inv_hom_id y).symm
      _ = e.hom.onPoints (z ^ p ^ P.n) := by
        exact (e.hom.onPoints.map_pow z (p ^ P.n)).symm
      _ = 1 := by rw [hz]; exact e.hom.onPoints.map_one
  have htriPow : (P.toTriangularPoint x) ^ p ^ P.n = 1 := by
    have h := congrArg UT.inclusion.onPoints hy
    rw [UT.inclusion.onPoints.map_pow, UT.inclusion.onPoints.map_one] at h
    have hyinc : UT.inclusion.onPoints y = P.toTriangularPoint x := by
      change (UT.pointEquiv y).val = P.toTriangularPoint x
      simp [y]
    rwa [hyinc] at h
  have htri_map_pow : P.toTriangularPoint (x ^ p ^ P.n) =
      (P.toTriangularPoint x) ^ p ^ P.n := by
    simp only [TriangularPresentation.toTriangularPoint, map_pow]
  have htri_one : P.toTriangularPoint (1 : Variety.Point G) = 1 := by
    change P.subgroup.inclusion.onPoints (P.iso.hom.onPoints 1) = 1
    rw [P.iso.hom.onPoints.map_one, P.subgroup.inclusion.onPoints.map_one]
  have hfinal : P.toTriangularPoint (x ^ p ^ P.n) =
      P.toTriangularPoint (1 : Variety.Point G) := by
    rw [htri_map_pow, htriPow, htri_one]
  have hiso : P.iso.hom.onPoints (x ^ p ^ P.n) =
      P.iso.hom.onPoints 1 := by
    apply P.subgroup.inclusion_injective
    simpa only [TriangularPresentation.toTriangularPoint] using hfinal
  have h := congrArg P.iso.inv.onPoints hiso
  simpa only [P.iso.hom_inv_id] using h

/-- In arbitrary characteristic, a triangular presentation's diagonal kernel
consists exactly of the unipotent elements. -/
public theorem TriangularPresentation.mem_unipotentRadical_iff_characteristicFree
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G)
    (x : Variety.Point G) :
    x ∈ P.unipotentRadical ↔ IsUnipotentElement G x := by
  letI : AlgebraicGroup P.subgroup.carrierVariety :=
    P.subgroup.carrierAlgebraicGroup
  have hkernelUnipotent : IsUnipotentAlgebraicGroup
      (tUnipotentKernel (k := k) P.n).carrierVariety := by
    intro y
    let e := uVarietyIsoTUnipotentKernel (k := k) P.n
    let z := e.inv.onPoints y
    have hz := uVariety_isUnipotentAlgebraicGroup_characteristicFree
      (k := k) P.n z
    have hy := morphism_preserves_unipotentElement e.hom z hz
    simpa [z, e.inv_hom_id y] using hy
  have htiff (y : Variety.Point (tVariety k P.n)) :
      IsUnipotentElement (tVariety k P.n) y ↔
        y ∈ (tUnipotentKernel (k := k) P.n :
          Set (Variety.Point (tVariety k P.n))) := by
    constructor
    · intro hy
      change (tDiagonalMorphism P.n).onPoints y = 1
      exact semisimple_unipotent_eq_one
        ((tDiagonalMorphism P.n).onPoints y)
        (dVariety_all_semisimple P.n ((tDiagonalMorphism P.n).onPoints y))
        (morphism_preserves_unipotentElement (tDiagonalMorphism P.n) y hy)
    · intro hy
      exact (closedSubgroup_unipotentElement_iff
        (tUnipotentKernel (k := k) P.n) hy).mpr
        (hkernelUnipotent
          ((tUnipotentKernel (k := k) P.n).pointEquiv.symm ⟨y, hy⟩))
  rw [P.mem_unipotentRadical_iff_diagonal]
  let h : Variety.Point P.subgroup.carrierVariety := P.iso.hom.onPoints x
  let y : Variety.Point (tVariety k P.n) := P.subgroup.inclusion.onPoints h
  have hto : P.toTriangularPoint x = y := rfl
  rw [hto]
  have hy_mem : y ∈ (P.subgroup :
      Set (Variety.Point (tVariety k P.n))) := by
    dsimp [y]
    exact (P.subgroup.pointEquiv h).property
  constructor
  · intro hy_kernel
    have hy_unipotent : IsUnipotentElement (tVariety k P.n) y :=
      (htiff y).mpr hy_kernel
    have hh_unipotent : IsUnipotentElement P.subgroup.carrierVariety h := by
      have hsub :=
        (closedSubgroup_unipotentElement_iff P.subgroup hy_mem).mp hy_unipotent
      have hpoint : P.subgroup.pointEquiv.symm ⟨y, hy_mem⟩ = h := by
        apply P.subgroup.pointEquiv.injective
        rw [P.subgroup.pointEquiv.apply_symm_apply]
        apply Subtype.ext
        rfl
      rw [hpoint] at hsub
      exact hsub
    have hback := morphism_preserves_unipotentElement P.iso.inv h hh_unipotent
    simpa [h, P.iso.hom_inv_id x] using hback
  · intro hx
    have hh_unipotent : IsUnipotentElement P.subgroup.carrierVariety h :=
      morphism_preserves_unipotentElement P.iso.hom x hx
    have hy_unipotent : IsUnipotentElement (tVariety k P.n) y :=
      morphism_preserves_unipotentElement P.subgroup.inclusion h hh_unipotent
    exact (htiff y).mp hy_unipotent

/-- The closed diagonal image of a connected triangularly presented algebraic
group is a torus. -/
public lemma TriangularPresentation.diagonalImage_isTorus
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G)
    (hG : Variety.IsConnected G) :
    @IsTorus k _ P.diagonalImage.carrierVariety
      P.diagonalImage.carrierAlgebraicGroup := by
  let I := P.diagonalImage
  let f := P.diagonalMorphism
  letI : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  have hIset : (I : Set (Variety.Point (dVariety k P.n))) =
      Set.range f.onPoints := by
    exact f.imageClosedSubgroup_carrier.trans f.image_carrier
  have hIconnSet : _root_.IsConnected
      (I : Set (Variety.Point (dVariety k P.n))) := by
    rw [hIset]
    let : ConnectedSpace (Variety.Point G) :=
      connectedSpace_iff_univ.mpr hG
    exact isConnected_range f.toVariety.continuous
  have hIconn : Variety.IsConnected I.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph I.isZariskiClosed
    let : ConnectedSpace
        {x : Variety.Point (dVariety k P.n) //
          x ∈ (I : Set (Variety.Point (dVariety k P.n)))} :=
      Subtype.connectedSpace hIconnSet
    let : ConnectedSpace (Variety.Point I.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  have hIcomm : IsMulCommutative (Variety.Point I.carrierVariety) := by
    apply IsMulCommutative.of_comm
    intro x y
    apply I.inclusion_injective
    calc
      I.inclusion.onPoints (x * y) =
          I.inclusion.onPoints x * I.inclusion.onPoints y :=
        I.inclusion.map_mul x y
      _ = I.inclusion.onPoints y * I.inclusion.onPoints x :=
        by
          have hdiag := dVariety_isMulCommutative (k := k) P.n
          rw [isMulCommutative_iff] at hdiag
          exact hdiag _ _
      _ = I.inclusion.onPoints (y * x) :=
        (I.inclusion.map_mul y x).symm
  have hIsemi : ∀ x : Variety.Point I.carrierVariety,
      IsSemisimpleElement I.carrierVariety x := by
    intro x
    have hAmbient : IsSemisimpleElement (dVariety k P.n)
        (I.inclusion.onPoints x) :=
      dVariety_all_semisimple P.n (I.inclusion.onPoints x)
    exact (closedSubgroup_semisimpleElement_iff I (I.pointEquiv x).property).mp hAmbient
  exact isTorus_of_isConnected_isMulCommutative_all_semisimple hIconn hIcomm hIsemi

/-- In positive characteristic, the unipotent radical of a connected
triangularly presented algebraic group is connected. -/
public theorem TriangularPresentation.unipotentRadical_isConnected
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G)
    (p : ℕ) [CharP k p] [Fact p.Prime]
    (hG : Variety.IsConnected G) :
    Variety.IsConnected P.unipotentRadical.carrierVariety := by
  let K := P.unipotentRadical
  letI : AlgebraicGroup K.carrierVariety := K.carrierAlgebraicGroup
  let K0 := AlgebraicGroup.identityComponentClosedSubgroup K.carrierVariety
  letI : AlgebraicGroup K0.carrierVariety := K0.carrierAlgebraicGroup
  letI : AlgebraicGroup P.diagonalImage.carrierVariety :=
    P.diagonalImage.carrierAlgebraicGroup
  let H := P.kernelIdentityComponent
  have hcomm : commutator (Variety.Point G) ≤ H.toSubgroup :=
    P.commutator_le_kernelIdentityComponent hG
  let : H.toSubgroup.Normal := by
    rw [← Subgroup.commutator_top_right_le_iff]
    exact (Subgroup.commutator_mono le_top le_rfl).trans hcomm
  have hQ : IsMulCommutative (Variety.Point G ⧸ H.toSubgroup) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  let : IsMulCommutative (Variety.Point G ⧸ H.toSubgroup) := hQ
  let q := p ^ P.n
  let Msub : Subgroup (Variety.Point G) :=
    (powMonoidHom q :
      (Variety.Point G ⧸ H.toSubgroup) →*
        (Variety.Point G ⧸ H.toSubgroup)).range.comap
      (QuotientGroup.mk' H.toSubgroup)
  let fst : Variety.Morphism (Variety.prod K0.carrierVariety G)
      K0.carrierVariety :=
    Variety.Morphism.fst K0.carrierVariety G
  let snd : Variety.Morphism (Variety.prod K0.carrierVariety G) G :=
    Variety.Morphism.snd K0.carrierVariety G
  let left : Variety.Morphism (Variety.prod K0.carrierVariety G) G :=
    P.kernelIdentityComponentMorphism.toVariety.comp fst
  let right : Variety.Morphism (Variety.prod K0.carrierVariety G) G :=
    (npowMorphism G q).comp snd
  let φ : Variety.Morphism (Variety.prod K0.carrierVariety G) G :=
    (AlgebraicGroup.mulMorphism G).comp (left.pair right)
  have hφ (z : Variety.Point (Variety.prod K0.carrierVariety G)) :
      φ.toFun z =
        P.kernelIdentityComponentMorphism.onPoints
            (Variety.prodPointEquiv K0.carrierVariety G z).1 *
          (Variety.prodPointEquiv K0.carrierVariety G z).2 ^ q := by
    simp [φ, left, right, fst, snd, Variety.Morphism.comp,
      Variety.Morphism.pair, AlgebraicGroup.mulMorphism,
      npowMorphism_apply, Variety.prodPointEquiv]
    apply Variety.Point.ext
    rfl
  have hcarrier : (Msub : Set (Variety.Point G)) = Set.range φ.toFun := by
    ext g
    constructor
    · intro hg
      change QuotientGroup.mk' H.toSubgroup g ∈
        (powMonoidHom q :
          (Variety.Point G ⧸ H.toSubgroup) →*
            (Variety.Point G ⧸ H.toSubgroup)).range at hg
      rcases hg with ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective H.toSubgroup x
      have hquot : QuotientGroup.mk' H.toSubgroup g =
          QuotientGroup.mk' H.toSubgroup (a ^ q) := by
        simpa using hx.symm
      have hh : g / a ^ q ∈ H.toSubgroup :=
        QuotientGroup.eq_iff_div_mem.mp hquot
      change g / a ^ q ∈ P.kernelIdentityComponentMorphism.image at hh
      rcases hh with ⟨z, hz⟩
      let w := (Variety.prodPointEquiv K0.carrierVariety G).symm (z, a)
      refine ⟨w, ?_⟩
      rw [hφ]
      simp only [w, Equiv.apply_symm_apply, hz]
      exact div_mul_cancel g (a ^ q)
    · rintro ⟨z, rfl⟩
      change QuotientGroup.mk' H.toSubgroup (φ.toFun z) ∈
        (powMonoidHom q :
          (Variety.Point G ⧸ H.toSubgroup) →*
            (Variety.Point G ⧸ H.toSubgroup)).range
      let a := (Variety.prodPointEquiv K0.carrierVariety G z).2
      refine ⟨QuotientGroup.mk' H.toSubgroup a, ?_⟩
      simp only [powMonoidHom_apply]
      rw [hφ]
      rw [map_mul, map_pow]
      have hleft : P.kernelIdentityComponentMorphism.onPoints
          (Variety.prodPointEquiv K0.carrierVariety G z).1 ∈ H.toSubgroup := by
        change _ ∈ P.kernelIdentityComponentMorphism.image
        exact ⟨_, rfl⟩
      have hleftq : QuotientGroup.mk' H.toSubgroup
          (P.kernelIdentityComponentMorphism.onPoints
            (Variety.prodPointEquiv K0.carrierVariety G z).1) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hleft
      rw [hleftq, one_mul]
  have hconstruct : Topology.IsConstructible
      (Msub : Set (Variety.Point G)) := by
    rw [hcarrier]
    exact φ.range_isConstructible
  have hclosed : IsClosed (Msub : Set (Variety.Point G)) :=
    constructible_subgroup_isClosed G Msub hconstruct
  let M : ClosedSubgroup G := ClosedSubgroup.ofSubgroup Msub
    (Variety.isClosed_iff_isZariskiClosed.mp hclosed)
  letI : AlgebraicGroup M.carrierVariety := M.carrierAlgebraicGroup
  have hHM : H.toSubgroup ≤ Msub := by
    intro x hx
    change QuotientGroup.mk' H.toSubgroup x ∈
      (powMonoidHom q :
        (Variety.Point G ⧸ H.toSubgroup) →*
          (Variety.Point G ⧸ H.toSubgroup)).range
    refine ⟨1, ?_⟩
    simp only [powMonoidHom_apply, one_pow]
    exact ((QuotientGroup.eq_one_iff _).mpr hx).symm
  have hHK : H.toSubgroup ≤ K.toSubgroup :=
    P.kernelIdentityComponent_le_unipotentRadical
  have hinc (x : Variety.Point G) :
      P.diagonalImage.inclusion.onPoints
          (P.diagonalImageMorphism.onPoints x) =
        P.diagonalMorphism.onPoints x := by
    simpa only [TriangularPresentation.diagonalImageMorphism] using
      (AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
        P.diagonalMorphism P.diagonalImage
        (fun z => by
          change P.diagonalMorphism.onPoints z ∈ P.diagonalMorphism.image
          exact ⟨z, rfl⟩) x)
  have hdiagSurj : Function.Surjective
      P.diagonalImageMorphism.onPoints := by
    intro y
    have hy := (P.diagonalImage.pointEquiv y).property
    change (P.diagonalImage.pointEquiv y).val ∈
      P.diagonalMorphism.image at hy
    rcases hy with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply P.diagonalImage.inclusion_injective
    rw [hinc]
    exact hx
  have hpowI := IsTorus.pow_primePower_bijective
    (P.diagonalImage_isTorus hG) p P.n
  have hdiagM (y : Variety.Point P.diagonalImage.carrierVariety) :
      ∃ m : Variety.Point G,
        m ∈ Msub ∧ P.diagonalImageMorphism.onPoints m = y := by
    rcases hpowI.2 y with ⟨a, ha⟩
    rcases hdiagSurj a with ⟨g, hg⟩
    refine ⟨g ^ q, ?_, ?_⟩
    · change QuotientGroup.mk' H.toSubgroup (g ^ q) ∈
        (powMonoidHom q :
          (Variety.Point G ⧸ H.toSubgroup) →*
            (Variety.Point G ⧸ H.toSubgroup)).range
      refine ⟨QuotientGroup.mk' H.toSubgroup g, ?_⟩
      simp only [powMonoidHom_apply, map_pow]
    · rw [map_pow, hg]
      simpa [q] using ha
  have hMcapK_le_H {x : Variety.Point G}
      (hxM : x ∈ Msub) (hxK : x ∈ K.toSubgroup) :
      x ∈ H.toSubgroup := by
    change QuotientGroup.mk' H.toSubgroup x ∈
      (powMonoidHom q :
        (Variety.Point G ⧸ H.toSubgroup) →*
          (Variety.Point G ⧸ H.toSubgroup)).range at hxM
    rcases hxM with ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective H.toSubgroup z
    have hquot : QuotientGroup.mk' H.toSubgroup x =
        QuotientGroup.mk' H.toSubgroup (a ^ q) := by
      simpa using hz.symm
    have hdiff : x / a ^ q ∈ H.toSubgroup :=
      QuotientGroup.eq_iff_div_mem.mp hquot
    have hdiffK : x / a ^ q ∈ K.toSubgroup := hHK hdiff
    have hpowK : a ^ q ∈ K.toSubgroup := by
      have hm := K.toSubgroup.mul_mem (K.toSubgroup.inv_mem hdiffK) hxK
      simpa [div_eq_mul_inv, mul_assoc] using hm
    have hdiagPow : P.diagonalMorphism.onPoints (a ^ q) = 1 := by
      exact hpowK
    have hdiagImagePow :
        P.diagonalImageMorphism.onPoints a ^ q = 1 := by
      apply P.diagonalImage.inclusion_injective
      calc
        P.diagonalImage.inclusion.onPoints
            (P.diagonalImageMorphism.onPoints a ^ q) =
            P.diagonalMorphism.onPoints (a ^ q) := by
              rw [map_pow, map_pow, hinc]
        _ = 1 := hdiagPow
        _ = P.diagonalImage.inclusion.onPoints 1 :=
          P.diagonalImage.inclusion.map_one.symm
    have hdiagImage : P.diagonalImageMorphism.onPoints a = 1 := by
      apply hpowI.1
      simpa [q] using hdiagImagePow
    have haK : a ∈ K.toSubgroup := by
      change P.diagonalMorphism.onPoints a = 1
      calc
        P.diagonalMorphism.onPoints a =
            P.diagonalImage.inclusion.onPoints
              (P.diagonalImageMorphism.onPoints a) := (hinc a).symm
        _ = P.diagonalImage.inclusion.onPoints 1 :=
          congrArg P.diagonalImage.inclusion.onPoints hdiagImage
        _ = 1 := P.diagonalImage.inclusion.map_one
    have haq : a ^ q = 1 := by
      simpa [q] using P.unipotentRadical_pow_primePower_eq_one p a haK
    have hxq : QuotientGroup.mk' H.toSubgroup x = 1 := by
      simpa [haq] using hquot
    exact (QuotientGroup.eq_one_iff _).mp hxq
  let : Msub.Normal := by
    rw [← Subgroup.commutator_top_right_le_iff]
    exact (Subgroup.commutator_mono le_top le_rfl).trans (hcomm.trans hHM)
  let Kcomp := AlgebraicGroup.identityComponentSubgroup K.carrierVariety
  let : Kcomp.Normal := by
    change (AlgebraicGroup.identityComponentSubgroup K.carrierVariety).Normal
    rw [← AlgebraicGroup.identityComponentClosedSubgroup_carrier]
    exact AlgebraicGroup.identityComponentClosedSubgroup_isNormal K.carrierVariety
  have hK0M : Kcomp ≤
      Subgroup.comap K.inclusion.onPoints Msub := by
    intro z hz
    change K.inclusion.onPoints z ∈ Msub
    apply hHM
    change K.inclusion.onPoints z ∈ P.kernelIdentityComponentMorphism.image
    have hz0 : z ∈ K0.toSubgroup := by
      change z ∈ (AlgebraicGroup.identityComponentClosedSubgroup
        K.carrierVariety).toSubgroup
      rw [AlgebraicGroup.identityComponentClosedSubgroup_carrier]
      exact hz
    let z0 : Variety.Point K0.carrierVariety :=
      K0.pointEquiv.symm ⟨z, hz0⟩
    refine ⟨z0, ?_⟩
    have hinner : K0.inclusion.onPoints z0 = z := by
      change (K0.pointEquiv z0).val = z
      simp [z0]
    exact congrArg K.inclusion.onPoints hinner
  let qmap := QuotientGroup.map Kcomp Msub
    K.inclusion.onPoints hK0M
  have hqmapSurj : Function.Surjective qmap := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Msub y
    rcases hdiagM (P.diagonalImageMorphism.onPoints g) with
      ⟨m, hmM, hmg⟩
    have hgmK : g / m ∈ K.toSubgroup := by
      change P.diagonalMorphism.onPoints (g / m) = 1
      rw [map_div]
      calc
        P.diagonalMorphism.onPoints g /
            P.diagonalMorphism.onPoints m =
            P.diagonalImage.inclusion.onPoints
                (P.diagonalImageMorphism.onPoints g) /
              P.diagonalImage.inclusion.onPoints
                (P.diagonalImageMorphism.onPoints m) := by
                  rw [hinc, hinc]
        _ = 1 := by rw [hmg]; simp
    let kg : Variety.Point K.carrierVariety :=
      K.pointEquiv.symm ⟨g / m, hgmK⟩
    refine ⟨QuotientGroup.mk' Kcomp kg, ?_⟩
    rw [QuotientGroup.map_mk']
    have hkg : K.inclusion.onPoints kg = g / m := by
      change (K.pointEquiv kg).val = g / m
      simp [kg]
    have hmone : QuotientGroup.mk' Msub m = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmM
    calc
      QuotientGroup.mk' Msub (K.inclusion.onPoints kg) =
          QuotientGroup.mk' Msub (g / m) := congrArg _ hkg
      _ = QuotientGroup.mk' Msub g / QuotientGroup.mk' Msub m :=
        by rw [map_div]
      _ = QuotientGroup.mk' Msub g / 1 := by rw [hmone]
      _ = QuotientGroup.mk' Msub g := div_one _
  let : Finite (Variety.Point K.carrierVariety ⧸ Kcomp) := by
    simpa [Kcomp] using finite_quotient_identityComponentSubgroup K.carrierVariety
  let : Finite (Variety.Point G ⧸ Msub) :=
    Finite.of_surjective qmap hqmapSurj
  let : Msub.FiniteIndex := Msub.finiteIndex_of_finite_quotient
  let : M.toSubgroup.FiniteIndex := by
    change Msub.FiniteIndex
    infer_instance
  have hG0 : AlgebraicGroup.identityComponent G = Set.univ :=
    (identityComponent_eq_univ_iff_isConnected G).mpr hG
  have hGM : ∀ x : Variety.Point G, x ∈ Msub := by
    intro x
    exact identityComponent_subset_of_finiteIndexSubgroup G M (by rw [hG0]; trivial)
  have hKH : K.toSubgroup ≤ H.toSubgroup := by
    intro x hx
    exact hMcapK_le_H (hGM x) hx
  have hK0univ : AlgebraicGroup.identityComponent K.carrierVariety =
      Set.univ := by
    apply Set.eq_univ_of_univ_subset
    intro z _
    have hzK : K.inclusion.onPoints z ∈ K.toSubgroup :=
      (K.pointEquiv z).property
    have hzH : K.inclusion.onPoints z ∈ H.toSubgroup := hKH hzK
    change K.inclusion.onPoints z ∈ P.kernelIdentityComponentMorphism.image at hzH
    rcases hzH with ⟨z0, hz0⟩
    have heq : K0.inclusion.onPoints z0 = z := by
      apply K.inclusion_injective
      exact hz0
    rw [← heq]
    exact (K0.pointEquiv z0).property
  exact (identityComponent_eq_univ_iff_isConnected K.carrierVariety).mp hK0univ

/-- Theorem 1.5.1(a) (Lie--Kolchin): every connected solvable algebraic
group is isomorphic to a closed subgroup of an upper-triangular group of
positive degree. -/
public theorem exists_iso_closedSubgroup_tVariety_of_isSolvable_isConnected
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G) :
    ∃ n : ℕ, 0 < n ∧ ∃ H : ClosedSubgroup (tVariety k n),
      letI := H.carrierAlgebraicGroup
      Nonempty (AlgebraicGroup.Iso G H.carrierVariety) := by
  let : Module.Finite k (coordinateTranslationSubmodule G) :=
    coordinateTranslationSubmodule_finite G
  let trivialRepresentation : RationalRepresentation G k := ⟨1⟩
  have trivialRational : IsRationalRepresentation trivialRepresentation := by
    let e : Module.Basis (Fin (Module.finrank k k)) k k := Module.finBasis k k
    let coefficient : Fin (Module.finrank k k) → Fin (Module.finrank k k) →
        G.PolynomialFunction := fun i j =>
      algebraMap k G.PolynomialFunction (e.repr (e j) i)
    let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
      e trivialRepresentation.action coefficient coefficient
      (by
        intro i j g
        rw [polynomialFunction_algebraMap_apply]
        simp [trivialRepresentation])
      (by
        intro i j g
        rw [polynomialFunction_algebraMap_apply]
        simp [trivialRepresentation])
    refine ⟨e, f, ?_⟩
    intro g
    change glPointEquivOf k k e
      (generalLinearRepresentationPoint e (trivialRepresentation.action g)) = _
    exact glPointEquivOf_generalLinearRepresentationPoint e
      (trivialRepresentation.action g)
  let coordinateRepresentation :
      RationalRepresentation G (coordinateTranslationSubmodule G) :=
    coordinateTranslationRationalRepresentation G
  have coordinateRational : IsRationalRepresentation coordinateRepresentation :=
    coordinateTranslationRationalRepresentation_isRational G
  obtain ⟨ρ, hρsum, hρ⟩ := rationalRepresentation_directSum_exists
    trivialRepresentation coordinateRepresentation trivialRational coordinateRational
  have hρinjective : Function.Injective ρ.action := by
    intro g h hgh
    apply coordinateTranslationRepresentation_injective G
    apply Units.ext
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun A : LinearMap.GeneralLinearGroup k
      (k × coordinateTranslationSubmodule G) =>
        (A : Module.End k (k × coordinateTranslationSubmodule G)) (0, v)) hgh
    have hgv := hρsum g (0 : k) v
    have hhv := hρsum h (0 : k) v
    rw [hgv, hhv] at hv
    exact congrArg Prod.snd hv
  obtain ⟨b, hb⟩ :=
    ρ.exists_basis_tTriangular_of_isSolvable_isConnected
      hρ hsolvable hconnected
  let f := triangularRepresentationMorphismOfBasis ρ hρ b hb
  have hcoordinate : ∀ c : G.Coordinates,
      ∃ q : Variety.PolynomialFunction (tVariety k
        (Module.finrank k (k × coordinateTranslationSubmodule G))),
        Variety.PolynomialFunction.pullback f.toVariety q =
          coordinatePolynomialFunction G c := by
    intro c
    let K : Module.Dual k (k × coordinateTranslationSubmodule G) :=
      { toFun := fun z =>
          polynomialFunctionSubspaceEvaluation G
            (coordinateTranslationSubmodule G) 1 z.2
        map_add' := by intro x y; simp
        map_smul' := by intro a x; simp }
    let v : k × coordinateTranslationSubmodule G :=
      (0, coordinateTranslationCoordinateVector G c)
    refine ⟨triangularLinearMatrixCoefficientPreimage (k := k) b K v, ?_⟩
    apply Variety.PolynomialFunction.ext
    intro g
    change triangularLinearMatrixCoefficientPreimage (k := k) b K v
      (f.onPoints g) = coordinatePolynomialFunction G c g
    rw [triangularLinearMatrixCoefficientPreimage_apply ρ hρ b hb K v g]
    change polynomialFunctionSubspaceEvaluation G
      (coordinateTranslationSubmodule G) 1
      ((ρ.action g : Module.End k (k × coordinateTranslationSubmodule G)) v).2 = _
    rw [hρsum]
    change (rightTranslationOnCoordinateSubmodule G g
      (coordinateTranslationCoordinateVector G c)).val 1 = _
    rw [rightTranslationOnCoordinateSubmodule_apply, rightTranslationPullback_apply]
    change coordinatePolynomialFunction G c (1 * g) = coordinatePolynomialFunction G c g
    rw [one_mul]
  letI : AlgebraicGroup f.imageClosedSubgroup.carrierVariety :=
    f.imageClosedSubgroup.carrierAlgebraicGroup
  obtain ⟨e, _⟩ :=
    triangularRepresentationMorphismOfBasis_iso_imageClosedSubgroup
      ρ hρ b hb hρinjective hcoordinate
  let : Module.Free k (coordinateTranslationSubmodule G) :=
    Module.Free.of_divisionRing k (coordinateTranslationSubmodule G)
  have hn : 0 < Module.finrank k (k × coordinateTranslationSubmodule G) := by
    rw [Module.finrank_prod, Module.finrank_self]
    omega
  refine ⟨Module.finrank k (k × coordinateTranslationSubmodule G), hn,
    f.imageClosedSubgroup, ?_⟩
  exact ⟨e⟩

end Theory.AlgebraicGroup
