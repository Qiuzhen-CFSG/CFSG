module
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.Envelope
public import Theory.AlgebraicGroup.Bor1.SingularTorusQuotient.Centralizer

/-!
# Fixed-radical dimensions through the actual rank-one quotient

For a subtorus `S≤T`, restrict the chosen radical quotient of `C(S)` to
`B_u^S`. Its kernel is unipotent inside the centralizer radical, whose
unipotent radical already maps into the candidate `I(T)_u`. The dimension
formula for this literal morphism therefore transfers a one-dimensional
image bound to the original fixed subgroup, without assuming normality of
`I(T)_u`.

The Borel consumer places that image in the actual quotient Borel's
unipotent radical. The independent rank-one geometry owner supplies its
dimension bound. Source: Borel, *Linear Algebraic Groups*, IV, 13.15(1).
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SingularTorusQuotient
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
open SemisimpleCenterContainment.RadicalGeometry
open SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

private theorem dimension_mono {A B : ClosedSubgroup G} (hAB : A ≤ B) :
    Variety.dimension A.carrierVariety ≤ Variety.dimension B.carrierVariety := by
  rw [← A.dimension_identityComponentAmbient]
  exact connected_closedSubgroup_dimension_le_of_le A.identityComponentAmbient B
    A.identityComponentAmbient_isConnected (fun _ hx => hAB (A.identityComponentAmbient_le hx))

private theorem image_dimension_eq_of_injective
    {H Q : Variety k} [AlgebraicGroup H] [AlgebraicGroup Q]
    (f : AlgebraicGroup.Morphism H Q) (hf : Function.Injective f.onPoints) :
    Variety.dimension f.imageClosedSubgroup.carrierVariety = Variety.dimension H := by
  let : Subsingleton f.kernelClosedSubgroup.toSubgroup := by
    constructor
    intro x y
    apply Subtype.ext
    apply hf
    exact x.property.trans y.property.symm
  let : Subsingleton (Variety.Point f.kernelClosedSubgroup.carrierVariety) :=
    f.kernelClosedSubgroup.pointEquiv.subsingleton
  have hzero : Variety.dimension f.kernelClosedSubgroup.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points _).2 inferInstance
  have heq := morphism_dimension_eq_kernel_add_image f
  rw [hzero,zero_add] at heq
  exact heq.symm

/-- The rank-one image bound gives the original fixed-radical dimension bound
through the literal radical quotient. Its kernel maps into `I(T)_u`; ambient
normality of that candidate radical is not assumed. -/
theorem fixed_radical_dimension_le_of_radical_quotient_image
    (hG : Variety.IsConnected G) {S T U B V : ClosedSubgroup G}
    (hS : IsSubtorus S) (hT : IsSubtorus T) (hST : S ≤ T)
    (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (hV : IsUnipotentRadicalOf B V)
    (R W : ClosedSubgroup S.centralizer.carrierVariety)
    (hR : IsRadicalSubgroup R) (hW : IsUnipotentRadicalOf R W)
    {Q : Variety k} [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism S.centralizer.carrierVariety Q)
    (hker : q.kernel = R.toSubgroup)
    (himage :
      let X := V.pointwiseCentralizer S
      let i := X.inclusion.codRestrictClosedSubgroup S.centralizer
        (fun x => (X.pointEquiv x).property.2)
      Variety.dimension (q.comp i).imageClosedSubgroup.carrierVariety ≤ 1) :
    Variety.dimension (V.pointwiseCentralizer S).carrierVariety ≤
      Variety.dimension ((V.pointwiseCentralizer S).inter U).carrierVariety + 1 := by
  let X := V.pointwiseCentralizer S
  let _ : AlgebraicGroup X.carrierVariety := X.carrierAlgebraicGroup
  let C := S.centralizer
  let i := X.inclusion.codRestrictClosedSubgroup C
    (fun x => (X.pointEquiv x).property.2)
  let f := q.comp i
  let _ : AlgebraicGroup f.imageClosedSubgroup.carrierVariety := f.imageClosedSubgroup.carrierAlgebraicGroup
  let K := f.kernelClosedSubgroup
  let _ : AlgebraicGroup K.carrierVariety := K.carrierAlgebraicGroup
  let j := X.inclusion.comp K.inclusion
  let r := i.comp K.inclusion
  let _ : AlgebraicGroup r.imageClosedSubgroup.carrierVariety := r.imageClosedSubgroup.carrierAlgebraicGroup
  have hX : IsUnipotentAlgebraicGroup X.carrierVariety :=
    unipotent_of_le (fun _ hx => hx.1) hV.2.1
  have hK : IsUnipotentAlgebraicGroup K.carrierVariety := by
    intro x
    exact (closedSubgroup_unipotentElement_iff K (K.pointEquiv x).property).mp
      (hX (K.includePoint x))
  have hrR : r.imageClosedSubgroup ≤ R := by
    rintro x ⟨a,rfl⟩
    change r.onPoints a ∈ R.toSubgroup
    rw [← hker]
    exact (K.pointEquiv a).property
  have hrW : r.imageClosedSubgroup ≤ W := by
    apply hW.contains_unipotent_closedSubgroup hR.connected hR.solvable hrR
    exact hK.of_surjective
      (r.codRestrictClosedSubgroup r.imageClosedSubgroup (fun x => ⟨x,rfl⟩))
      (r.codRestrictImageClosedSubgroup_surjective (fun x => ⟨x,rfl⟩))
  have hjU : j.imageClosedSubgroup ≤ U := by
    rintro x ⟨a,rfl⟩
    have ha : r.onPoints a ∈ W := hrW ⟨a,rfl⟩
    apply centralizer_unipotent_radical_image_le hG hS hT hST hU R W hR hW
    refine ⟨W.pointEquiv.symm ⟨r.onPoints a,ha⟩, ?_⟩
    change C.inclusion.onPoints (r.onPoints a) = j.onPoints a
    exact Morphism.codRestrictClosedSubgroup_inclusion_apply X.inclusion C
      (fun x => (X.pointEquiv x).property.2) (K.includePoint a)
  have hjXU : j.imageClosedSubgroup ≤ X.inter U := by
    intro x hx
    refine ⟨?_,hjU hx⟩
    obtain ⟨a,rfl⟩ := hx
    exact (X.pointEquiv (K.includePoint a)).property
  have hj : Function.Injective j.onPoints := by
    intro a b hab
    exact K.inclusion_injective (X.inclusion_injective hab)
  have hkdim : Variety.dimension K.carrierVariety ≤ Variety.dimension (X.inter U).carrierVariety := by
    rw [← image_dimension_eq_of_injective j hj]
    exact dimension_mono hjXU
  have hd := morphism_dimension_eq_kernel_add_image f
  change Variety.dimension X.carrierVariety ≤ Variety.dimension (X.inter U).carrierVariety + 1
  rw [hd]
  exact add_le_add hkdim himage

/-- The only quotient-model input needed for 13.15(1) is the dimension of
Borel unipotent radicals. The actual quotient image of `V^S` is placed in
such a radical; equality with it is unnecessary. -/
theorem fixed_radical_dimension_le_of_quotient_borel_radicals
    (hG : Variety.IsConnected G) {S T U B V : ClosedSubgroup G}
    (hS : IsSubtorus S) (hT : IsSubtorus T) (hST : S ≤ T)
    (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (hB : IsBorelSubgroup B) (hSB : S ≤ B) (hV : IsUnipotentRadicalOf B V)
    (R : ClosedSubgroup S.centralizer.carrierVariety) (hR : IsRadicalSubgroup R)
    {Q : Variety k} [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism S.centralizer.carrierVariety Q)
    (hq : Function.Surjective q.onPoints) (hker : q.kernel = R.toSubgroup)
    (hsmall : ∀ A N : ClosedSubgroup Q, IsBorelSubgroup A →
      IsUnipotentRadicalOf A N → Variety.dimension N.carrierVariety ≤ 1) :
    Variety.dimension (V.pointwiseCentralizer S).carrierVariety ≤
      Variety.dimension ((V.pointwiseCentralizer S).inter U).carrierVariety + 1 := by
  obtain ⟨W,hW⟩ := exists_unipotent_radical R hR
  apply fixed_radical_dimension_le_of_radical_quotient_image hG hS hT hST hU hV R W hR hW q hker
  let X := V.pointwiseCentralizer S
  let _ : AlgebraicGroup X.carrierVariety := X.carrierAlgebraicGroup
  let C := S.centralizer
  let i := X.inclusion.codRestrictClosedSubgroup C (fun x => (X.pointEquiv x).property.2)
  let f := q.comp i
  let _ : AlgebraicGroup f.imageClosedSubgroup.carrierVariety := f.imageClosedSubgroup.carrierAlgebraicGroup
  let A := C.inclusion.closedSubgroupPreimage B
  let _ : AlgebraicGroup A.carrierVariety := A.carrierAlgebraicGroup
  have hA : IsBorelSubgroup A :=
    SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.isBorel_centralizer_restriction
      hG S B hS hB hSB
  let Aq := (q.comp A.inclusion).imageClosedSubgroup
  let _ : AlgebraicGroup Aq.carrierVariety := Aq.carrierAlgebraicGroup
  have hAq : IsBorelSubgroup Aq := TorusFree.borel_image_of_solvable_kernel
    q hq (hR.quotient_kernel_isSolvable q hker) A hA
  obtain ⟨N,hN,_⟩ := exists_unipotentRadical_of_connected_solvable Aq hAq.connected hAq.solvable
  have hfA : f.imageClosedSubgroup ≤ Aq := by
    rintro x ⟨a,rfl⟩
    have ha : i.onPoints a ∈ A := hV.1 (X.pointEquiv a).property.1
    exact ⟨A.pointEquiv.symm ⟨i.onPoints a,ha⟩,rfl⟩
  have hfU : IsUnipotentAlgebraicGroup f.imageClosedSubgroup.carrierVariety := by
    have hX : IsUnipotentAlgebraicGroup X.carrierVariety :=
      unipotent_of_le (fun _ hx => hx.1) hV.2.1
    exact hX.of_surjective
      (f.codRestrictClosedSubgroup f.imageClosedSubgroup (fun x => ⟨x,rfl⟩))
      (f.codRestrictImageClosedSubgroup_surjective (fun x => ⟨x,rfl⟩))
  have hfN := hN.contains_unipotent_closedSubgroup hAq.connected hAq.solvable hfA hfU
  exact (dimension_mono hfN).trans (hsmall Aq N hAq hN)

end Theory.AlgebraicGroup.Bor1.SingularTorusQuotient
