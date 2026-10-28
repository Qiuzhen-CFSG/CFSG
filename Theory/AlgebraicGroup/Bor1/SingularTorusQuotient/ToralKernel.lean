module
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.Envelope
public import Theory.AlgebraicGroup.Tori.UnipotentIntersection
public import Theory.AlgebraicGroup.Bor1.SingularTorusQuotient.RankOne

/-!
# Killing the envelope image in the actual radical quotient

In Bor1 IV, 13.15(2)--13.16, the separating Borel places the fixed subgroup
of `H=(I(B^S)∩B_u)^0` in two distinct restricted Borels. This module carries
those exact Borels through the chosen radical quotient of `C(Q)`: their
images remain distinct and contain the image of the original maximal torus.
The independent semisimple rank-one intersection theorem makes their
intersection toral. The unipotent image is therefore trivial, and its
literal kernel maps into `I(T)_u` by the centralizer-radical containment.

This proves the precise fixed-subgroup bound used by the normalizer argument.
It neither assumes ambient normality of `I(T)_u` nor replaces the quotient
maps by abstract isomorphic groups. Separating-Borel and rank-one model
geometry remain the independent source inputs of the final consumer.
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SingularTorusQuotient
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
open SemisimpleCenterContainment.RadicalGeometry
open SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

/-- An actual unipotent subgroup of `C(S)` whose radical-quotient image is
toral lies in `I(T)_u`. No normality of `I(T)_u` is required. -/
theorem unipotent_le_intersection_radical_of_toral_quotient_image
    (hG : Variety.IsConnected G) {S T U X : ClosedSubgroup G}
    (hS : IsSubtorus S) (hT : IsSubtorus T) (hST : S ≤ T)
    (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (hX : IsUnipotentAlgebraicGroup X.carrierVariety) (hXC : X ≤ S.centralizer)
    (R : ClosedSubgroup S.centralizer.carrierVariety) (hR : IsRadicalSubgroup R)
    {Q : Variety k} [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism S.centralizer.carrierVariety Q)
    (hker : q.kernel = R.toSubgroup)
    (D : ClosedSubgroup Q) (hD : IsSubtorus D)
    (himage :
      let i := X.inclusion.codRestrictClosedSubgroup S.centralizer
        (fun x => hXC (X.pointEquiv x).property)
      (q.comp i).imageClosedSubgroup ≤ D) : X ≤ U := by
  let _ : AlgebraicGroup X.carrierVariety := X.carrierAlgebraicGroup
  let C := S.centralizer
  let i := X.inclusion.codRestrictClosedSubgroup C
    (fun x => hXC (X.pointEquiv x).property)
  let f := q.comp i
  let _ : AlgebraicGroup i.imageClosedSubgroup.carrierVariety := i.imageClosedSubgroup.carrierAlgebraicGroup
  let _ : AlgebraicGroup f.imageClosedSubgroup.carrierVariety := f.imageClosedSubgroup.carrierAlgebraicGroup
  have hfU : IsUnipotentAlgebraicGroup f.imageClosedSubgroup.carrierVariety :=
    hX.of_surjective
      (f.codRestrictClosedSubgroup f.imageClosedSubgroup (fun x => ⟨x,rfl⟩))
      (f.codRestrictImageClosedSubgroup_surjective (fun x => ⟨x,rfl⟩))
  have hf (x : Variety.Point X.carrierVariety) : f.onPoints x = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← subtorus_inf_unipotent_eq_bot D f.imageClosedSubgroup hD hfU]
    exact ⟨himage ⟨x,rfl⟩,⟨x,rfl⟩⟩
  have hiR : i.imageClosedSubgroup ≤ R := by
    rintro x ⟨a,rfl⟩
    change i.onPoints a ∈ R.toSubgroup
    rw [← hker]
    exact hf a
  obtain ⟨W,hW⟩ := exists_unipotent_radical R hR
  let _ : AlgebraicGroup W.carrierVariety := W.carrierAlgebraicGroup
  have hiW : i.imageClosedSubgroup ≤ W := by
    apply hW.contains_unipotent_closedSubgroup hR.connected hR.solvable hiR
    exact hX.of_surjective
      (i.codRestrictClosedSubgroup i.imageClosedSubgroup (fun x => ⟨x,rfl⟩))
      (i.codRestrictImageClosedSubgroup_surjective (fun x => ⟨x,rfl⟩))
  intro x hx
  let a := X.pointEquiv.symm ⟨x,hx⟩
  have ha : i.onPoints a ∈ W := hiW ⟨a,rfl⟩
  apply centralizer_unipotent_radical_image_le hG hS hT hST hU R W hR hW
  refine ⟨W.pointEquiv.symm ⟨i.onPoints a,ha⟩,?_⟩
  change C.inclusion.onPoints (i.onPoints a) = x
  exact Morphism.codRestrictClosedSubgroup_inclusion_apply X.inclusion C
    (fun x => hXC (X.pointEquiv x).property) a

/-- A separating Borel places the literal envelope fixed subgroup in the
toral intersection of the two actual quotient Borels. -/
theorem envelope_fixed_le_radical_of_separating_toral_images
    (hG : Variety.IsConnected G) {S P T U B B' V : ClosedSubgroup G}
    (hP : IsSubtorus P) (hT : IsSubtorus T) (hPT : P ≤ T)
    (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (hB' : IsBorelSubgroup B')
    (hV : IsUnipotentRadicalOf B V)
    (hsep : B'.pointwiseCentralizer S = B.pointwiseCentralizer S)
    (R : ClosedSubgroup P.centralizer.carrierVariety) (hR : IsRadicalSubgroup R)
    {Q : Variety k} [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism P.centralizer.carrierVariety Q)
    (hker : q.kernel = R.toSubgroup)
    (D : ClosedSubgroup Q) (hD : IsSubtorus D)
    (hinter :
      let A := P.centralizer.inclusion.closedSubgroupPreimage B
      let A' := P.centralizer.inclusion.closedSubgroupPreimage B'
      letI : AlgebraicGroup A.carrierVariety := A.carrierAlgebraicGroup
      letI : AlgebraicGroup A'.carrierVariety := A'.carrierAlgebraicGroup
      (q.comp A.inclusion).imageClosedSubgroup.inter
        (q.comp A'.inclusion).imageClosedSubgroup ≤ D) :
    (unipotentEnvelope (B.pointwiseCentralizer S) V).pointwiseCentralizer P ≤ U := by
  let H := unipotentEnvelope (B.pointwiseCentralizer S) V
  let X := H.pointwiseCentralizer P
  let _ : AlgebraicGroup X.carrierVariety := X.carrierAlgebraicGroup
  have hXC : X ≤ P.centralizer := fun _ hx => hx.2
  have hX : IsUnipotentAlgebraicGroup X.carrierVariety :=
    unipotent_of_le (fun _ hx => hx.1)
      (unipotentEnvelope_connected_unipotent (B.pointwiseCentralizer S) V hV.2.1).2
  apply unipotent_le_intersection_radical_of_toral_quotient_image
    hG hP hT hPT hU hX hXC R hR q hker D hD
  let i := X.inclusion.codRestrictClosedSubgroup P.centralizer
    (fun x => hXC (X.pointEquiv x).property)
  have hHB : H ≤ B := by
    intro x hx
    exact hV.1 (((torusBorelIntersection (B.pointwiseCentralizer S)).inter V).identityComponentAmbient_le hx).2
  have hHB' : H ≤ B' := by
    intro x hx
    apply torusBorelIntersection_le_borel (B.pointwiseCentralizer S) B' hB'
      (fun a ha => (hsep ▸ ha).1)
    exact (((torusBorelIntersection (B.pointwiseCentralizer S)).inter V).identityComponentAmbient_le hx).1
  change (q.comp i).imageClosedSubgroup ≤ D
  rintro x ⟨a,rfl⟩
  apply hinter
  constructor
  · let A := P.centralizer.inclusion.closedSubgroupPreimage B
    have ha : i.onPoints a ∈ A := by
      change P.centralizer.inclusion.onPoints (i.onPoints a) ∈ B
      rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
      exact hHB (X.pointEquiv a).property.1
    exact ⟨A.pointEquiv.symm ⟨i.onPoints a,ha⟩,rfl⟩
  · let A' := P.centralizer.inclusion.closedSubgroupPreimage B'
    have ha : i.onPoints a ∈ A' := by
      change P.centralizer.inclusion.onPoints (i.onPoints a) ∈ B'
      rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
      exact hHB' (X.pointEquiv a).property.1
    exact ⟨A'.pointEquiv.symm ⟨i.onPoints a,ha⟩,rfl⟩

private theorem quotient_images_ne_of_kernel_le
    {Q : Variety k} [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism G Q) {A B : ClosedSubgroup G}
    (hA : q.kernel ≤ A.toSubgroup) (hB : q.kernel ≤ B.toSubgroup)
    (hne : A ≠ B) :
    (q.comp A.inclusion).imageClosedSubgroup ≠ (q.comp B.inclusion).imageClosedSubgroup := by
  have hle {D E : ClosedSubgroup G} (hE : q.kernel ≤ E.toSubgroup)
      (hDE : (q.comp D.inclusion).imageClosedSubgroup ≤ (q.comp E.inclusion).imageClosedSubgroup) :
      D ≤ E := by
    intro d hd
    have him : q.onPoints d ∈ (q.comp D.inclusion).imageClosedSubgroup :=
      ⟨D.pointEquiv.symm ⟨d,hd⟩,rfl⟩
    obtain ⟨e,he⟩ := hDE him
    have hker : (E.includePoint e)⁻¹ * d ∈ q.kernel := by
      change q.onPoints ((E.includePoint e)⁻¹ * d) = 1
      rw [map_mul,map_inv]
      change ((q.comp E.inclusion).onPoints e)⁻¹ * q.onPoints d = 1
      rw [he,inv_mul_cancel]
    have hm := E.toSubgroup.mul_mem (E.pointEquiv e).property (hE hker)
    change E.includePoint e * ((E.includePoint e)⁻¹ * d) ∈ E.toSubgroup at hm
    rw [mul_inv_cancel_left] at hm
    exact hm
  intro heq
  apply hne
  apply SetLike.coe_injective
  exact Set.Subset.antisymm
    (hle hB (fun x hx => heq ▸ hx))
    (hle hA (fun x hx => heq.symm ▸ hx))

/-- The two restricted Borels stay distinct under the literal radical
quotient. The radical belongs to each of them, so no quotient ambiguity
or arbitrary choice of a conjugate Borel is introduced. -/
theorem restricted_borel_quotient_images_ne
    (hG : Variety.IsConnected G) {P B B' : ClosedSubgroup G}
    (hP : IsSubtorus P) (hB : IsBorelSubgroup B) (hB' : IsBorelSubgroup B')
    (hPB : P ≤ B) (hPB' : P ≤ B')
    (hne : B.pointwiseCentralizer P ≠ B'.pointwiseCentralizer P)
    (R : ClosedSubgroup P.centralizer.carrierVariety) (hR : IsRadicalSubgroup R)
    {Q : Variety k} [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism P.centralizer.carrierVariety Q)
    (hker : q.kernel = R.toSubgroup) :
    let A := P.centralizer.inclusion.closedSubgroupPreimage B
    let A' := P.centralizer.inclusion.closedSubgroupPreimage B'
    letI : AlgebraicGroup A.carrierVariety := A.carrierAlgebraicGroup
    letI : AlgebraicGroup A'.carrierVariety := A'.carrierAlgebraicGroup
    (q.comp A.inclusion).imageClosedSubgroup ≠ (q.comp A'.inclusion).imageClosedSubgroup := by
  let C := P.centralizer
  let A := C.inclusion.closedSubgroupPreimage B
  let A' := C.inclusion.closedSubgroupPreimage B'
  have hA := BorelRestriction.isBorel_centralizer_restriction hG P B hP hB hPB
  have hA' := BorelRestriction.isBorel_centralizer_restriction hG P B' hP hB' hPB'
  have hRA : R ≤ A := normal_connected_solvable_le_borel R A hR.normal hR.connected hR.solvable hA
  have hRA' : R ≤ A' := normal_connected_solvable_le_borel R A' hR.normal hR.connected hR.solvable hA'
  apply quotient_images_ne_of_kernel_le q
  · rw [hker]
    exact hRA
  · rw [hker]
    exact hRA'
  · intro heq
    change A = A' at heq
    apply hne
    apply SetLike.coe_injective
    ext x
    constructor
    · intro hx
      have ha : C.pointEquiv.symm ⟨x,hx.2⟩ ∈ A := hx.1
      have ha' : C.pointEquiv.symm ⟨x,hx.2⟩ ∈ A' := heq ▸ ha
      exact ⟨ha',hx.2⟩
    · intro hx
      have ha' : C.pointEquiv.symm ⟨x,hx.2⟩ ∈ A' := hx.1
      have ha : C.pointEquiv.symm ⟨x,hx.2⟩ ∈ A := heq.symm ▸ ha'
      exact ⟨ha,hx.2⟩

private theorem internal_maximal {T C : ClosedSubgroup G}
    (hT : IsMaximalTorus T) (hTC : T ≤ C) :
    IsMaximalTorus (T.inclusion.codRestrictClosedSubgroup C
      (fun x => hTC (T.pointEquiv x).property)).imageClosedSubgroup := by
  let j := T.inclusion.codRestrictClosedSubgroup C
    (fun x => hTC (T.pointEquiv x).property)
  let A := j.imageClosedSubgroup
  have hj (x : Variety.Point T.carrierVariety) :
      C.inclusion.onPoints (j.onPoints x) = T.inclusion.onPoints x :=
    Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
  have hAmem (x : Variety.Point C.carrierVariety) : x ∈ A ↔ C.inclusion.onPoints x ∈ T := by
    constructor
    · rintro ⟨t,rfl⟩
      rw [hj]
      exact (T.pointEquiv t).property
    · intro hx
      refine ⟨T.pointEquiv.symm ⟨C.inclusion.onPoints x,hx⟩,C.inclusion_injective ?_⟩
      rw [hj]
      rfl
  refine ⟨morphism_image_isTorus j hT.1, ?_⟩
  intro R hR hAR
  let : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
  let f := C.inclusion.comp R.inclusion
  have hTf : T ≤ f.imageClosedSubgroup := by
    intro t ht
    let c := C.pointEquiv.symm ⟨t,hTC ht⟩
    have hc : c ∈ R := hAR ((hAmem c).mpr ht)
    exact ⟨R.pointEquiv.symm ⟨c,hc⟩,rfl⟩
  have hfT := hT.2 _ (morphism_image_isTorus f hR) hTf
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro r hr
    apply (hAmem r).mpr
    rw [← hfT]
    exact ⟨R.pointEquiv.symm ⟨r,hr⟩,rfl⟩
  · exact hAR


/-- The literal two restricted quotient Borels contain a common maximal torus,
namely the quotient image of the original ambient torus. No general common-
torus theorem for arbitrary pairs of Borels is used. -/
theorem restricted_borel_quotient_common_maximalTorus
    {P T B B' : ClosedSubgroup G} (hT : IsMaximalTorus T)
    (hPT : P ≤ T) (hTB : T ≤ B) (hTB' : T ≤ B')
    (R : ClosedSubgroup P.centralizer.carrierVariety) (hR : IsRadicalSubgroup R)
    {Q : Variety k} [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism P.centralizer.carrierVariety Q)
    (hq : Function.Surjective q.onPoints) (hker : q.kernel = R.toSubgroup) :
    let A := P.centralizer.inclusion.closedSubgroupPreimage B
    let A' := P.centralizer.inclusion.closedSubgroupPreimage B'
    letI : AlgebraicGroup A.carrierVariety := A.carrierAlgebraicGroup
    letI : AlgebraicGroup A'.carrierVariety := A'.carrierAlgebraicGroup
    ∃ D : ClosedSubgroup Q, IsMaximalTorus D ∧
      D ≤ (q.comp A.inclusion).imageClosedSubgroup ∧
      D ≤ (q.comp A'.inclusion).imageClosedSubgroup := by
  let C := P.centralizer
  have hTC : T ≤ C := by
    intro t ht
    apply Subgroup.mem_centralizer_iff.mpr
    intro p hp
    exact Subgroup.mem_centralizer_iff.mp (maximalTorus_le_centralizer hT ht) p (hPT hp)
  let j := T.inclusion.codRestrictClosedSubgroup C
    (fun x => hTC (T.pointEquiv x).property)
  let E := j.imageClosedSubgroup
  let _ : AlgebraicGroup E.carrierVariety := E.carrierAlgebraicGroup
  have hE : IsMaximalTorus E := internal_maximal hT hTC
  let D := (q.comp E.inclusion).imageClosedSubgroup
  have hD : IsMaximalTorus D := maximalTorus_image_of_solvable_kernel q hq
    (hR.quotient_kernel_isSolvable q hker) hE
  have hle (B0 : ClosedSubgroup G) (hTB0 : T ≤ B0) :
      let A0 := C.inclusion.closedSubgroupPreimage B0
      letI : AlgebraicGroup A0.carrierVariety := A0.carrierAlgebraicGroup
      D ≤ (q.comp A0.inclusion).imageClosedSubgroup := by
    dsimp only
    rintro x ⟨e,rfl⟩
    let A0 := C.inclusion.closedSubgroupPreimage B0
    have he : E.includePoint e ∈ A0 := by
      obtain ⟨t,ht⟩ := (E.pointEquiv e).property
      change C.inclusion.onPoints (E.includePoint e) ∈ B0
      change j.onPoints t = E.includePoint e at ht
      rw [← ht]
      rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
      exact hTB0 (T.pointEquiv t).property
    exact ⟨A0.pointEquiv.symm ⟨E.includePoint e,he⟩,rfl⟩
  exact ⟨D,hD,hle B hTB,hle B' hTB'⟩

/-- The source separating Borel and the independent rank-one intersection
geometry give exactly the fixed-subgroup containment needed in 13.16.
Both target Borels, their distinctness, and their common maximal torus are
constructed along the supplied radical quotient. -/
theorem envelope_fixed_le_radical_of_rankOne_intersections
    (hG : Variety.IsConnected G) {S P T U B B' V : ClosedSubgroup G}
    (hP : IsSubtorus P) (hT : IsMaximalTorus T) (hPT : P ≤ T)
    (hTB : T ≤ B) (hTB' : T ≤ B')
    (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (hB : IsBorelSubgroup B) (hB' : IsBorelSubgroup B')
    (hV : IsUnipotentRadicalOf B V)
    (hsep : B'.pointwiseCentralizer S = B.pointwiseCentralizer S)
    (hne : B.pointwiseCentralizer P ≠ B'.pointwiseCentralizer P)
    (R : ClosedSubgroup P.centralizer.carrierVariety) (hR : IsRadicalSubgroup R)
    {Q : Variety k} [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism P.centralizer.carrierVariety Q)
    (hq : Function.Surjective q.onPoints) (hker : q.kernel = R.toSubgroup)
    (hgeometry : ∀ A A' D : ClosedSubgroup Q,
      IsBorelSubgroup A → IsBorelSubgroup A' → IsMaximalTorus D →
      D ≤ A → D ≤ A' → A ≠ A' → IsSubtorus (A.inter A')) :
    (unipotentEnvelope (B.pointwiseCentralizer S) V).pointwiseCentralizer P ≤ U := by
  let C := P.centralizer
  let A := C.inclusion.closedSubgroupPreimage B
  let A' := C.inclusion.closedSubgroupPreimage B'
  let _ : AlgebraicGroup A.carrierVariety := A.carrierAlgebraicGroup
  let _ : AlgebraicGroup A'.carrierVariety := A'.carrierAlgebraicGroup
  let Aq := (q.comp A.inclusion).imageClosedSubgroup
  let Aq' := (q.comp A'.inclusion).imageClosedSubgroup
  have hA : IsBorelSubgroup A := BorelRestriction.isBorel_centralizer_restriction
    hG P B hP hB (fun _ hx => hTB (hPT hx))
  have hA' : IsBorelSubgroup A' := BorelRestriction.isBorel_centralizer_restriction
    hG P B' hP hB' (fun _ hx => hTB' (hPT hx))
  have hAq : IsBorelSubgroup Aq := TorusFree.borel_image_of_solvable_kernel
    q hq (hR.quotient_kernel_isSolvable q hker) A hA
  have hAq' : IsBorelSubgroup Aq' := TorusFree.borel_image_of_solvable_kernel
    q hq (hR.quotient_kernel_isSolvable q hker) A' hA'
  obtain ⟨D,hD,hDA,hDA'⟩ := restricted_borel_quotient_common_maximalTorus
    hT hPT hTB hTB' R hR q hq hker
  have hneq : Aq ≠ Aq' := restricted_borel_quotient_images_ne hG hP hB hB'
    (fun _ hx => hTB (hPT hx)) (fun _ hx => hTB' (hPT hx)) hne R hR q hker
  have htoral := hgeometry Aq Aq' D hAq hAq' hD hDA hDA' hneq
  exact envelope_fixed_le_radical_of_separating_toral_images hG hP hT.1 hPT
    hU hB' hV hsep R hR q hker (Aq.inter Aq') htoral (fun _ hx => hx)

end Theory.AlgebraicGroup.Bor1.SingularTorusQuotient
