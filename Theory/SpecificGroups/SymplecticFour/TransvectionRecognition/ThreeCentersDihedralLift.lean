module
public import Theory.GroupTheory.DihedralCentralLift
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.CosetRadicalCentral
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.CentralRootLifts
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ProductPlane
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ThreeCentersRecognition

/-!
# Excluding the odd-dihedral three-center image

Failure of the original commuting-coset witness makes the literal local
radical central. The third marked root survives in the quotient: otherwise
it is a central radical transvection and supplies that same witness directly.
An odd-dihedral quotient then has a rotation conjugator through the central
kernel. Its lift centralizes the first-pair product; uniqueness of transvection
lifts identifies its conjugate with the third root, contradicting the moved
plane of that product.

Thus the actual quotient image in Aschbacher--Smith G.4.9, printed p.341,
must be an SL₂ subfield group under the no-witness assumption. The subsequent
SL₂ Sylow lift, needed to remove that assumption, is a separate step.
-/

@[expose] public noncomputable section
open Subgroup Module
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ThreeCenterConfiguration
open InvolutionTypes InvolutionCentralizers
variable {F : Type*} [Field F] [CharP F 2] {X : Subgroup (Sp F)} {a : Sp F}

/-- A disappearing third root already provides the original coset witness. -/
theorem third_quotient_ne_one_of_no_coset_witness
    (D : ThreeCenterConfiguration X a) (ha : IsB1 a)
    (han : a∈normalizer (X : Set (Sp F)))
    (hno : ¬∃ b : Sp F, IsB1 b ∧ a⁻¹*b∈X ∧ Commute a b ∧ a*b∈X ∧ IsC2 (a*b)) :
    pointQuotient D.thirdLocal≠1 := by
  intro hq
  have hcentral := pointRadical_transvection_central D.thirdLocal hq (D.thirdLocal_isB1 ha)
  let c := (D.y : Sp F)*a*(D.y : Sp F)⁻¹
  have hc : IsB1 c := (isB1_conj_iff (D.y : Sp F) a).mpr ha
  have hcomm : Commute a c := by
    have h := (show Commute D.firstLocal D.thirdLocal from
      Subgroup.mem_center_iff.mp hcentral D.firstLocal).map pointLocal.subtype
    change (D.frame*a*D.frame⁻¹)*(D.frame*c*D.frame⁻¹)=(D.frame*c*D.frame⁻¹)*(D.frame*a*D.frame⁻¹) at h
    apply (MulAut.conj D.frame).injective
    change (D.frame*(a*c)*D.frame⁻¹)=(D.frame*(c*a)*D.frame⁻¹)
    simpa only [firstLocal,thirdLocal,localActor,c,Subgroup.coe_mul,mul_assoc,
      inv_mul_cancel_left] using h
  have hne : movedSpace a≠movedSpace c := by
    intro he
    have hlocal : movedSpace D.firstLocal.val=movedSpace D.thirdLocal.val := by
      change movedSpace (D.frame*a*D.frame⁻¹)=movedSpace (D.frame*c*D.frame⁻¹)
      rw [movedSpace_conj,movedSpace_conj,he]
    apply (D.first_second_quotient_ne_one ha).1
    apply pointQuotient_eq_one_of_movedSpace_le_point
    rw [hlocal,pointRadical_movedSpace_of_isB1 D.thirdLocal hq (D.thirdLocal_isB1 ha)]
  have hcoset : a⁻¹*c∈X := D.conjugate_in_coset han D.y
  exact hno ⟨c,hc,hcoset,hcomm,isC2_mem_of_commuting_coset X a c ha hc hcomm hne hcoset⟩

omit [CharP F 2] in
/-- The literal point quotient restricted to the actual generated subgroup. -/
def generatedQuotient (D : ThreeCenterConfiguration X a) : D.localGenerated →* D.quotientImage :=
  (pointQuotient.comp D.localGenerated.subtype).codRestrict D.quotientImage
    (fun t => ⟨t.val,t.property,rfl⟩)

omit [CharP F 2] in
theorem generatedQuotient_surjective (D : ThreeCenterConfiguration X a) :
    Function.Surjective D.generatedQuotient := by
  rintro ⟨t,⟨g,hg,rfl⟩⟩
  exact ⟨⟨g,hg⟩,rfl⟩


/-- The original no-witness assumption excludes every odd-dihedral model of the actual image. -/
theorem not_dihedral_of_no_coset_witness [Finite F]
    (D : ThreeCenterConfiguration X a) (ha : IsB1 a)
    (han : a∈normalizer (X : Set (Sp F)))
    (hno : ¬∃ b : Sp F, IsB1 b ∧ a⁻¹*b∈X ∧ Commute a b ∧ a*b∈X ∧ IsC2 (a*b))
    {m : ℕ} (hm : Odd m) (e : D.quotientImage ≃* DihedralGroup m) : False := by
  let f : D.localGenerated →* DihedralGroup m := e.toMonoidHom.comp D.generatedQuotient
  have hf : Function.Surjective f := e.surjective.comp D.generatedQuotient_surjective
  have hz := D.radicalIntersection_central_of_no_coset_witness ha han hno
  have hfker : f.ker≤Subgroup.center D.localGenerated := by
    intro t ht
    change e (D.generatedQuotient t)=1 at ht
    have htq : pointQuotient t.val=1 := by
      have he : D.generatedQuotient t=1 := e.injective (by simpa only [map_one] using ht)
      exact congrArg Subtype.val he
    apply mem_center_iff.mpr
    intro s
    exact Subtype.ext (mem_center_iff.mp (hz ⟨t.property,htq⟩) s.val)
  let aL : D.localGenerated := ⟨D.firstLocal,subset_closure (by simp)⟩
  let bL : D.localGenerated := ⟨D.secondLocal,subset_closure (by simp)⟩
  let cL : D.localGenerated := ⟨D.thirdLocal,subset_closure (by simp)⟩
  have horder (t : D.localGenerated) : orderOf (f t)=orderOf (pointQuotient t.val) := by
    rw [show f t=e (D.generatedQuotient t) from rfl,e.orderOf_eq]
    exact (orderOf_coe (D.generatedQuotient t)).symm
  have ha2 : orderOf (f aL)=2 := (horder aL).trans (D.first_second_quotient_orderOf ha).1
  have hb2 : orderOf (f bL)=2 := (horder bL).trans (D.first_second_quotient_orderOf ha).2
  have hcq : pointQuotient D.thirdLocal≠1 := D.third_quotient_ne_one_of_no_coset_witness ha han hno
  have hc2 : orderOf (f cL)=2 := by
    rw [horder]
    apply orderOf_eq_prime _ hcq
    rw [←map_pow]
    have hs : D.thirdLocal^2=1 := Subtype.ext (by
      simpa only [Subgroup.coe_pow,Subgroup.coe_one,(D.thirdLocal_isB1 ha).1] using pow_orderOf_eq_one D.thirdLocal.val)
    rw [hs,map_one]
  obtain ⟨g,hg,hgc⟩ := f.exists_dihedral_conjugator_centralizing_product hf hfker hm aL bL cL ha2 hb2 hc2
  have hgcq : pointQuotient (g.val*D.firstLocal*g.val⁻¹)=pointQuotient D.thirdLocal :=
    congrArg Subtype.val (e.injective hgc)
  have hmem : g.val*D.firstLocal*g.val⁻¹∈D.localGenerated :=
    D.localGenerated.mul_mem (D.localGenerated.mul_mem g.property aL.property)
      (D.localGenerated.inv_mem g.property)
  have hdiff : (g.val*D.firstLocal*g.val⁻¹)⁻¹*D.thirdLocal∈Subgroup.center (pointLocal (F:=F)) := by
    apply hz
    refine ⟨D.localGenerated.mul_mem (D.localGenerated.inv_mem hmem) cL.property,?_⟩
    change pointQuotient ((g.val*D.firstLocal*g.val⁻¹)⁻¹*D.thirdLocal)=1
    rw [map_mul,map_inv,hgcq,inv_mul_cancel]
  have htype : IsB1 (g.val*D.firstLocal*g.val⁻¹).val :=
    (isB1_conj_iff g.val.val D.firstLocal.val).mpr (D.firstLocal_isB1 ha)
  have heq : g.val*D.firstLocal*g.val⁻¹=D.thirdLocal :=
    eq_of_isB1_same_pointQuotient _ _ htype (D.thirdLocal_isB1 ha)
      (by rwa [hgcq]) hgcq hdiff
  let s := D.frame⁻¹*g.val.val*D.frame
  have hsg : (MulAut.conj D.frame) s=g.val.val := by
    dsimp [s,MulAut.conj_apply]
    group
  have hcomm : Commute s (a*((D.x : Sp F)*a*(D.x : Sp F)⁻¹)) := by
    apply (MulAut.conj D.frame).injective
    have h := (hg.map D.localGenerated.subtype).map pointLocal.subtype
    change Commute g.val.val (D.firstLocal.val*D.secondLocal.val) at h
    change _ = _
    simpa only [map_mul,hsg,firstLocal,secondLocal,localActor,aL,bL,
      MulAut.conj_apply,Subgroup.subtype_apply,Subgroup.coe_mul,mul_assoc,
      inv_mul_cancel_left] using h.eq
  apply D.third_not_rotation_conjugate ha s hcomm
  apply (MulAut.conj D.frame).injective
  have h := congrArg (fun t : pointLocal (F:=F) => t.val) heq.symm
  simpa only [map_mul,map_inv,hsg,firstLocal,thirdLocal,localActor,MulAut.conj_apply,
    Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_rev,inv_inv,mul_assoc,
    inv_mul_cancel_left,mul_inv_cancel_left] using h


/-- The actual Dickson image is SL₂ once the original commuting-coset witness
is excluded. No central-kernel or lifting premise remains. -/
theorem quotientImage_sl2_of_no_coset_witness [Finite F] {n : ℕ}
    (hF : Nat.card F=2^n) (D : ThreeCenterConfiguration X a) (ha : IsB1 a)
    (han : a∈normalizer (X : Set (Sp F)))
    (hno : ¬∃ b : Sp F, IsB1 b ∧ a⁻¹*b∈X ∧ Commute a b ∧ a*b∈X ∧ IsC2 (a*b)) :
    ∃ k : ℕ, 1<k ∧ k∣n ∧
      Nonempty (D.quotientImage ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) := by
  rcases D.quotientImage_recognition hF ha with ⟨m,hm,_,⟨e⟩⟩ | hSL
  · exact (D.not_dihedral_of_no_coset_witness ha han hno hm e).elim
  · exact hSL

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ThreeCenterConfiguration
