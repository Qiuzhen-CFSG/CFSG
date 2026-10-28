module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ThreeCenters
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.PointRadicalRoots

/-!
# Literal local actors in the three-center configuration

The chosen symplectic frame embeds the three marked transvections in the
actual point-local group. Their b₁ types and first-pair noncommutation are
preserved, so neither of the first two disappears in the literal SL₂
quotient. These are the original actors, transported by the original frame;
no abstract isomorphism or replacement subgroup is chosen.

This connects the source three-center producer to the radical calculation
in Aschbacher--Smith G.4.9, printed p.341. The quotient subgroup recognition
and commuting-coset existence remain independent subsequent steps.
-/

@[expose] public noncomputable section

open Subgroup Module
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ThreeCenterConfiguration
open InvolutionTypes InvolutionCentralizers
variable {F : Type*} [Field F] [CharP F 2] {X : Subgroup (Sp F)} {a : Sp F}

omit [CharP F 2] in
/-- The actual frame sends every marked fixed-point element into pointLocal. -/
def localActor (D : ThreeCenterConfiguration X a) (g : Sp F)
    (hg : g • D.point=D.point) : pointLocal (F:=F) :=
  ⟨D.frame*g*D.frame⁻¹,by
    rw [mem_pointLocal_iff_fixed,mul_smul,mul_smul]
    have he : D.frame⁻¹ • e (F:=F) 0=D.point := by
      rw [←D.frame_point,inv_smul_smul]
    rw [he,hg,D.frame_point]⟩

omit [CharP F 2] in
def firstLocal (D : ThreeCenterConfiguration X a) : pointLocal (F:=F) :=
  D.localActor a D.first_fixes

omit [CharP F 2] in
def secondLocal (D : ThreeCenterConfiguration X a) : pointLocal (F:=F) :=
  D.localActor ((D.x : Sp F)*a*(D.x : Sp F)⁻¹) D.second_fixes

omit [CharP F 2] in
def thirdLocal (D : ThreeCenterConfiguration X a) : pointLocal (F:=F) :=
  D.localActor ((D.y : Sp F)*a*(D.y : Sp F)⁻¹) D.third_fixes

omit [CharP F 2] in
theorem localActor_coe (D : ThreeCenterConfiguration X a) (g : Sp F)
    (hg : g • D.point=D.point) : (D.localActor g hg).val=D.frame*g*D.frame⁻¹ := rfl

omit [CharP F 2] in
theorem firstLocal_isB1 (D : ThreeCenterConfiguration X a) (ha : IsB1 a) :
    IsB1 D.firstLocal.val := (isB1_conj_iff D.frame a).mpr ha

omit [CharP F 2] in
theorem secondLocal_isB1 (D : ThreeCenterConfiguration X a) (ha : IsB1 a) :
    IsB1 D.secondLocal.val :=
  (isB1_conj_iff (F:=F) D.frame ((D.x : Sp F)*a*(D.x : Sp F)⁻¹)).mpr
    ((isB1_conj_iff (F:=F) (D.x : Sp F) a).mpr ha)

omit [CharP F 2] in
theorem thirdLocal_isB1 (D : ThreeCenterConfiguration X a) (ha : IsB1 a) :
    IsB1 D.thirdLocal.val :=
  (isB1_conj_iff (F:=F) D.frame ((D.y : Sp F)*a*(D.y : Sp F)⁻¹)).mpr
    ((isB1_conj_iff (F:=F) (D.y : Sp F) a).mpr ha)

/-- Noncommutation survives the literal conjugation and subgroup restriction. -/
theorem firstLocal_secondLocal_noncommute (D : ThreeCenterConfiguration X a) :
    ¬Commute D.firstLocal D.secondLocal := by
  intro hc
  apply D.second_noncommuting
  apply (MulAut.conj D.frame).injective
  have he := congrArg (fun g : pointLocal (F:=F) => g.val) hc.eq
  simpa only [firstLocal,secondLocal,localActor,Subgroup.coe_mul,MulAut.conj_apply,
    mul_assoc,inv_mul_cancel_left] using he

/-- Neither of the first two marked roots disappears in the actual SL₂ quotient. -/
theorem first_second_quotient_ne_one (D : ThreeCenterConfiguration X a) (ha : IsB1 a) :
    pointQuotient D.firstLocal≠1 ∧ pointQuotient D.secondLocal≠1 := by
  exact ⟨pointQuotient_ne_one_of_isB1_noncommuting D.firstLocal D.secondLocal
      (D.firstLocal_isB1 ha) D.firstLocal_secondLocal_noncommute,
    pointQuotient_ne_one_of_isB1_noncommuting D.secondLocal D.firstLocal
      (D.secondLocal_isB1 ha) (fun h => D.firstLocal_secondLocal_noncommute h.symm)⟩

/-- The first two quotient roots retain order two in the literal SL₂ group. -/
theorem first_second_quotient_orderOf (D : ThreeCenterConfiguration X a) (ha : IsB1 a) :
    orderOf (pointQuotient D.firstLocal)=2 ∧ orderOf (pointQuotient D.secondLocal)=2 := by
  have hs (t : pointLocal (F:=F)) (ht : IsB1 t.val) : t^2=1 := by
    apply Subtype.ext
    simpa only [Subgroup.coe_pow,Subgroup.coe_one,ht.1] using pow_orderOf_eq_one t.val
  have hn := D.first_second_quotient_ne_one ha
  exact ⟨orderOf_eq_prime (by rw [←map_pow,hs _ (D.firstLocal_isB1 ha),map_one]) hn.1,
    orderOf_eq_prime (by rw [←map_pow,hs _ (D.secondLocal_isB1 ha),map_one]) hn.2⟩

/-- The marked pair remains noncommuting after passage to the actual quotient. -/
theorem first_second_quotient_noncommute [Finite F]
    (D : ThreeCenterConfiguration X a) (ha : IsB1 a) :
    ¬Commute (pointQuotient D.firstLocal) (pointQuotient D.secondLocal) := by
  have hlocal : ¬Commute D.firstLocal.val D.secondLocal.val := by
    intro hh
    apply D.firstLocal_secondLocal_noncommute
    exact Subtype.ext hh.eq
  have ho := odd_order_product_of_isB1 D.firstLocal.val D.secondLocal.val
    (D.firstLocal_isB1 ha) (D.secondLocal_isB1 ha) hlocal
  have hom : Odd (orderOf (D.firstLocal*D.secondLocal)) := by
    rw [←orderOf_injective (pointLocal (F:=F)).subtype Subtype.coe_injective]
    exact ho
  have hone (t : pointLocal (F:=F)) (ht : Odd (orderOf t))
      (hq : pointQuotient t=1) : t=1 := by
    have hs := pointRadical_pow_two (⟨t,hq⟩ : pointRadical (F:=F))
    have hts : t^2=1 := congrArg (fun g : pointRadical (F:=F) => g.val) hs
    have hd : orderOf t∣2 := orderOf_dvd_of_pow_eq_one hts
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
    · exact orderOf_eq_one_iff.mp he
    · rw [he] at ht
      exact False.elim (ht.not_two_dvd_nat dvd_rfl)
  intro hh
  obtain ⟨hoa,hob⟩ := D.first_second_quotient_orderOf ha
  have hsq : (pointQuotient D.firstLocal*pointQuotient D.secondLocal)^2=1 := by
    rw [hh.mul_pow]
    have has : (pointQuotient D.firstLocal)^2=1 := by
      simpa only [hoa] using pow_orderOf_eq_one (pointQuotient D.firstLocal)
    have hbs : (pointQuotient D.secondLocal)^2=1 := by
      simpa only [hob] using pow_orderOf_eq_one (pointQuotient D.secondLocal)
    rw [has,hbs,mul_one]
  have hd := orderOf_dvd_of_pow_eq_one hsq
  have hdiv : orderOf (pointQuotient D.firstLocal*pointQuotient D.secondLocal)∣
      orderOf (D.firstLocal*D.secondLocal) := by
    simpa only [map_mul] using orderOf_map_dvd pointQuotient (D.firstLocal*D.secondLocal)
  have he : pointQuotient (D.firstLocal*D.secondLocal)=1 := by
    rw [map_mul,←orderOf_eq_one_iff]
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact h
    · exact False.elim (hom.not_two_dvd_nat ((dvd_of_eq h.symm).trans hdiv))
  have hprod := hone _ hom he
  have hab : D.secondLocal=D.firstLocal⁻¹ := eq_inv_of_mul_eq_one_right hprod
  exact D.firstLocal_secondLocal_noncommute (by rw [hab]; exact Commute.inv_right (Commute.refl _))

omit [CharP F 2] in
/-- The literal subgroup generated by the three framed actors. -/
def localGenerated (D : ThreeCenterConfiguration X a) : Subgroup (pointLocal (F:=F)) :=
  Subgroup.closure ({D.firstLocal,D.secondLocal,D.thirdLocal} : Set (pointLocal (F:=F)))

omit [CharP F 2] in
/-- Its image under the existing concrete point-local quotient. -/
def quotientImage (D : ThreeCenterConfiguration X a) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
  D.localGenerated.map pointQuotient

omit [CharP F 2] in
def firstImage (D : ThreeCenterConfiguration X a) : D.quotientImage :=
  ⟨pointQuotient D.firstLocal,⟨D.firstLocal,Subgroup.subset_closure (by simp),rfl⟩⟩

omit [CharP F 2] in
def secondImage (D : ThreeCenterConfiguration X a) : D.quotientImage :=
  ⟨pointQuotient D.secondLocal,⟨D.secondLocal,Subgroup.subset_closure (by simp),rfl⟩⟩

/-- Both quotient involutions live in the exact image subgroup used by Dickson. -/
theorem image_pair_orderOf (D : ThreeCenterConfiguration X a) (ha : IsB1 a) :
    orderOf D.firstImage=2 ∧ orderOf D.secondImage=2 := by
  obtain ⟨h1,h2⟩ := D.first_second_quotient_orderOf ha
  exact ⟨(orderOf_coe D.firstImage).symm.trans h1,
    (orderOf_coe D.secondImage).symm.trans h2⟩

/-- The exact image subgroup has a noncommuting marked involution pair. -/
theorem image_pair_noncommute [Finite F]
    (D : ThreeCenterConfiguration X a) (ha : IsB1 a) :
    ¬Commute D.firstImage D.secondImage := by
  intro hh
  exact D.first_second_quotient_noncommute ha (hh.map D.quotientImage.subtype)

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ThreeCenterConfiguration
