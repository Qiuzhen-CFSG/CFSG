module
public import Glauberman.PushingUpCenterIncidence
public import Theory.Representation.SL2FourQuadraticRecognition.NaturalActorCovering

/-!
# Pointwise commutator covering in the original center

Each Sylow element outside the two-core displaces the center of the core
onto the Sylow center modulo the ambient center. Conversely, the Sylow
orbit of each core-center vector outside the Sylow center supplies every
coset in the same quotient. The natural fixed quotient gives both lift
formulas; translating through the original conjugation action retains the
literal elements and multiplication. The corresponding subgroup joins
are equal to the full embedded Sylow center.

Source: Niles, *Pushing-up in finite groups* (1979), Theorem 4.7(d),
printed page 48. These are its original endpoint covering statements,
before restriction to point cells and transport along the diagram.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

theorem original_psl2_four_center_vector_covering
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α)
    (y : H) (hyV : y ∈ centerIn (pCore 2 H)) (hyZ : y ∉ centerIn (S : Subgroup H)) :
    ∀ z ∈ centerIn (S : Subgroup H),
      ∃ s ∈ (S : Subgroup H), z * ⁅s,y⁆⁻¹ ∈ center H := by
  have hcenter := (original_psl2_four_omegaCenters_eq_centers hF S α hu K e hf hno).2
  obtain ⟨_,hfixed⟩ := original_psl2_four_full_center_fixed_spaces hF S α hu K e hf hno
  let v : Additive (omegaCenterIn (pCore 2 H)) := Additive.ofMul ⟨y, hcenter.symm ▸ hyV⟩
  have hv : v ∉ fixedSpace (omegaAction H) (S : Subgroup H) := by
    intro hh
    apply hyZ
    rw [←hfixed]
    exact ⟨v.toMul.property, (omegaAction_fixedSpace H (S : Subgroup H) v).mp hh⟩
  obtain ⟨q,hq,_,_,_,_,E,hE⟩ := original_psl2_four_omegaAction_recognition
    hF S hu K e hf hno.noCharacteristicNormal
  have hd := (original_psl2_four_omegaAction_sylow hF S hu K e hf
    hno.noCharacteristicNormal).2.2.1
  intro z hz
  have hz' : z ∈ omegaCenterIn (pCore 2 H) ⊓ centralizer ((S : Subgroup H) : Set H) := hfixed.symm ▸ hz
  let w : Additive (omegaCenterIn (pCore 2 H)) := Additive.ofMul ⟨z,hz'.1⟩
  have hw : w ∈ fixedSpace (omegaAction H) (S : Subgroup H) :=
    (omegaAction_fixedSpace H (S : Subgroup H) w).mpr hz'.2
  obtain ⟨s, hs, hr⟩ :=
    Representation.SL2FourQuadraticRecognition.sylow_vector_displacements_cover_fixed
      (omegaAction H) q hq E hE S hd v hv w hw
  have hc := (omegaAction_fixedSpace H ⊤ (w - (omegaAction H s v - v))).mp hr
  simp only [coe_top, centralizer_univ] at hc
  have heq : ((w - (omegaAction H s v - v)).toMul : H) = z * ⁅s,y⁆⁻¹ := by
    simp only [toMul_sub, div_eq_mul_inv]
    change z * (((omegaAction H s v).toMul : H) * y⁻¹)⁻¹ = _
    rw [omegaAction_apply]
    rfl
  exact ⟨s,hs,heq ▸ hc⟩

/-- Every Sylow element outside the core displaces enough center vectors to
cover the full Sylow center modulo the ambient center. -/
theorem original_psl2_four_center_actor_covering
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α)
    (x : H) (hxS : x ∈ (S : Subgroup H)) (hxQ : x ∉ pCore 2 H) :
    ∀ z ∈ centerIn (S : Subgroup H),
      ∃ y ∈ centerIn (pCore 2 H), z * ⁅x,y⁆⁻¹ ∈ center H := by
  have hcenter := (original_psl2_four_omegaCenters_eq_centers hF S α hu K e hf hno).2
  obtain ⟨_,hfixed⟩ := original_psl2_four_full_center_fixed_spaces hF S α hu K e hf hno
  obtain ⟨q,hq,hk,_,_,_,E,hE⟩ := original_psl2_four_omegaAction_recognition
    hF S hu K e hf hno.noCharacteristicNormal
  have hquad := (original_psl2_four_omegaAction_sylow hF S hu K e hf
    hno.noCharacteristicNormal).2.1
  have hqx : q x ≠ 1 := by
    intro he
    have hxker : x ∈ q.ker := he
    rw [hk] at hxker
    have hc := original_omega_sylow_centralizer_eq hF S hu K e q hq hk
    exact hxQ (hc ▸ (show x ∈ (S : Subgroup H) ⊓ centralizer
      (omegaCenterIn (pCore 2 H) : Set H) from ⟨hxS,hxker⟩))
  intro z hz
  have hz' : z ∈ omegaCenterIn (pCore 2 H) ⊓ centralizer ((S : Subgroup H) : Set H) := hfixed.symm ▸ hz
  let w : Additive (omegaCenterIn (pCore 2 H)) := Additive.ofMul ⟨z,hz'.1⟩
  have hw : w ∈ fixedSpace (omegaAction H) (S : Subgroup H) :=
    (omegaAction_fixedSpace H (S : Subgroup H) w).mpr hz'.2
  obtain ⟨v,hr⟩ := Representation.SL2FourQuadraticRecognition.sylow_actor_displacements_cover_fixed
    (omegaAction H) q hq E hE S hquad x hxS hqx w hw
  have hc := (omegaAction_fixedSpace H ⊤ (w - (omegaAction H x v - v))).mp hr
  simp only [coe_top, centralizer_univ] at hc
  have heq : ((w - (omegaAction H x v - v)).toMul : H) = z * ⁅x,(v.toMul : H)⁆⁻¹ := by
    simp only [toMul_sub, div_eq_mul_inv]
    change z * (((omegaAction H x v).toMul : H) * (v.toMul : H)⁻¹)⁻¹ = _
    rw [omegaAction_apply]
    rfl
  exact ⟨v.toMul,hcenter ▸ v.toMul.property,heq ▸ hc⟩

/-- The literal single-actor commutator covers the center quotient. -/
theorem original_psl2_four_actor_commutator_center
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α)
    (x : H) (hxS : x ∈ (S : Subgroup H)) (hxQ : x ∉ pCore 2 H) :
    ⁅zpowers x,centerIn (pCore 2 H)⁆ ⊔ center H = centerIn (S : Subgroup H) := by
  have hcover := original_psl2_four_center_commutator_covering hF S α hu K e hf hno
  apply le_antisymm
  · rw [←hcover,commutator_comm (centerIn (pCore 2 H))]
    exact sup_le_sup_right (commutator_mono (zpowers_le.mpr hxS) le_rfl) _
  · intro z hz
    obtain ⟨y,hy,hres⟩ := original_psl2_four_center_actor_covering hF S α hu K e hf hno x hxS hxQ z hz
    have hc := commutator_mem_commutator (mem_zpowers x) hy
    have hm := (⁅zpowers x,centerIn (pCore 2 H)⁆ ⊔ center H).mul_mem
      (mem_sup_right hres) (mem_sup_left hc)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm

/-- The literal orbit commutators of any nonfixed center vector cover the
same center quotient. -/
theorem original_psl2_four_vector_commutator_center
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α)
    (y : H) (hyV : y ∈ centerIn (pCore 2 H)) (hyZ : y ∉ centerIn (S : Subgroup H)) :
    ⁅(S : Subgroup H),zpowers y⁆ ⊔ center H = centerIn (S : Subgroup H) := by
  have hcover := original_psl2_four_center_commutator_covering hF S α hu K e hf hno
  apply le_antisymm
  · rw [←hcover,commutator_comm (centerIn (pCore 2 H))]
    exact sup_le_sup_right (commutator_mono le_rfl (zpowers_le.mpr hyV)) _
  · intro z hz
    obtain ⟨s,hs,hres⟩ := original_psl2_four_center_vector_covering hF S α hu K e hf hno y hyV hyZ z hz
    have hc := commutator_mem_commutator hs (mem_zpowers y)
    have hm := (⁅(S : Subgroup H),zpowers y⁆ ⊔ center H).mul_mem
      (mem_sup_right hres) (mem_sup_left hc)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm

end Glauberman
