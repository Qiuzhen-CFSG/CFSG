module
public import Theory.SpecificGroups.PSL2.BorelCoprimeFieldAction
public import Theory.GroupTheory.QuotientSylowNormalizerDisplacement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Normalizer.Coefficients
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Components
public import Theory.GroupTheory.OddElementLift

/-!
# Simultaneous PSL₂ subfield Borel normalizer lifts

Sylow conjugacy aligns the literal I/O₂(I) projection. The original Sylow
acts semilinearly on its Borel, and the inner Borel factor disappears on
the coefficient quotient. Its two-power field factors fix the constructed
odd-degree subfield. Every coefficient in that subfield therefore lifts
to N_G(T), by the quotient-displacement criterion.

A coprime original Cartan mover retains a nontrivial odd coefficient action.
Restriction preserves its nontriviality. An odd-order power of a moved
normalizer lift gives the literal BorelMovement required in 11.5.6(3).
No subfield subgroup, torus alignment, invariant Borel or normalizer-lift
premise is imposed. Fixation of the component by T is discharged by the
three-rank isolation consumer in RankOneComponent.

Source: Aschbacher--Smith 11.5.6(3), printed p.781.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.Converse Atlas
open scoped MatrixGroups commutatorElement
open Matrix.ProjectiveSpecialLinearGroup
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear.RankOne
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I : Subgroup G}

/-- Coordinates on the literal quotient, aligned with the original Sylow intersection. -/
structure Coordinates (T : Sylow 2 G) (I : Subgroup G) (F : BinaryField) where
  model : (I ⧸ pCore 2 I) ≃* PSL(2,F.Carrier)
  sylow_image : ((T : Subgroup G).subgroupOf I).map
    (model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) = OddBorel.kernel F.Carrier

namespace Coordinates
variable {F : BinaryField} (c : Coordinates T I F)

def quotient : I →* PSL(2,F.Carrier) :=
  c.model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))

omit [Finite G] in
theorem quotient_surjective : Function.Surjective c.quotient :=
  c.model.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem quotient_sylow_image : ((T : Subgroup G).subgroupOf I).map c.quotient =
    OddBorel.kernel F.Carrier := c.sylow_image

def localBorel (_ : Coordinates T I F) : Subgroup I := normalizer ((T : Subgroup G).subgroupOf I : Set I)

def borelMap : c.localBorel →* OddBorel.borel F.Carrier :=
  (c.quotient.comp c.localBorel.subtype).codRestrict (OddBorel.borel F.Carrier) (by
    intro b
    rw [← normalizer_kernel, ← c.quotient_sylow_image]
    exact ((T : Subgroup G).subgroupOf I).le_normalizer_map c.quotient
      (mem_map_of_mem c.quotient b.property))

def coefficient : c.localBorel →* F.Carrierˣ :=
  (torusProjection F.Carrier).comp c.borelMap

theorem borelMap_surjective (hTI : (T : Subgroup G) ≤ normalizer (I : Set G)) :
    Function.Surjective c.borelMap := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T I hTI
  have he := P.normalizer_map_surjective c.quotient c.quotient_surjective
  change (normalizer ((P : Subgroup I) : Set I)).map c.quotient =
    normalizer ((P : Subgroup I).map c.quotient : Set PSL(2,F.Carrier)) at he
  rw [hP,c.quotient_sylow_image,normalizer_kernel] at he
  intro b
  have hb : (b : PSL(2,F.Carrier)) ∈ c.localBorel.map c.quotient := by
    change _ ∈ (normalizer ((T : Subgroup G).subgroupOf I : Set I)).map c.quotient
    rw [he]
    exact b.property
  obtain ⟨i,hi,heq⟩ := hb
  exact ⟨⟨i,hi⟩,Subtype.ext heq⟩

theorem coefficient_surjective (hTI : (T : Subgroup G) ≤ normalizer (I : Set G)) :
    Function.Surjective c.coefficient :=
  (torusProjection_surjective F.Carrier).comp (c.borelMap_surjective hTI)

def actor (x : normalizer (I : Set G)) : MulAut PSL(2,F.Carrier) :=
  MulAut.congr c.model (coreQuotientAction I x)

omit [Finite G] in
theorem actor_quotient (x : normalizer (I : Set G)) (i : I) :
    c.actor x (c.quotient i) = c.quotient (I.normalizerMonoidHom x i) := by
  change c.model (coreQuotientAction I x (c.model.symm
    (c.model (QuotientGroup.mk' (pCore 2 I) i)))) = _
  rw [c.model.symm_apply_apply,coreQuotientAction_apply_mk]
  rfl

omit [Finite G] in
theorem actor_preserves_root (x : normalizer (I : Set G))
    (hx : (x : G) ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G)) :
    (OddBorel.kernel F.Carrier).map (c.actor x).toMonoidHom = OddBorel.kernel F.Carrier := by
  rw [← c.quotient_sylow_image]
  have he : (c.actor x).toMonoidHom.comp c.quotient =
      c.quotient.comp (I.normalizerMonoidHom x).toMonoidHom := by
    ext i
    exact c.actor_quotient x i
  rw [map_map,he,← map_map]
  congr 1
  ext i
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact ((mem_normalizer_iff.mp hx j).mp ⟨hj,j.property⟩).1
  · intro hi
    refine ⟨(I.normalizerMonoidHom x).symm i,?_,(I.normalizerMonoidHom x).apply_symm_apply i⟩
    exact ((mem_normalizer_iff.mp ((normalizer _).inv_mem hx) i).mp
      ⟨hi,i.property⟩).1

/-- The original Sylow acts trivially on every odd-subfield Borel coefficient,
so each such Borel element already normalizes the whole original Sylow. -/
theorem normalizes_of_odd_coefficient
    (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    (b : c.localBorel) (u : (oddField F).Carrierˣ)
    (hbu : c.coefficient b = Units.map (oddInclusion F).toMonoidHom u) :
    (b.val : G) ∈ normalizer (T : Set G) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T I hTI
  have hk : c.quotient.ker ≤ (T : Subgroup G).subgroupOf I := by
    intro i hi
    have hi' : i ∈ pCore 2 I := (QuotientGroup.eq_one_iff _).mp
      (c.model.map_eq_one_iff.mp hi)
    rw [← hP]
    exact pCore_isPGroup.le_sylow_of_normal P hi'
  let a : T → MulAut PSL(2,F.Carrier) := fun t => c.actor ⟨t,hTI t.property⟩
  apply mem_normalizer_of_quotient_displacements (T : Subgroup G) I hTI
    c.quotient hk a (fun t i => c.actor_quotient ⟨t,hTI t.property⟩ i) b.val
  intro t
  have htS : (t : G) ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨(T : Subgroup G).le_normalizer t.property,hTI t.property⟩
  have hr := c.actor_preserves_root ⟨t,hTI t.property⟩ htS
  obtain ⟨g,σ,he⟩ := exists_inner_field F.Carrier (a t)
  have hg : g ∈ OddBorel.borel F.Carrier := inner_factor_mem_borel F.Carrier g σ (he ▸ hr)
  obtain ⟨k,hkpow⟩ := T.isPGroup'.exists_pow_pow_eq_one t
  have hapow : a t ^ (2 ^ k) = 1 := by
    let f := (MulAut.congr c.model).toMonoidHom.comp
      ((coreQuotientAction I).comp (inclusion hTI))
    change f t ^ (2 ^ k) = 1
    rw [← map_pow,hkpow,map_one]
  have hσ := field_pow_eq_one_of_actor_pow F.Carrier ⟨g,hg⟩ σ (2 ^ k) (he ▸ hapow)
  rw [c.quotient_sylow_image,he,← twoCoreIn_eq_kernel F.Carrier F.card_eq]
  apply (borelActor_commutator_mem_core_iff F.Carrier F.card_eq ⟨g,hg⟩ σ (c.borelMap b)).mpr
  change Units.map σ.toMonoidHom (c.coefficient b) = c.coefficient b
  rw [hbu]
  exact oddInclusion_fixed_of_two_power F σ hσ u

/-- Every odd-subfield coefficient has a simultaneous original normalizer lift. -/
theorem odd_coefficient_lifts (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    (u : (oddField F).Carrierˣ) :
    ∃ b : c.localBorel, (b.val : G) ∈ normalizer (T : Set G) ∧
      c.coefficient b = Units.map (oddInclusion F).toMonoidHom u := by
  obtain ⟨b,hb⟩ := c.coefficient_surjective hTI (Units.map (oddInclusion F).toMonoidHom u)
  exact ⟨b,c.normalizes_of_odd_coefficient hTI b u hb,hb⟩

/-- Conjugation by a normalizer of the component Sylow intersection preserves
its intrinsic Borel. -/
def localActor (x : normalizer (I : Set G))
    (hx : (x : G) ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G)) :
    MulAut c.localBorel := by
  let α := I.normalizerMonoidHom x
  have hs : ((T : Subgroup G).subgroupOf I).map α.toMonoidHom =
      (T : Subgroup G).subgroupOf I := by
    ext i
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact ((mem_normalizer_iff.mp hx j).mp ⟨hj,j.property⟩).1
    · intro hi
      refine ⟨α.symm i,?_,α.apply_symm_apply i⟩
      exact ((mem_normalizer_iff.mp ((normalizer _).inv_mem hx) i).mp
        ⟨hi,i.property⟩).1
  have hb : c.localBorel.map α.toMonoidHom = c.localBorel := by
    change (normalizer ((T : Subgroup G).subgroupOf I : Set I)).map α.toMonoidHom = _
    rw [map_equiv_normalizer_eq,hs]
    rfl
  exact (α.subgroupMap c.localBorel).trans (MulEquiv.subgroupCongr hb)

omit [Finite G] in
theorem localActor_apply (x : normalizer (I : Set G))
    (hx : (x : G) ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G))
    (b : c.localBorel) :
    (c.localActor x hx b).val = I.normalizerMonoidHom x b.val := rfl

omit [Finite G] in
theorem coefficient_action (x : normalizer (I : Set G))
    (hx : (x : G) ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G))
    (g : OddBorel.borel F.Carrier) (σ : F.Carrier ≃+* F.Carrier)
    (he : c.actor x = MulAut.conj (g : PSL(2,F.Carrier)) * fieldEquivPSL 2 σ)
    (b : c.localBorel) :
    c.coefficient (c.localActor x hx b) = Units.map σ.toMonoidHom (c.coefficient b) := by
  have hh : c.borelMap (c.localActor x hx b) =
      Semilinear.borelActor F.Carrier g σ (c.borelMap b) := by
    apply Subtype.ext
    change c.quotient (c.localActor x hx b).val = _
    rw [c.localActor_apply,← c.actor_quotient,he]
    rfl
  change torusProjection F.Carrier (c.borelMap (c.localActor x hx b)) = _
  rw [hh,torusProjection_borelActor]
  rfl

variable {L V : Subgroup G} {D : ChosenModule T L V} {E : Geometry D}

include c in
/-- The odd subfield detects the original coprime mover on the actual Borel.
All normalizer lifts are constructed, and the inner Borel factor is retained. -/
theorem borel_movement
    (hTI : (T : Subgroup G) ≤ normalizer (I : Set G)) (hIY : I ≤ E.Y)
    (x : normalizer (I : Set G)) (hxX : (x : G) ∈ E.X)
    (hxS : (x : G) ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G))
    (ho : Odd (Nat.card E.X)) (hc : Nat.Coprime (Nat.card E.X) (Nat.card I))
    (hne : coreQuotientAction I x ≠ 1) : E.BorelMovement := by
  have hα : c.actor x ≠ 1 := by
    intro h
    exact hne ((MulAut.congr c.model).injective (h.trans (map_one _).symm))
  have hd : orderOf (c.actor x) ∣ Nat.card E.X := by
    apply ((orderOf_map_dvd (MulAut.congr c.model).toMonoidHom _).trans
      (orderOf_map_dvd (coreQuotientAction I) x)).trans
    rw [← Subgroup.orderOf_coe x]
    exact E.X.orderOf_dvd_natCard hxX
  have hcop : Nat.Coprime (orderOf (c.actor x)) (Nat.card PSL(2,F.Carrier)) :=
    hc.of_dvd hd (card_dvd_of_surjective c.quotient c.quotient_surjective)
  obtain ⟨g,σ,hσ,hdσ,he⟩ := exists_borel_inner_field_of_coprime F.Carrier
    (c.actor x) hα hcop (c.actor_preserves_root x hxS)
  have hσodd : Odd (orderOf σ) := ho.of_dvd_nat (hdσ.trans hd)
  have hne' := oddRestriction_ne_one F σ hσodd hσ
  have hunits : Odd (Nat.card F.Carrierˣ) := by
    rw [Nat.card_units,F.card_eq]
    exact Nat.Even.sub_odd (pow_pos (by decide : 0 < (2 : ℕ)) _)
      (even_two.pow_of_ne_zero F.degree_pos.ne') odd_one
  by_contra hmove
  apply hne'
  have hfix (u : (oddField F).Carrierˣ) :
      Units.map (oddRestriction F σ).toMonoidHom u = u := by
    obtain ⟨b,hbN,hbu⟩ := c.odd_coefficient_lifts hTI u
    obtain ⟨r,hr,hro,hre⟩ := c.coefficient.exists_odd_power_with_image b
      (hunits.of_dvd_nat (orderOf_dvd_natCard _))
    have hrN : (r.val : G) ∈ normalizer (T : Set G) := by
      obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hr
      exact (normalizer (T : Set G)).zpow_mem hbN n
    let B : Subgroup G := zpowers (r.val : G)
    have hBY : B ≤ E.Y := zpowers_le.mpr (hIY r.val.property)
    have hBN : B ≤ normalizer (T : Set G) := zpowers_le.mpr hrN
    have hBo : Odd (Nat.card B) := by
      rw [Nat.card_zpowers,Subgroup.orderOf_coe r.val,Subgroup.orderOf_coe r]
      exact hro
    have hcomm : ⁅E.X,B⁆ ≤ (T : Subgroup G) := by
      by_contra hn
      exact hmove ⟨B,hBY,hBN,hBo,hn⟩
    let d : c.localBorel := c.localActor x hxS r * r⁻¹
    have hdT : (d.val : G) ∈ (T : Subgroup G) :=
      hcomm (commutator_mem_commutator hxX (mem_zpowers (r.val : G)))
    obtain ⟨k,hk⟩ := T.isPGroup'.exists_pow_pow_eq_one ⟨d.val,hdT⟩
    have hdp : d ^ (2 ^ k) = 1 :=
      Subtype.ext (Subtype.ext (congrArg (fun t : T => (t : G)) hk))
    have hcd : c.coefficient d =
        Units.map σ.toMonoidHom (Units.map (oddInclusion F).toMonoidHom u) *
          (Units.map (oddInclusion F).toMonoidHom u)⁻¹ := by
      rw [map_mul,map_inv,c.coefficient_action x hxS g σ he,hre,hbu]
    have hpow : c.coefficient d ^ (2 ^ k) = 1 := by
      rw [← map_pow,hdp,map_one]
    have hz : c.coefficient d = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hunits.coprime_two_left.pow_left k)
        (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_natCard _))
    rw [hcd,mul_inv_eq_one] at hz
    apply Units.ext
    apply (oddInclusion F).injective
    change oddInclusion F (oddRestriction F σ u.val) = oddInclusion F u.val
    rw [oddRestriction_apply]
    exact congrArg Units.val hz
  ext z
  by_cases hz : z = 0
  · simp [hz]
  · exact congrArg Units.val (hfix (Units.mk0 z hz))
end Coordinates

/-- Sylow conjugacy constructs aligned coordinates from any supplied quotient marking. -/
theorem exists_coordinates (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    (F : BinaryField) (e : (I ⧸ pCore 2 I) ≃* PSL(2,F.Carrier)) :
    Nonempty (Coordinates T I F) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T I hTI
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let S := P.mapSurjective hq
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(2,F.Carrier) S (standardSylow F.Carrier)
  let e' := e.trans (MulAut.conj g)
  refine ⟨⟨e',?_⟩⟩
  have hh := congrArg Sylow.toSubgroup hg
  rw [Sylow.coe_subgroup_smul,coe_standardSylow] at hh
  change ((P : Subgroup I).map q).map (MulAut.conj g).toMonoidHom = _ at hh
  have heq : e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I)) =
      (MulAut.conj g).toMonoidHom.comp q := rfl
  rw [heq,← map_map,← hP]
  exact hh
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear.RankOne
