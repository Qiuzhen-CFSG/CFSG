module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.CosetRadical
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ThreeCentersQuotient
import Mathlib.Tactic.LinearCombination

/-!
# The central radical reduction for the three-center subgroup

A radical element fixing two nonorthogonal vectors in e₀-perpendicular
has zero middle coordinates. Thus the common radical centralizer of a
noncommuting transvection pair is the central root. Odd-product fusion
propagates centralization of the first root to the second inside the
literal generated group.

Applied to the original three-center configuration, the radical witness
construction shows that absence of the required coset product forces its
entire radical intersection into the center of pointLocal. This is the
central-kernel reduction in Aschbacher--Smith G.4.9, printed p.341. The
subsequent Dickson and Sylow lifting argument is separate.
-/

public noncomputable section
open Subgroup Module
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open InvolutionTypes InvolutionCentralizers
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private theorem center_lower_zero (a : pointLocal (F:=F)) (u : Vector F) (c : F)
    (hu : u≠0) (hc : c≠0)
    (ha : ∀ v, a.val • v=v+(c*form F u v) • u) : u (.inr 0)=0 := by
  have hf := (mem_pointLocal_iff_fixed a.val).mp a.property
  rw [ha] at hf
  have hs : (c*form F u (e 0)) • u=0 :=
    add_left_cancel (hf.trans (add_zero _).symm)
  have hz := (mul_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hu)).resolve_left hc
  simpa only [form_e_right,neg_eq_zero] using hz

omit [CharP F 2] in
private theorem pairing_ne_zero_of_noncommuting (a b : Sp F) (u v : Vector F) (c d : F)
    (ha : ∀ x, a • x=x+(c*form F u x) • u)
    (hb : ∀ x, b • x=x+(d*form F v x) • v)
    (hnc : ¬Commute a b) : form F u v≠0 := by
  intro huv
  have hvu : form F v u=0 := TwoLocalCover.form_alternating.isRefl _ _ huv
  apply hnc
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Vector F)
  intro x
  change (a*b) • x=(b*a) • x
  rw [mul_smul,mul_smul,ha,hb,hb,ha]
  simp only [map_add,map_smul,smul_eq_mul,huv,hvu,mul_zero,add_zero]
  abel

/-- Two nonorthogonal fixed vectors in e₀-perpendicular force a radical
element to lie in its central root coordinate. -/
theorem pointRadical_central_of_fixed_pair (q : pointLocal (F:=F))
    (hq : q∈pointRadical) (u v : Vector F)
    (hu : u (.inr 0)=0) (hv : v (.inr 0)=0) (huv : form F u v≠0)
    (hqu : q.val • u=u) (hqv : q.val • v=v) :
    q∈center (pointLocal (F:=F)) := by
  have he := pointRadical_eq_element q hq
  rw [he] at hqu hqv ⊢
  apply (pointRadicalElement_mem_center_iff _ _ _).mpr
  have hdet : u (.inl 1)*v (.inr 1)-u (.inr 1)*v (.inl 1)≠0 := by
    simpa only [form_apply,Fin.sum_univ_two,hu,hv,mul_zero,zero_mul,sub_self,zero_add] using huv
  have h1 := congrFun hqu (.inl 0)
  have h2 := congrFun hqv (.inl 0)
  simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec,
    dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,hu,hv] at h1 h2
  constructor
  · apply (mul_eq_zero.mp (show
      (u (.inl 1)*v (.inr 1)-u (.inr 1)*v (.inl 1))*q.val.val (.inl 1) (.inr 0)=0 from ?_)).resolve_left hdet
    linear_combination u (.inl 1)*h2-v (.inl 1)*h1
  · apply (mul_eq_zero.mp (show
      (u (.inl 1)*v (.inr 1)-u (.inr 1)*v (.inl 1))*q.val.val (.inr 1) (.inr 0)=0 from ?_)).resolve_left hdet
    linear_combination v (.inr 1)*h1-u (.inr 1)*h2

/-- The common centralizer in the actual point radical of a noncommuting
transvection pair is contained in the central root. -/
theorem pointRadical_central_of_commuting_noncommuting_pair
    (a b q : pointLocal (F:=F)) (ha : IsB1 a.val) (hb : IsB1 b.val)
    (hab : ¬Commute a b) (hq : q∈pointRadical)
    (hqa : Commute q a) (hqb : Commute q b) : q∈center (pointLocal (F:=F)) := by
  obtain ⟨u,c,hu,hc,haform⟩ := rank_one_formula a.val ha
  obtain ⟨v,d,hv,hd,hbform⟩ := rank_one_formula b.val hb
  apply pointRadical_central_of_fixed_pair q hq u v
    (center_lower_zero a u c hu hc haform) (center_lower_zero b v d hv hd hbform)
  · apply pairing_ne_zero_of_noncommuting a.val b.val u v c d haform hbform
    intro he
    exact hab (Subtype.ext he.eq)
  · exact fixes_center_of_commute a.val q.val u c hu hc haform (hqa.map pointLocal.subtype)
  · exact fixes_center_of_commute b.val q.val v d hv hd hbform (hqb.map pointLocal.subtype)

/-- Normality of the radical and odd-product fusion propagate centralization
of the first root to the second, hence to the full point-local group. -/
theorem pointRadical_inter_central_of_first_centralizes [Finite F]
    (L : Subgroup (pointLocal (F:=F))) (a b : pointLocal (F:=F))
    (haL : a∈L) (hbL : b∈L) (ha : IsB1 a.val) (hb : IsB1 b.val)
    (hab : ¬Commute a b)
    (hcentral : ∀ q∈L, q∈pointRadical → Commute q a) :
    L⊓pointRadical≤center (pointLocal (F:=F)) := by
  let aL : L := ⟨a,haL⟩
  let bL : L := ⟨b,hbL⟩
  have ha2 : aL^2=1 := Subtype.ext (Subtype.ext (by
    change a.val^2=1
    simpa only [ha.1] using pow_orderOf_eq_one a.val))
  have hb2 : bL^2=1 := Subtype.ext (Subtype.ext (by
    change b.val^2=1
    simpa only [hb.1] using pow_orderOf_eq_one b.val))
  have ho : Odd (orderOf (aL*bL)) := by
    rw [←orderOf_injective L.subtype L.subtype_injective,
      ←orderOf_injective pointLocal.subtype pointLocal.subtype_injective]
    exact odd_order_product_of_isB1 a.val b.val ha hb (fun h => hab (Subtype.ext h.eq))
  obtain ⟨k,hk⟩ := isConj_iff.mp (isConj_of_involutions_odd_product aL bL ha2 hb2 ho)
  have hkb : k.val*a*k.val⁻¹=b := congrArg Subtype.val hk
  intro q hq
  have hqconj : k.val⁻¹*q*k.val∈L := L.mul_mem
    (L.mul_mem (L.inv_mem k.property) hq.1) k.property
  have hqrad : k.val⁻¹*q*k.val∈pointRadical := by
    simpa only [inv_inv] using pointRadical_normal.conj_mem q hq.2 k.val⁻¹
  have hc := (hcentral _ hqconj hqrad).map (MulAut.conj k.val).toMonoidHom
  have hqb : Commute q b := by
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_assoc,
      mul_inv_cancel_left,inv_mul_cancel_left,←mul_assoc,hkb,mul_inv_cancel,one_mul,mul_one,mul_inv_cancel_right] using hc
  exact pointRadical_central_of_commuting_noncommuting_pair a b q ha hb hab hq.2
    (hcentral q hq.1 hq.2) hqb

namespace ThreeCenterConfiguration
variable {X : Subgroup (Sp F)} {a : Sp F}

omit [CharP F 2] in
/-- The local generated group retains the actual original three-generator subgroup. -/
theorem localGenerated_map_le (D : ThreeCenterConfiguration X a) :
    D.localGenerated.map pointLocal.subtype≤
      (closure {a,(D.x : Sp F)*a*(D.x : Sp F)⁻¹,
        (D.y : Sp F)*a*(D.y : Sp F)⁻¹}).map (MulAut.conj D.frame).toMonoidHom := by
  rw [map_le_iff_le_comap]
  rw [localGenerated,closure_le]
  intro t ht
  rcases ht with rfl | rfl | rfl
  · exact ⟨a,subset_closure (by simp),rfl⟩
  · exact ⟨(D.x : Sp F)*a*(D.x : Sp F)⁻¹,subset_closure (by simp),rfl⟩
  · exact ⟨(D.y : Sp F)*a*(D.y : Sp F)⁻¹,subset_closure (by simp),rfl⟩

/-- Failure of the original coset witness forces the entire local radical
intersection into the one-dimensional central root subgroup. -/
theorem radicalIntersection_central_of_no_coset_witness [Finite F]
    (D : ThreeCenterConfiguration X a) (ha : IsB1 a)
    (han : a∈normalizer (X : Set (Sp F)))
    (hno : ¬∃ b : Sp F, IsB1 b ∧ a⁻¹*b∈X ∧ Commute a b ∧ a*b∈X ∧ IsC2 (a*b)) :
    D.localGenerated⊓pointRadical≤Subgroup.center (pointLocal (F:=F)) := by
  apply pointRadical_inter_central_of_first_centralizes D.localGenerated
    D.firstLocal D.secondLocal (subset_closure (by simp)) (subset_closure (by simp))
    (D.firstLocal_isB1 ha) (D.secondLocal_isB1 ha) D.firstLocal_secondLocal_noncommute
  intro q hq hqR
  by_contra hncomm
  obtain ⟨r,hr,he⟩ := D.localGenerated_map_le ⟨q,hq,rfl⟩
  have hrad : (⟨D.frame*r*D.frame⁻¹,D.local_containment ⟨r,hr,rfl⟩⟩ :
      pointLocal (F:=F))∈pointRadical := by
    have hqeq : (⟨D.frame*r*D.frame⁻¹,D.local_containment ⟨r,hr,rfl⟩⟩ :
      pointLocal (F:=F))=q := Subtype.ext he
    rwa [hqeq]
  have hnc : ¬Commute r a := by
    intro hcomm
    apply hncomm
    apply Subtype.ext
    have h := hcomm.map (MulAut.conj D.frame).toMonoidHom
    change q.val*D.firstLocal.val=D.firstLocal.val*q.val
    change (MulAut.conj D.frame).toMonoidHom r * (MulAut.conj D.frame).toMonoidHom a =
      (MulAut.conj D.frame).toMonoidHom a * (MulAut.conj D.frame).toMonoidHom r at h
    rw [he] at h
    exact h
  exact hno (D.exists_isC2_of_radical ha han r hr hrad hnc)

end ThreeCenterConfiguration

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
