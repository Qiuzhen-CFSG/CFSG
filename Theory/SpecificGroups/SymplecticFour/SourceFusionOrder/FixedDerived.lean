module
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.FixedFlag
public import Theory.FieldTheory.ScalarTwistedFixedPoints
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Lattice

/-!
# A root in the derived subgroup of an outer involution's fixed Sylow

For a fixed field parameter t outside {0,1}, two simple-root commutators
multiply to the nonidentity long-root element with parameter t²+t. The
fixed-field order theorem supplies t whenever the original field has more
than four elements. Descent inside the original Borel carries this witness
to the fixed Sylow of any outer flag involution, preserving the marked root.

The binary fixed-field exception is deliberately excluded by n>2. The
Chapter 6 application contradicts the original ambient root-disjointness
obstruction, without replacing the full centralizer by its native image.

Source: Aschbacher--Smith F.4.37, printed p.293 of refs/quasithin.pdf,
the nonexceptional symplectic case of the center-derived argument.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
open CentralRootGeometry DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem field_element (σ : F ≃+* F) (b u w v : F) :
    fieldAutomorphism σ (element b u w v).val =
      (element (σ b) (σ u) (σ w) (σ v)).val := by
  apply Subtype.ext
  change (element b u w v).val.val.map σ = _
  rw [element_matrix,element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks]

omit [Finite F] in
private theorem simple_commutator (b v : F) :
    ⁅element b 0 0 0,element 0 0 0 v⁆ = theta (b^2*v) (b*v) := by
  have hi (c : F) : (element c 0 0 0)⁻¹=element c 0 0 0 := by
    apply inv_eq_of_mul_eq_one_left
    rw [element_mul]
    simpa [CharTwo.add_self_eq_zero] using (element_zero (F := F))
  have hj (c : F) : (element 0 0 0 c)⁻¹=element 0 0 0 c := by
    apply inv_eq_of_mul_eq_one_left
    rw [element_mul]
    simpa [CharTwo.add_self_eq_zero] using (element_zero (F := F))
  rw [commutatorElement_def,hi,hj,element_mul,element_mul,element_mul]
  apply (element_eq_iff _ _ _ _ _ _ _ _).mpr
  simp only [zero_add,add_zero,mul_zero,zero_mul,CharTwo.add_self_eq_zero,true_and]
  constructor
  · ring
  · exact ⟨mul_comm _ _,True.intro⟩

omit [CharP F 2] in
private theorem fixed_parameter (hF : 4 < Nat.card F)
    (σ : F ≃+* F) (ho : orderOf σ=2) :
    ∃ t : F, σ t=t ∧ t≠0 ∧ t≠1 := by
  classical
  have hs : Function.Involutive σ := by
    intro x
    have hh : σ^2=1 := by simpa only [ho] using pow_orderOf_eq_one σ
    exact congrArg (fun a : F ≃+* F => a x) hh
  have hn : σ≠RingEquiv.refl F := by
    intro hh
    have hh' : σ=1 := hh
    rw [hh',orderOf_one] at ho
    omega
  have hc := FiniteField.card_involution_fixed_sq σ hs hn
  have hb : 2 < Nat.card (FixedBy.subfield F σ) := by nlinarith
  by_contra! hh
  let f : FixedBy.subfield F σ → Bool := fun x => if x.val=0 then false else true
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : x.val=0 <;> by_cases hy : y.val=0
    · exact Subtype.ext (hx.trans hy.symm)
    · change (if x.val=0 then false else true)=(if y.val=0 then false else true) at hxy
      rw [if_pos hx,if_neg hy] at hxy
      cases hxy
    · change (if x.val=0 then false else true)=(if y.val=0 then false else true) at hxy
      rw [if_neg hx,if_pos hy] at hxy
      cases hxy
    · exact Subtype.ext ((hh x.val x.property hx).trans (hh y.val y.property hy).symm)
  have hb' := Nat.card_le_card_of_injective f hf
  have hcB : Nat.card Bool=2 := by simp [Nat.card_eq_fintype_card]
  rw [hcB] at hb'
  omega

omit [Finite F] in
private theorem field_fixed_derived_root (σ : F ≃+* F)
    (t : F) (ht : σ t=t) :
    let P := unipotent ⊓ (fieldAutomorphism σ).fixedSubgroup
    (theta (t^2+t) 0).val ∈ (_root_.commutator P).map P.subtype := by
  let P := unipotent ⊓ (fieldAutomorphism σ).fixedSubgroup
  have hb (b : F) (h : σ b=b) : (element b 0 0 0).val ∈ P := by
    refine ⟨(element b 0 0 0).property,?_⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [field_element,h,map_zero]
  have hv (v : F) (h : σ v=v) : (element 0 0 0 v).val ∈ P := by
    refine ⟨(element 0 0 0 v).property,?_⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [field_element,h,map_zero]
  have hm (b v : F) (hb' : σ b=b) (hv' : σ v=v) :
      (theta (b^2*v) (b*v)).val ∈ (_root_.commutator P).map P.subtype := by
    let x : P := ⟨(element b 0 0 0).val,hb b hb'⟩
    let y : P := ⟨(element 0 0 0 v).val,hv v hv'⟩
    have hxy : ⁅x,y⁆ ∈ _root_.commutator P :=
      commutator_mem_commutator (mem_top x) (mem_top y)
    have hm := mem_map_of_mem P.subtype hxy
    change (⁅element b 0 0 0,element 0 0 0 v⁆).val ∈ _ at hm
    rw [simple_commutator] at hm
    exact hm
  have h1 := hm t 1 ht (map_one σ)
  have h2 := hm 1 t (map_one σ) ht
  have hh := ((_root_.commutator P).map P.subtype).mul_mem h1 h2
  change (theta (t^2*1) (t*1) * theta (1^2*t) (1*t)).val ∈ _ at hh
  rw [theta_add] at hh
  simpa only [mul_one,one_pow,one_mul,CharTwo.add_self_eq_zero] using hh

/-- Above field order four, the fixed inner Sylow of every outer flag
involution has a nonidentity derived element in the marked long root. -/
theorem outer_fixed_derived_meets_root {n : ℕ} (hF : Nat.card F=2^n) (hn : 2<n)
    (a : MulAut (Sp F)) (hao : orderOf a=2)
    (ha : a ∈ SourceNormalizerExtension.flagAutomorphisms F)
    (hi : a ∉ MulAut.innerSubgroup (Sp F)) :
    let P := unipotent ⊓ a.fixedSubgroup
    ∃ z : Sp F, z≠1 ∧ z ∈ (_root_.commutator P).map P.subtype ∧
      z ∈ (center (pointLocal (F := F))).map pointLocal.subtype := by
  obtain ⟨σ,hσ,c,hc⟩ := outer_flag_involution_normal_form hF (by omega) a hao ha hi
  have hlarge : 4 < Nat.card F := by
    rw [hF]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) hn
  obtain ⟨t,ht,ht0,ht1⟩ := fixed_parameter hlarge σ hσ
  have hparam : t^2+t≠0 := by
    intro hh
    have hh' : t*(t+1)=0 := by linear_combination hh
    have hh'' := (mul_eq_zero.mp hh').resolve_left ht0
    exact ht1 (CharTwo.add_eq_zero.mp hh'')
  let r := (theta (t^2+t) 0).val
  have hr1 : r≠1 := by
    intro hh
    have he : theta (t^2+t) 0=1 := Subtype.ext hh
    rw [theta,←element_zero,element_eq_iff] at he
    exact hparam he.2.1
  let P₀ := unipotent ⊓ (fieldAutomorphism σ).fixedSubgroup
  let P := unipotent ⊓ a.fixedSubgroup
  have hcN : c.val ∈ normalizer (unipotent (F := F) : Set (Sp F)) := by
    rw [←borel_eq_normalizer_unipotent]
    exact c.property
  have hmap (x : P₀) : c.val*x.val*c.val⁻¹ ∈ P := by
    refine ⟨(hcN x.val).mp x.property.1,?_⟩
    apply (MulAut.mem_fixedSubgroup a _).mpr
    have hx := (MulAut.mem_fixedSubgroup _ _).mp x.property.2
    rw [hc]
    rw [show (MulAut.conj c.val)⁻¹=MulAut.conj (c.val⁻¹) from (map_inv MulAut.conj c.val).symm]
    simp only [MulAut.mul_apply,MulAut.conj_apply,inv_inv]
    simp only [mul_assoc,inv_mul_cancel,mul_one,inv_mul_cancel_left,hx]
  let j : P₀ →* P := ((MulAut.conj c.val).toMonoidHom.comp P₀.subtype).codRestrict P hmap
  have hderived : (_root_.commutator P₀).map j ≤ _root_.commutator P := by
    rw [map_commutator_eq,_root_.commutator_def]
    exact commutator_mono le_top le_top
  obtain ⟨v,hv,hvr⟩ := field_fixed_derived_root σ t ht
  change v.val=r at hvr
  have hrD : c.val*r*c.val⁻¹ ∈ (_root_.commutator P).map P.subtype := by
    have hh := mem_map_of_mem P.subtype (hderived (mem_map_of_mem j hv))
    change c.val*v.val*c.val⁻¹ ∈ _ at hh
    rwa [hvr] at hh
  have hrZ : r ∈ RootSubgroup.group (F := F) 0 := by
    change (theta (t^2+t) 0).val ∈ _
    rw [theta_val,RootSubgroup.element_zero,mul_one]
    exact (RootSubgroup.mem_group_iff _ _).mpr ⟨_,rfl⟩
  have hcR : c.val ∈ normalizer (RootSubgroup.group (F := F) 0 : Set (Sp F)) := by
    rw [RootNormalizerResidual.normalizer_zero_eq]
    exact c.property.1
  refine ⟨c.val*r*c.val⁻¹,?_,hrD,?_⟩
  · intro hh
    apply hr1
    have hh' : MulAut.conj c.val r=MulAut.conj c.val 1 := by simpa using hh
    exact (MulAut.conj c.val).injective hh'
  · rw [PointRadicalAction.center_eq_root hF (by omega)]
    exact (hcR r).mp hrZ

end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
