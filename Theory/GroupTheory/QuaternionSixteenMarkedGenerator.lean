module
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

/-!
# A generator compatible with a marked quaternion-sixteen extension

For an actual Q₈ subgroup C and an outside order-four element r generating
Q₁₆ with C, choose an order-eight generator a of the cyclic maximal subgroup.
The index-two membership formula places a² and ar in C. The sixteen-element
model then proves r a=a⁻¹ r and lists C as the eight quaternion words.
Thus an unmarked model identification suffices while retaining the actual r,C.

Source: the marked complement in Aschbacher, *Sporadic Groups* (1994),
45.8 and 45.11, pp.245–248.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

@[expose] def quaternionMarkedWord (a r z : G) (k : Fin 8) : G :=
  ![1,z,a^2,z*a^2,a*r,z*(a*r),a^2*(a*r),z*(a^2*(a*r))] k

theorem map_quaternionMarkedWord {H : Type*} [Group H] (f : G →* H) (a r z : G) (k : Fin 8) :
    f (quaternionMarkedWord a r z k)=quaternionMarkedWord (f a) (f r) (f z) k := by
  fin_cases k <;> simp [quaternionMarkedWord]

/-- An arbitrary Q₁₆ identification can be made compatible with the actual
outside order-four element and the actual Q₈ subgroup. -/
theorem exists_marked_quaternion_generator (C : Subgroup G)
    (eC : C ≃* QuaternionGroup 2) (z r : G) (hzC : z∈C) (hz : orderOf z=2)
    (hr2 : r^2=z) (E : (C⊔zpowers r : Subgroup G) ≃* QuaternionGroup 4) :
    ∃ a : G, a∈C⊔zpowers r ∧ a^4=z ∧ r*a=a⁻¹*r ∧
      (∀ k : Fin 8, quaternionMarkedWord a r z k ∈ C) ∧
      (∀ x∈C, ∃ k : Fin 8, x=quaternionMarkedWord a r z k) := by
  let S := C⊔zpowers r
  let zS : S := ⟨z,mem_sup_left hzC⟩
  let rS : S := ⟨r,mem_sup_right (mem_zpowers r)⟩
  let A : S := E.symm (QuaternionGroup.a 1)
  have hCcard : Nat.card C=8 := by
    rw [Nat.card_congr eC.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
  have hScard : Nat.card S=16 := by
    rw [Nat.card_congr E.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
  have hzE : E zS=QuaternionGroup.a 4 := by
    have hn : E zS≠1 := by
      intro he
      have he' : z=1 := congrArg Subtype.val (E.injective (he.trans E.map_one.symm))
      simp [he'] at hz
    have hs : (E zS)^2=1 := by
      rw [←map_pow]
      have hz2 : zS^2=1 := Subtype.ext (hz ▸ pow_orderOf_eq_one z)
      rw [hz2,map_one]
    exact (by decide +kernel : ∀ x : QuaternionGroup 4, x≠1 → x^2=1 → x=QuaternionGroup.a 4) _ hn hs
  have hA4 : A^4=zS := by
    apply E.injective
    rw [map_pow,hzE]
    change (E (E.symm (QuaternionGroup.a 1)))^4=QuaternionGroup.a 4
    rw [MulEquiv.apply_symm_apply]
    decide +kernel
  have hrout : r∉C := by
    intro hr
    have hs : S=C := sup_eq_left.mpr (zpowers_le.mpr hr)
    rw [hs,hCcard] at hScard
    omega
  let C' := C.subgroupOf S
  have hi : C'.index=2 := by
    have hh := C'.card_mul_index
    have hhC : Nat.card C'=8 :=
      (Nat.card_congr (subgroupOfEquivOfLe (H:=C) (K:=S) le_sup_left).toEquiv).trans hCcard
    rw [hhC,hScard] at hh
    omega
  have hA2 : A^2∈C' := C'.sq_mem_of_index_two hi A
  have hAout : A∉C' := by
    intro ha
    have hfour : (A:G)^4=1 := by
      have hh : (eC ⟨A,ha⟩)^4=1 := (by decide +kernel : ∀ x : QuaternionGroup 2,x^4=1) _
      have he : (⟨(A:G),ha⟩:C)^4=1 := eC.injective (by simpa only [map_pow,map_one] using hh)
      exact congrArg Subtype.val he
    have he : z=1 := (congrArg Subtype.val hA4).symm.trans hfour
    simp [he] at hz
  have har : A*rS∈C' := (C'.mul_mem_iff_of_index_two hi).mpr (iff_of_false hAout hrout)
  have hrE2 : (E rS)^2=QuaternionGroup.a 4 := by
    rw [←map_pow,show rS^2=zS from Subtype.ext hr2,hzE]
  have hrEne2 : E rS≠QuaternionGroup.a 2 := by
    intro he
    have hh : rS=A^2 := E.injective (by rw [he,map_pow]; change QuaternionGroup.a 2=(E (E.symm (QuaternionGroup.a 1)))^2; rw [MulEquiv.apply_symm_apply]; decide +kernel)
    exact hrout (show rS∈C' from hh ▸ hA2)
  have hrEne6 : E rS≠QuaternionGroup.a 6 := by
    intro he
    have hh : rS=(A^2)^3 := E.injective (by rw [he,map_pow,map_pow]; change QuaternionGroup.a 6=((E (E.symm (QuaternionGroup.a 1)))^2)^3; rw [MulEquiv.apply_symm_apply]; decide +kernel)
    exact hrout (show rS∈C' from hh ▸ C'.pow_mem hA2 3)
  have hreverse : rS*A=A⁻¹*rS := by
    apply E.injective
    simp only [map_mul,map_inv]
    change E rS*E (E.symm (QuaternionGroup.a 1))=(E (E.symm (QuaternionGroup.a 1)))⁻¹*E rS
    rw [MulEquiv.apply_symm_apply]
    exact (by decide +kernel : ∀ R : QuaternionGroup 4, R^2=QuaternionGroup.a 4 →
      R≠QuaternionGroup.a 2 → R≠QuaternionGroup.a 6 →
      R*QuaternionGroup.a 1=(QuaternionGroup.a 1)⁻¹*R) _ hrE2 hrEne2 hrEne6
  have hmem (k : Fin 8) : quaternionMarkedWord (A:G) r z k∈C := by
    fin_cases k <;> simp only [quaternionMarkedWord]
    · exact C.one_mem
    · exact hzC
    · exact hA2
    · exact C.mul_mem hzC hA2
    · exact har
    · exact C.mul_mem hzC har
    · exact C.mul_mem hA2 har
    · exact C.mul_mem hzC (C.mul_mem hA2 har)
  refine ⟨A,A.property,congrArg Subtype.val hA4,congrArg Subtype.val hreverse,hmem,?_⟩
  intro x hx
  let xS : S := ⟨x,mem_sup_left hx⟩
  have words : ∀ R X : QuaternionGroup 4, R^2=QuaternionGroup.a 4 →
      R≠QuaternionGroup.a 2 → R≠QuaternionGroup.a 6 →
      ∃ k : Fin 8, X=quaternionMarkedWord (QuaternionGroup.a 1) R (QuaternionGroup.a 4) k ∨
        X=quaternionMarkedWord (QuaternionGroup.a 1) R (QuaternionGroup.a 4) k*R := by decide +kernel
  obtain ⟨k,hk|hk⟩ := words (E rS) (E xS) hrE2 hrEne2 hrEne6
  · refine ⟨k,?_⟩
    have he : xS=quaternionMarkedWord A rS zS k := by
      apply E.injective
      change E.toMonoidHom xS = E.toMonoidHom (quaternionMarkedWord A rS zS k)
      rw [map_quaternionMarkedWord]
      change E xS=quaternionMarkedWord (E A) (E rS) (E zS) k
      rw [show E A=QuaternionGroup.a 1 from E.apply_symm_apply _,hzE]
      exact hk
    have hh := congrArg S.subtype he
    rw [map_quaternionMarkedWord] at hh
    exact hh
  · have he : xS=quaternionMarkedWord A rS zS k*rS := by
      apply E.injective
      rw [map_mul]
      change E.toMonoidHom xS = E.toMonoidHom (quaternionMarkedWord A rS zS k)*E rS
      rw [map_quaternionMarkedWord]
      change E xS=quaternionMarkedWord (E A) (E rS) (E zS) k*E rS
      rw [show E A=QuaternionGroup.a 1 from E.apply_symm_apply _,hzE]
      exact hk
    have hx' : x=quaternionMarkedWord (A:G) r z k*r := by
      have hh := congrArg S.subtype he
      rw [map_mul,map_quaternionMarkedWord] at hh
      exact hh
    exact False.elim (hrout ((C.mul_mem_cancel_left (hmem k)).mp (hx' ▸ hx)))
end Subgroup
