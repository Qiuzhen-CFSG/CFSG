module
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PGroup.CriticalSubgroup
public import Mathlib.GroupTheory.IndexNormal

/-!
# An involution moved across a subgroup of index two

Let D have index two in P and let v be a central involution of D.
If t in P moves v, the same t exchanges v and its distinct conjugate w.
Both lie in the center of D, and their product is a nonidentity central
involution of P. Normality preserves the center of D; the two cosets
then show that all of P fixes the product.

This is the elementary ambient Sylow calculation used in the analysis of
Aschbacher--Smith 12.6.12, printed pp.825--826. The actual conjugator and
ambient center embeddings are retained.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A moved central involution and its conjugate have nonidentity central product. -/
theorem central_involution_pair_of_relIndex_two
    (D P : Subgroup G) (hDP : D ≤ P) (hi : D.relIndex P = 2)
    (v : G) (hv : v ∈ (center D).map D.subtype) (hv2 : v ^ 2 = 1)
    (t : G) (ht : t ∈ P) (hmove : (MulAut.conj t) v ≠ v) :
    let w := (MulAut.conj t) v
    w ∈ (center D).map D.subtype ∧ w ≠ v ∧ (MulAut.conj t) w = v ∧
      v * w ∈ (center P).map P.subtype ∧ v * w ≠ 1 ∧
      (v * w) ^ 2 = 1 ∧ v * w ≠ v := by
  let Z := (center D).map D.subtype
  let w := (MulAut.conj t) v
  have hDn : P ≤ normalizer (D : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hDP).mp (normal_of_index_eq_two hi)
  have hZn : P ≤ normalizer (Z : Set G) :=
    hDn.trans (normalizer_le_normalizer_characteristic_image D (center D))
  have hw : w ∈ (center D).map D.subtype := (mem_normalizer_iff.mp (hZn ht) v).mp hv
  have hvD := (map_center_subtype_eq_inf_centralizer D ▸ hv).1
  have hvC := (map_center_subtype_eq_inf_centralizer D ▸ hv).2
  have hwD := (map_center_subtype_eq_inf_centralizer D ▸ hw).1
  have hwC := (map_center_subtype_eq_inf_centralizer D ▸ hw).2
  have htD : t ∉ D := by
    intro hh
    apply hmove
    exact mul_inv_eq_iff_eq_mul.mpr (hvC t hh)
  have hsq : t * t ∈ D := (D.subgroupOf P).mul_self_mem_of_index_two hi ⟨t,ht⟩
  have hswap : (MulAut.conj t) w = v := by
    calc
      _ = (MulAut.conj (t*t)) v := by simp [w, MulAut.conj_apply, mul_assoc]
      _ = v := mul_inv_eq_iff_eq_mul.mpr (hvC _ hsq)
  have hcomm : Commute v w := (hvC w hwD).symm
  have htc : t ∈ centralizer ({v*w} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    change (MulAut.conj t) (v*w) = v*w
    rw [map_mul,hswap]
    exact hcomm.eq.symm
  have hDC : D ≤ centralizer ({v*w} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr ((show Commute x v from hvC x hx).mul_right (hwC x hx))
  have hPC : P ≤ centralizer ({v*w} : Set G) := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact hDC hxD
    · have hxt : x*t⁻¹ ∈ D :=
        ((D.subgroupOf P).mul_mem_iff_of_index_two hi).mpr
          (show ((⟨x,hx⟩ : P) ∈ D.subgroupOf P ↔
            (⟨t⁻¹,P.inv_mem ht⟩ : P) ∈ D.subgroupOf P) from by
            change x ∈ D ↔ t⁻¹ ∈ D
            simp only [inv_mem_iff,hxD,htD])
      simpa only [inv_mul_cancel_right] using
        (centralizer ({v*w} : Set G)).mul_mem (hDC hxt) htc
  have hw2 : w ^ 2 = 1 := by rw [show w = (MulAut.conj t) v from rfl,←map_pow,hv2,map_one]
  have hv1 : v ≠ 1 := by intro hh; simp [hh] at hmove
  have hprod1 : v*w ≠ 1 := by
    intro hh
    have he : w = v := by
      calc
        w = v*(v*w) := by rw [←mul_assoc,←pow_two,hv2,one_mul]
        _ = v := by rw [hh,mul_one]
    exact hmove he
  refine ⟨hw,hmove,hswap,?_,hprod1,?_,?_⟩
  · rw [map_center_subtype_eq_inf_centralizer]
    exact ⟨P.mul_mem (hDP hvD) (hDP hwD), fun x hx =>
      mem_centralizer_singleton_iff.mp (hPC hx)⟩
  · rw [hcomm.mul_pow,hv2,hw2,one_mul]
  · intro hh
    have hw1 : w = 1 := mul_left_cancel (hh.trans (mul_one v).symm)
    exact hv1 ((MulAut.conj t).injective (hw1.trans (map_one _).symm))
end Subgroup
