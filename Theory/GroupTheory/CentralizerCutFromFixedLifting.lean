module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# A centralizer cut from fixed-point lifting

If Z lies in U D, D centralizes L, and commutators of Z with the candidate
cut lie in D, fixed-point lifting on U makes that cut centralize Z. The proof
retains the literal product with T intersect C(Z) and the literal core Q.

Source: the last paragraph of Meierfrankenfeld–Stellmacher (1993), (3.4),
printed p.869. The prior graph comparisons and the representation giving
fixed-point lifting are separate inputs.
-/

public section
open scoped Pointwise commutatorElement
open Subgroup

namespace Subgroup
variable {G : Type*} [Group G]

theorem centralizer_cut_of_fixed_lifting (L T Q U D Z : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G)) (hQT : Q ≤ T)
    (hDU : D ≤ normalizer (U : Set G))
    (hDL : D ≤ centralizer (L : Set G)) (hZ : Z ≤ U ⊔ D)
    (hcomm : ⁅Z, (L ⊔ (T ⊓ centralizer (Z : Set G))) ⊓ Q⁆ ≤ D)
    (hfix : ∀ u ∈ U, ∀ l ∈ L, ⁅l,u⁆ ∈ D → Commute l u) :
    (L ⊔ (T ⊓ centralizer (Z : Set G))) ⊓ Q ≤ T ⊓ centralizer (Z : Set G) := by
  intro x hx
  refine ⟨hQT hx.2, ?_⟩
  intro z hz
  have hxprod : x ∈ (L : Set G) * ((T ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L _ (inf_le_left.trans hTL)]
    exact hx.1
  obtain ⟨l,hl,t,ht,rfl⟩ := hxprod
  have hzprod : z ∈ (U : Set G) * (D : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left U D hDU]
    exact hZ hz
  obtain ⟨u,hu,d,hd,rfl⟩ := hzprod
  have htd : Commute t (u*d) := (ht.2 (u*d) hz).symm
  have hld : Commute l d := (hDL hd l hl)
  have hc : ⁅l,u⁆ ∈ D := by
    have hc' : ⁅l*t,u*d⁆ ∈ D := by
      simpa only [commutatorElement_inv] using
        D.inv_mem (hcomm (commutator_mem_commutator hz hx))
    rw [commutatorElement_mul_left_eq_conj_mul l t (u*d),
      commutatorElement_eq_one_iff_commute.mpr htd, mul_one, mul_inv_cancel,
      one_mul, commutatorElement_mul_right_eq_mul_conj l u d,
      commutatorElement_eq_one_iff_commute.mpr hld, mul_one,
      mul_inv_cancel_right] at hc'
    exact hc'
  have hlz : Commute l (u*d) := (hfix u hu l hl hc).mul_right hld
  exact ((hlz.mul_left htd).symm).eq

end Subgroup
