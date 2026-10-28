module

public import Theory.GroupTheory.CommutatorPreimage
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Stability of fixed subgroups under an abelian quotient action

When P normalizes an abelian V and P/V is abelian, the induced automorphisms
on V commute. Consequently P preserves the fixed subgroup of each actor.
The companion join lemma derives the required commutator containment from
the normalized factor and its derived subgroup.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed p246.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G:Type*} [Group G]
theorem commutator_sup_le_of_normalized_derived (V D:Subgroup G)
    (hDV:D≤normalizer (V:Set G)) (hDD:⁅D,D⁆≤V) : ⁅V⊔D,V⊔D⁆≤V := by
  let P:=V⊔D
  have hPN:P≤normalizer (V:Set G):=sup_le V.le_normalizer hDV
  have hPV:⁅V,P⁆≤V:=le_normalizer_iff_commutator_le_left.mp hPN
  have hpre:P≤commutatorPreimage P D V:=sup_le
    (le_commutatorPreimage le_sup_left (le_normalizer_iff_commutator_le_left.mp hDV))
    (le_commutatorPreimage le_sup_right hDD)
  have hPD:⁅P,D⁆≤V:=(commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le P D V hPN)
  have hpre':P≤commutatorPreimage P P V:=sup_le
    (le_commutatorPreimage le_sup_left hPV)
    (le_commutatorPreimage le_sup_right (by rw [commutator_comm];exact hPD))
  exact (commutator_mono hpre' le_rfl).trans (commutator_commutatorPreimage_le P P V hPN)

theorem abelian_quotient_preserves_fixed (P V:Subgroup G) [IsMulCommutative V]
    (hPV:P≤normalizer (V:Set G)) (hcom:⁅P,P⁆≤V) (x:G) (hx:x∈P) :
    P≤normalizer ((V⊓centralizer ({x}:Set G):Subgroup G):Set G) := by
  let f:P→*MulAut V:=V.normalizerMonoidHom.comp (inclusion hPV)
  have hf (p q:P):Commute (f p) (f q):=by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    ext v
    change (⁅(p:G),(q:G)⁆*(v:G)*⁅(p:G),(q:G)⁆⁻¹)=(v:G)
    have hc:⁅(p:G),(q:G)⁆∈V:=hcom (commutator_mem_commutator p.property q.property)
    rw [←V.le_centralizer hc v v.property,mul_inv_cancel_right]
  apply le_normalizer_iff.mpr
  intro g hg v hv
  have hgv:g*v*g⁻¹∈V:=(mem_normalizer_iff.mp (hPV hg) v).mp hv.1
  refine ⟨hgv,mem_centralizer_singleton_iff.mpr ?_⟩
  have hvfix:f ⟨x,hx⟩ ⟨v,hv.1⟩=(⟨v,hv.1⟩:V):=by
    apply Subtype.ext
    change x*v*x⁻¹=v
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hv.2).symm
  have hh:=DFunLike.congr_fun (hf ⟨x,hx⟩ ⟨g,hg⟩).eq (⟨v,hv.1⟩:V)
  change f ⟨x,hx⟩ (f ⟨g,hg⟩ ⟨v,hv.1⟩)=f ⟨g,hg⟩ (f ⟨x,hx⟩ ⟨v,hv.1⟩) at hh
  rw [hvfix] at hh
  have he:x*(g*v*g⁻¹)*x⁻¹=g*v*g⁻¹:=congrArg Subtype.val hh
  exact (mul_inv_eq_iff_eq_mul.mp he).symm
end Subgroup
