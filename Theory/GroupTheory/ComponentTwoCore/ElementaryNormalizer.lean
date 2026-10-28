module
public import Theory.GroupTheory.ComponentTwoCore.Normalizer
public import Theory.ElementaryAbelian.Basic

/-!+# Elementary normal subgroups preserve components with nonsquares

Suppose an elementary abelian two-subgroup V is normalized by an element s
of a component K. If a member v of V moves K, the conjugate component is
disjoint from K and commutes with it. The commutator of v and s belongs to
V, so its square is one. Its two component coordinates then imply s² = 1.
Thus a nonsquare in K ∩ N(V) forces V to preserve K.

This is the factor-preservation step for the paired odd-linear case of
Aschbacher–Smith E.2.7, printed p.219.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {H : Type*} [Group H] [Finite H]

theorem elementary_le_component_normalizer_of_nonsquare
    (K V : Subgroup H) (hK : IsComponent H K) (hC : K.IsCComponent)
    (hrad : solvableRadical H = ⊥) [IsElementaryAbelian 2 V]
    (s : H) (hsK : s ∈ K) (hsV : s ∈ normalizer (V : Set H))
    (hs : s ^ 2 ≠ 1) : V ≤ normalizer (K : Set H) := by
  intro v hv
  by_contra hn
  let D := K.map (MulAut.conj v).toMonoidHom
  have hne : K ≠ D := by
    intro he
    exact hn (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hc : ⁅K,D⁆ = ⊥ := hK.commutator_eq_bot_of_ne (hK.map_conj v) hne
  have hd : Disjoint K D :=
    hC.disjoint_of_commutator_eq_bot_of_solvableRadical_eq_bot hrad hc
  let c := MulAut.conj v s
  have hcD : c ∈ D := mem_map_of_mem _ hsK
  have hcomm : Commute c s :=
    commutator_eq_bot_iff_le_centralizer.mp hc hsK c hcD
  have hz : c * s⁻¹ ∈ V := by
    have hi := (mem_normalizer_iff.mp hsV v⁻¹).mp (V.inv_mem hv)
    simpa only [c,MulAut.conj_apply,mul_assoc] using V.mul_mem hv hi
  have he : c ^ 2 = s ^ 2 := by
    have hsq := elemPow_eq_one_of_isElementaryAbelian (p := 2) (c * s⁻¹) hz
    rw [hcomm.inv_right.mul_pow,inv_pow] at hsq
    exact mul_inv_eq_one.mp hsq
  exact hs (disjoint_def.mp hd (K.pow_mem hsK 2) (he ▸ D.pow_mem hcD 2))

end Subgroup
