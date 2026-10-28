module

public import Stellmacher.Recognition.Parrott.CentralizerStructure
public import Theory.GroupTheory.C5C4ElementaryTwoSubgroup

/-!
# Derived subgroups of two-subgroups in Parrott's centralizer

Every two-subgroup of H=C_G(z) has its derived subgroup in J=O₂(H).
Indeed its image in H/J is a two-subgroup of C₅⋊C₄, hence cyclic.
This places the local derived groups in the core before computing their
images modulo E=J′, as in Parrott (1972), pp.674 and 677.
-/

open Subgroup
open scoped commutatorElement

namespace Stellmacher.Recognition

/-- The derived group of any two-subgroup of the involution centralizer
lies in the actual ambient image of its two-core. -/
public theorem parrott_two_subgroup_derived_le_core
    {G : Type*} [Group G] {z : G}
    (h : ParrottCentralizerHypotheses z) (V : Subgroup G)
    (hVH : V ≤ centralizer ({z} : Set G)) (hp : IsPGroup 2 V) :
    (commutator V).map V.subtype ≤
      (pCore 2 (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let K := V.subgroupOf H
  obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
  let m := e.toMonoidHom.comp (QuotientGroup.mk' J)
  let A := K.map m
  have hKp : IsPGroup 2 K := hp.comap_subtype
  let : IsCyclic A := (SemidirectProduct.two_subgroup_isCyclic_card_dvd_four
    φ A (hKp.map m)).1
  have hz : (⁅K, K⁆).map m = ⊥ := by
    rw [map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr A.le_centralizer
  have hK : ⁅K, K⁆ ≤ J := by
    intro x hx
    have hm : m x = 1 := (Subgroup.map_eq_bot_iff _).mp hz hx
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    simpa only [m, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply, map_one] using hm
  have hbound := map_mono (f := H.subtype) hK
  rw [map_commutator, map_subgroupOf_eq_of_le hVH] at hbound
  rwa [map_subtype_commutator]

end Stellmacher.Recognition
