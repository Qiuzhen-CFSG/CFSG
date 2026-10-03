module

public import Theory.SpecificGroups.Tits.RecognitionSylowSeed
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Preserving marked generators in the Case 2 coordinate change

The printed isomorphism sends v to vt. Conjugation by x restores the supplied
z,t,v and hence makes the change usable with fixed local witnesses. Before
conjugation, both elementary bases and the generating sets of J and T have
unchanged closures. The campaign adapter uses normalization of those actual
subgroups to transport their closure equalities through conjugation.

Source: Parrott (1972), §3, printed pp.679–680. No abstract presentation or
isomorphism recognition is used: the replacement words lie in the original group.
-/

open Subgroup
namespace Tits.ParrottSylowSeedRelations
variable {G : Type*} [Group G] {z t v u w a b c d x : G}

/-- Conjugation by x restores the prescribed three marked involutions. -/
public theorem marked_conjugates (h : ParrottSylowSeedRelations true z t v u w a b c d x) :
    MulAut.conj x z = z ∧ MulAut.conj x t = t ∧ MulAut.conj x (v*t) = v := by
  have hxz : x*z=z*x := h.comm_zx.symm.eq
  have hxt : x*t=t*x := ((Tits.parrottCommutator_eq_one_iff x t).mp h.eq01_xt).eq
  have hxv := (Tits.parrottCommutator_eq_iff x v t).mp h.eq01_xv
  have tt : t*t=1 := by simpa only [pow_two] using h.t_sq
  have ft : MulAut.conj x t = t := by
    change x*t*x⁻¹=t
    rw [hxt, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨?_, ft, ?_⟩
  · change x*z*x⁻¹=z
    rw [hxz, mul_assoc, mul_inv_cancel, mul_one]
  · rw [map_mul, ft]
    change x*v*x⁻¹*t=v
    rw [hxv]
    have hxinv : Commute t x⁻¹ :=
      ((Tits.parrottCommutator_eq_one_iff x t).mp h.eq01_xt).symm.inv_right
    calc
      v*x*t*x⁻¹*t = v*x*(t*x⁻¹)*t := by simp only [mul_assoc]
      _ = v*x*(x⁻¹*t)*t := by rw [hxinv.eq]
      _ = v := by simp only [mul_assoc, mul_inv_cancel_left, tt, mul_one]

/-- The unprimed relations in the original group, fixing z,t,v literally. -/
public theorem caseTwo_corrected (h : ParrottSylowSeedRelations true z t v u w a b c d x) :
    ParrottSylowSeedRelations false z t v
      (MulAut.conj x u) (MulAut.conj x (w*u)) (MulAut.conj x a)
      (MulAut.conj x (a*b*t)) (MulAut.conj x c) (MulAut.conj x (c*d*u))
      (MulAut.conj x x⁻¹) := by
  have hh := h.caseTwo_raw.map (MulAut.conj x).toMonoidHom
  have hm := marked_conjugates h
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, hm.1, hm.2.1, hm.2.2] using hh

private theorem comm_mem (L : Subgroup G) {g k : G} (hg : g ∈ L) (hk : k ∈ L) :
    Tits.parrottCommutator g k ∈ L :=
  L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem hg) (L.inv_mem hk)) hg) hk

private theorem core_mem_tu {caseTwo : Bool}
    (h : ParrottSylowSeedRelations caseTwo z t v u w a b c d x)
    (L : Subgroup G) (ha : a ∈ L) (hb : b ∈ L) (hd : d ∈ L) : t ∈ L ∧ u ∈ L := by
  have ht : t ∈ L := h.eq05_ab ▸ comm_mem L ha hb
  have hv : v ∈ L := h.eq03_b ▸ L.pow_mem hb 2
  have had := comm_mem L ha hd
  rw [h.eq11_ad] at had
  cases caseTwo
  · exact ⟨ht, had⟩
  · exact ⟨ht, (L.mul_mem_cancel_right hv).mp had⟩

/-- The printed replacement words generate the original core. -/
public theorem caseTwo_core_closure (h : ParrottSylowSeedRelations true z t v u w a b c d x) :
    closure ({a, a*b*t, c, c*d*u} : Set G) = closure ({a,b,c,d} : Set G) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    have ha : a ∈ closure ({a,b,c,d} : Set G) := subset_closure (by simp)
    have hb : b ∈ closure ({a,b,c,d} : Set G) := subset_closure (by simp)
    have hc : c ∈ closure ({a,b,c,d} : Set G) := subset_closure (by simp)
    have hd : d ∈ closure ({a,b,c,d} : Set G) := subset_closure (by simp)
    obtain ⟨ht, hu⟩ := core_mem_tu h _ ha hb hd
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ha
    · exact mul_mem (mul_mem ha hb) ht
    · exact hc
    · exact mul_mem (mul_mem hc hd) hu
  · apply (closure_le _).mpr
    let L := closure ({a, a*b*t, c, c*d*u} : Set G)
    have ha : a ∈ L := subset_closure (by simp)
    have hb : a*b*t ∈ L := subset_closure (by simp)
    have hc : c ∈ L := subset_closure (by simp)
    have hd : c*d*u ∈ L := subset_closure (by simp)
    obtain ⟨ht, hu⟩ := core_mem_tu h.caseTwo_raw L ha hb hd
    have hb' : b ∈ L := (L.mul_mem_cancel_left ha).mp ((L.mul_mem_cancel_right ht).mp hb)
    have hd' : d ∈ L := (L.mul_mem_cancel_left hc).mp ((L.mul_mem_cancel_right hu).mp hd)
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> assumption

private theorem closure_five (g k l m n : G) :
    closure ({g,k,l,m,n} : Set G) = zpowers g ⊔ closure ({k,l,m,n} : Set G) := by
  rw [zpowers_eq_closure, ← closure_union]
  congr 1

/-- Inverting x and replacing the core generators preserves the Sylow closure. -/
public theorem caseTwo_sylow_closure (h : ParrottSylowSeedRelations true z t v u w a b c d x) :
    closure ({x⁻¹, a, a*b*t, c, c*d*u} : Set G) = closure ({x,a,b,c,d} : Set G) := by
  rw [closure_five, closure_five, h.caseTwo_core_closure, zpowers_inv]

/-- The elementary change of basis preserves the original derived subgroup. -/
public theorem caseTwo_derived_closure :
    closure ({z,t,v*t,u,w*u} : Set G) = closure ({z,t,v,u,w} : Set G) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    have hz : z ∈ closure ({z,t,v,u,w} : Set G) := subset_closure (by simp)
    have ht : t ∈ closure ({z,t,v,u,w} : Set G) := subset_closure (by simp)
    have hv : v ∈ closure ({z,t,v,u,w} : Set G) := subset_closure (by simp)
    have hu : u ∈ closure ({z,t,v,u,w} : Set G) := subset_closure (by simp)
    have hw : w ∈ closure ({z,t,v,u,w} : Set G) := subset_closure (by simp)
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hz
    · exact ht
    · exact mul_mem hv ht
    · exact hu
    · exact mul_mem hw hu
  · apply (closure_le _).mpr
    have hz : z ∈ closure ({z,t,v*t,u,w*u} : Set G) := subset_closure (by simp)
    have ht : t ∈ closure ({z,t,v*t,u,w*u} : Set G) := subset_closure (by simp)
    have hv : v*t ∈ closure ({z,t,v*t,u,w*u} : Set G) := subset_closure (by simp)
    have hu : u ∈ closure ({z,t,v*t,u,w*u} : Set G) := subset_closure (by simp)
    have hw : w*u ∈ closure ({z,t,v*t,u,w*u} : Set G) := subset_closure (by simp)
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hz
    · exact ht
    · exact (mul_mem_cancel_right ht).mp hv
    · exact hu
    · exact (mul_mem_cancel_right hu).mp hw

/-- The elementary change of basis preserves the supplied second elementary subgroup. -/
public theorem caseTwo_elementary_closure :
    closure ({z,t,v*t,u,a} : Set G) = closure ({z,t,v,u,a} : Set G) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    have hz : z ∈ closure ({z,t,v,u,a} : Set G) := subset_closure (by simp)
    have ht : t ∈ closure ({z,t,v,u,a} : Set G) := subset_closure (by simp)
    have hv : v ∈ closure ({z,t,v,u,a} : Set G) := subset_closure (by simp)
    have hu : u ∈ closure ({z,t,v,u,a} : Set G) := subset_closure (by simp)
    have hw : a ∈ closure ({z,t,v,u,a} : Set G) := subset_closure (by simp)
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hz
    · exact ht
    · exact mul_mem hv ht
    · exact hu
    · exact hw
  · apply (closure_le _).mpr
    have hz : z ∈ closure ({z,t,v*t,u,a} : Set G) := subset_closure (by simp)
    have ht : t ∈ closure ({z,t,v*t,u,a} : Set G) := subset_closure (by simp)
    have hv : v*t ∈ closure ({z,t,v*t,u,a} : Set G) := subset_closure (by simp)
    have hu : u ∈ closure ({z,t,v*t,u,a} : Set G) := subset_closure (by simp)
    have hw : a ∈ closure ({z,t,v*t,u,a} : Set G) := subset_closure (by simp)
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hz
    · exact ht
    · exact (mul_mem_cancel_right ht).mp hv
    · exact hu
    · exact hw

end Tits.ParrottSylowSeedRelations
