module
public import Theory.GroupTheory.ComponentLocalOrbitCore
/-!
# Commuting complements in an ordinary component orbit

For K inside an ordinary component L, conjugates under an actor A either
coincide or commute when N_A(L) normalizes K. The join of all conjugates
other than K is therefore a commuting complement to K in the orbit.
The relative version works inside a specified overgroup, preserving the
original ambient embeddings and allowing A to permute the components.

Source application: Aschbacher--Smith 15.1.22(*), printed pp.1098--1099.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem IsComponent.local_orbit_commuting_complement
    {L K A : Subgroup G} (hL : IsComponent G L) (hKL : K ≤ L)
    (hn : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G)) :
    ∃ C : Subgroup G, C ≤ componentOrbit K A ∧
      K ≤ centralizer (C : Set G) ∧ K ⊔ C = componentOrbit K A := by
  classical
  let F := fun a : A => K.map (MulAut.conj (a : G)).toMonoidHom
  let C := ⨆ a : {a : A // F a ≠ K}, F a
  have hCF : C ≤ componentOrbit K A := iSup_le fun a => le_iSup F a.1
  have hCK : C ≤ centralizer (K : Set G) := by
    apply iSup_le
    intro a
    have he : (MulAut.conj ((1 : A) : G)).toMonoidHom = MonoidHom.id G := by
      ext x; simp
    have hh := hL.local_conjugates_eq_or_commute hKL hn 1 a.1
    rw [he,Subgroup.map_id] at hh
    exact commutator_eq_bot_iff_le_centralizer.mp (hh.resolve_left a.2)
  refine ⟨C,hCF,le_centralizer_iff.mp hCK,?_⟩
  apply le_antisymm (sup_le (le_componentOrbit K A) hCF)
  apply iSup_le
  intro a
  change F a ≤ K ⊔ C
  by_cases ha : F a = K
  · rw [ha]; exact le_sup_left
  · exact (le_iSup (fun a : {a : A // F a ≠ K} => F a) ⟨a,ha⟩).trans le_sup_right

theorem IsComponent.relative_local_orbit_commuting_complement
    {H L K A : Subgroup G} (hL : IsComponent H (L.subgroupOf H))
    (hLH : L ≤ H) (hKL : K ≤ L) (hAH : A ≤ H)
    (hn : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G)) :
    ∃ C : Subgroup G, C ≤ componentOrbit K A ∧
      K ≤ centralizer (C : Set G) ∧ K ⊔ C = componentOrbit K A := by
  let F := K.subgroupOf H
  let B := A.subgroupOf H
  have hKH := hKL.trans hLH
  have hnH : B ⊓ normalizer (L.subgroupOf H : Set H) ≤ normalizer (F : Set H) := by
    rw [←subgroupOf_normalizer_eq hLH,←subgroupOf_normalizer_eq hKH]
    intro x hx
    exact hn hx
  obtain ⟨C,hC,hc,hg⟩ := hL.local_orbit_commuting_complement (subgroupOf_mono H hKL) hnH
  have hmF : F.map H.subtype = K := map_subgroupOf_eq_of_le hKH
  have hmB : B.map H.subtype = A := map_subgroupOf_eq_of_le hAH
  have hm : (componentOrbit F B).map H.subtype = componentOrbit K A := by
    rw [map_componentOrbit,hmF,hmB]
  refine ⟨C.map H.subtype,?_,?_,?_⟩
  · exact hm ▸ map_mono hC
  · intro k hk c hcm
    obtain ⟨c,hc',rfl⟩ := hcm
    exact congrArg Subtype.val (hc (show (⟨k,hKH hk⟩ : H) ∈ F from hk) c hc')
  · calc
      K ⊔ C.map H.subtype = (F ⊔ C).map H.subtype := by rw [Subgroup.map_sup,hmF]
      _ = (componentOrbit F B).map H.subtype := congrArg (map H.subtype) hg
      _ = componentOrbit K A := hm
end Theory.GroupTheory
