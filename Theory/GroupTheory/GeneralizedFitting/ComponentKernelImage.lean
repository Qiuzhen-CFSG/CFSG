module
public import Theory.GroupTheory.ConjugateOrbitIndexTwo

/-!
# A component image from a noncentral kernel in a two-component orbit

The index-two normalizer identifies the original normal orbit with the join
of two actual components. A normal subgroup centralizes each component that
it does not contain. Thus a noncentral restricted kernel contains one factor.
If the orbit image is nontrivial, it is exactly the image of the other factor;
surjective component transport proves that this literal image is a component.
No component is assumed normal in the original ambient group.

Source application: Aschbacher--Smith G.10.15, printed p.362.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.ExchangedOrbit

private theorem one_factor_le_normal_of_not_central
    {G : Type*} [Group G] (A B N : Subgroup G) [N.Normal]
    (hA : IsComponent G A) (hB : IsComponent G B) (hAB : A ⊔ B = ⊤)
    (hn : ¬ N ≤ center G) : A ≤ N ∨ B ≤ N := by
  rcases hA.normal_dichotomy N with ha | ha
  · exact .inl ha
  rcases hB.normal_dichotomy N with hb | hb
  · exact .inr hb
  apply False.elim
  apply hn
  apply commutator_top_right_eq_bot_iff_le_center.mp
  rw [commutator_comm,←hAB]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact sup_le (commutator_eq_bot_iff_le_centralizer.mp ha)
    (commutator_eq_bot_iff_le_centralizer.mp hb)

/-- A nontrivial image of a two-component orbit under an actual surjection
is a component when the restricted kernel is noncentral. -/
theorem image_orbit_component
    {G Q : Type*} [Group G] [Finite G] [Group Q]
    {L : Subgroup G} (hL : IsComponent G L)
    (hi : (normalizer (L:Set G)).index = 2)
    (P : Subgroup G) (hHP : componentOrbit L ⊤ ≤ P)
    (f : P →* Q) (hf : Function.Surjective f)
    (hker : ¬ (f.comp (inclusion hHP)).ker ≤ center (componentOrbit L ⊤))
    (hne : ((componentOrbit L ⊤).subgroupOf P).map f ≠ ⊥) :
    IsComponent Q (((componentOrbit L ⊤).subgroupOf P).map f) := by
  classical
  have hex : ∃ t : G, t ∉ normalizer (L:Set G) := by
    by_contra! hn
    have ht : normalizer (L:Set G) = ⊤ := top_unique (fun t _ => hn t)
    rw [ht, index_top] at hi
    omega
  obtain ⟨t,ht⟩ := hex
  let H := componentOrbit L ⊤
  let K := L.map (MulAut.conj t).toMonoidHom
  have hprod : H = L ⊔ K := componentOrbit_eq_sup_of_index_two L ⊤ (normalizer (L:Set G))
    (by simpa only [relIndex_top_right] using hi) inf_le_right (mem_top t) ht
  have hLH : L ≤ H := le_componentOrbit L ⊤
  have hKH : K ≤ H := hprod ▸ le_sup_right
  have hAB : L.subgroupOf H ⊔ K.subgroupOf H = ⊤ := by
    rw [←subgroupOf_sup hLH hKH,←hprod,subgroupOf_self]
  have hmap : (H.subgroupOf P).map f = (L.subgroupOf P).map f ⊔ (K.subgroupOf P).map f := by
    rw [hprod, subgroupOf_sup (hLH.trans hHP) (hKH.trans hHP), Subgroup.map_sup]
  have hzero (C : Subgroup G) (hCH : C ≤ H)
      (hC : C.subgroupOf H ≤ (f.comp (inclusion hHP)).ker) :
      (C.subgroupOf P).map f = ⊥ := by
    apply bot_unique
    rintro q ⟨c,hc,rfl⟩
    exact MonoidHom.mem_ker.mp (hC (show (⟨c,hCH hc⟩:H) ∈ C.subgroupOf H from hc))
  rcases one_factor_le_normal_of_not_central (L.subgroupOf H) (K.subgroupOf H)
      (f.comp (inclusion hHP)).ker (hL.subgroupOf hLH)
      ((hL.map_conj t).subgroupOf hKH) hAB hker with ha | hb
  · rw [hzero L hLH ha,bot_sup_eq] at hmap
    rw [hmap]
    exact (((hL.map_conj t).subgroupOf (hKH.trans hHP)).map_surjective f hf).resolve_left
      (fun hz => hne (hmap.trans hz))
  · rw [hzero K hKH hb,sup_bot_eq] at hmap
    rw [hmap]
    exact ((hL.subgroupOf (hLH.trans hHP)).map_surjective f hf).resolve_left
      (fun hz => hne (hmap.trans hz))

end Theory.GroupTheory.ExchangedOrbit
