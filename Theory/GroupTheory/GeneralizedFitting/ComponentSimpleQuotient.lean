module
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
public import Theory.GroupTheory.GeneralizedFitting.ComponentProductCenters

/-!
# Simple quotients of a centerless two-component orbit

Two conjugate components with normalizer of index two generate their orbit.
Each is normal in that orbit, so a surjection to a simple group is nontrivial
on a factor. Its kernel in that factor is central, hence trivial when the
orbit is centerless. Conjugacy identifies that factor with the original one.

Source: the paired-component step in Aschbacher--Smith G.10.15,
printed pp.362--363.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.GroupTheory.ExchangedOrbit
private theorem factor_equiv_image {G Q : Type*} [Group G] [Group Q]
    {C : Subgroup G} (hC : IsComponent G C) (hz : center C = ⊥)
    (f : G →* Q) (hne : C.map f ≠ ⊥) : Nonempty (C ≃* C.map f) := by
  let : IsQuasisimple C := hC.2
  let r : C →* C.map f := f.subgroupMap C
  have hk : r.ker ≤ center C := by
    rcases IsQuasisimple.normal_le_center_or_eq_top r.ker with hk | ht
    · exact hk
    · apply False.elim
      apply hne
      apply bot_unique
      rintro _ ⟨c,hc,rfl⟩
      have ha : (⟨c,hc⟩:C) ∈ r.ker := by rw [ht]; exact mem_top _
      have he : r ⟨c,hc⟩ = 1 := MonoidHom.mem_ker.mp ha
      exact mem_bot.mpr (congrArg (fun q : C.map f => (q:Q)) he)
  exact ⟨MulEquiv.ofBijective r ⟨(MonoidHom.ker_eq_bot_iff r).mp
    (bot_unique (hk.trans_eq hz)),f.subgroupMap_surjective C⟩⟩

/-- A centerless two-component orbit has its original component isomorphic
 to every nontrivial simple quotient. -/
theorem component_equiv_simple_quotient
    {G Q : Type*} [Group G] [Finite G] [Group Q] [IsSimpleGroup Q]
    {L : Subgroup G} (hL : IsComponent G L)
    (hi : (normalizer (L:Set G)).index = 2)
    (f : componentOrbit L ⊤ →* Q) (hf : Function.Surjective f)
    (hz : center (componentOrbit L ⊤) = ⊥) : Nonempty (L ≃* Q) := by
  have hex : ∃ t : G, t ∉ normalizer (L:Set G) := by
    by_contra! hn
    have ht : normalizer (L:Set G) = ⊤ := top_unique (fun t _ => hn t)
    rw [ht,index_top] at hi
    omega
  obtain ⟨t,ht⟩ := hex
  let H := componentOrbit L ⊤
  let K := L.map (MulAut.conj t).toMonoidHom
  have hprod : H = L ⊔ K := componentOrbit_eq_sup_of_index_two L ⊤ (normalizer (L:Set G))
    (by simpa only [relIndex_top_right] using hi) inf_le_right (mem_top t) ht
  have hLH : L ≤ H := le_componentOrbit L ⊤
  have hKH : K ≤ H := hprod ▸ le_sup_right
  let A := L.subgroupOf H
  let B := K.subgroupOf H
  have hA : IsComponent H A := hL.subgroupOf hLH
  have hB : IsComponent H B := (hL.map_conj t).subgroupOf hKH
  have hAB : A ⊔ B = ⊤ := by
    rw [←subgroupOf_sup hLH hKH,←hprod,subgroupOf_self]
  have hsemi : componentLayer H = ⊤ := by
    apply top_unique
    rw [←hAB]
    exact sup_le (le_sSup hA) (le_sSup hB)
  have hcenter (C : Subgroup H) (hC : IsComponent H C) : center C = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ C.subtype_injective).mp
    exact le_bot_iff.mp (hz ▸ hC.center_map_le_center_of_semisimple hsemi)
  have hne : K ≠ L := fun he => ht (mem_normalizer_iff_map_conj_eq.mpr he)
  have hc : L ≤ centralizer (K:Set G) := commutator_eq_bot_iff_le_centralizer.mp
    (hL.commutator_eq_bot_of_ne (hL.map_conj t) hne.symm)
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer hLH).mpr (by
    rw [hprod]
    exact sup_le L.le_normalizer ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)))
  let : B.Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr (by
    rw [hprod]
    exact sup_le (hc.trans (Subgroup.centralizer_le_normalizer _)) K.le_normalizer)
  have hmap : A.map f ⊔ B.map f = ⊤ := by
    rw [←Subgroup.map_sup,hAB,←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr hf]
  have hnA : (A.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hnB : (B.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have heq (C : Subgroup H) (hC : IsComponent H C) (htop : C.map f = ⊤) : Nonempty (C ≃* Q) := by
    obtain ⟨e⟩ := factor_equiv_image hC (hcenter C hC) f (by rw [htop]; exact top_ne_bot)
    exact ⟨(e.trans (MulEquiv.subgroupCongr htop)).trans topEquiv⟩
  rcases hnA.eq_bot_or_eq_top with ha | ha
  · have hb : B.map f = ⊤ := by rwa [ha,bot_sup_eq] at hmap
    obtain ⟨e⟩ := heq B hB hb
    exact ⟨(((MulAut.conj t).subgroupMap L).trans
      (subgroupOfEquivOfLe hKH).symm).trans e⟩
  · obtain ⟨e⟩ := heq A hA ha
    exact ⟨(subgroupOfEquivOfLe hLH).symm.trans e⟩
end Theory.GroupTheory.ExchangedOrbit

