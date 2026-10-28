module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.LocalGluing.ModuleData
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# Transport to the second canonical fusion eight

The intrinsic core and its fusion-generated subgroup commute with group
isomorphisms. Sylow conjugacy transports the fixed-point hypothesis from the
chosen cubic to every order-three subgroup of the involution centralizer.
These statements give both `CubicEightContext`s for the source chain, including
the literal canonical subgroup at the selected involution c.u. No simplicity
or choice of the ambient-order alternative is used.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), the symmetry in Lemma 4.6, pp.40–41.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.LocalGluing

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] {K : Type*} [Group K]

public theorem map_centralizer (e : G ≃* K) (S : Set G) :
    (centralizer S).map e.toMonoidHom = centralizer (e '' S) := by
  apply le_antisymm (map_centralizer_le_centralizer_image S e.toMonoidHom)
  intro t ht
  refine ⟨e.symm t, ?_, e.apply_symm_apply t⟩
  intro s hs
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using ht (e s) ⟨s, hs, rfl⟩

public theorem map_involutionCentralizer (e : G ≃* K) (z : G) :
    (Centralizer z).map e.toMonoidHom = Centralizer (e z) := by
  simpa only [Set.image_singleton] using map_centralizer e ({z} : Set G)

@[expose] public def centralizerEquiv (e : G ≃* K) (z : G) :
    Centralizer z ≃* Centralizer (e z) :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_involutionCentralizer e z))

@[simp] public theorem centralizerEquiv_coe (e : G ≃* K) (z : G) (t : Centralizer z) :
    (centralizerEquiv e z t : K) = e (t : G) := rfl

public theorem map_coreInG (e : G ≃* K) (z : G) :
    (coreInG z).map e.toMonoidHom = coreInG (e z) := by
  have he : e.toMonoidHom.comp (Centralizer z).subtype =
      (Centralizer (e z)).subtype.comp (centralizerEquiv e z).toMonoidHom := rfl
  rw [coreInG, map_map, he, ← map_map, map_generalizedFitting_equiv]
  rfl

public theorem map_fusionCore (e : G ≃* K) (z : G) :
    (fusionCore z).map e.toMonoidHom = fusionCore (e z) := by
  rw [fusionCore, MonoidHom.map_closure, fusionCore]
  congr 1
  ext t
  constructor
  · rintro ⟨s, ⟨hs, hc⟩, rfl⟩
    exact ⟨map_coreInG e z ▸ mem_map_of_mem e.toMonoidHom hs, e.toMonoidHom.map_isConj hc⟩
  · rintro ⟨ht, hc⟩
    have ht' : t ∈ (coreInG z).map e.toMonoidHom := map_coreInG e z ▸ ht
    obtain ⟨s, hs, rfl⟩ := ht'
    refine ⟨s, ⟨hs, ?_⟩, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using e.symm.toMonoidHom.map_isConj hc

public theorem fusionEightData_map (e : G ≃* K) {z : G} (d : FusionEightData z) :
    FusionEightData (e z) := by
  let f : fusionCore z ≃* fusionCore (e z) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_fusionCore e z))
  have he : IsElementaryAbelian 2 (fusionCore (e z)) := by
    let := d.elementary
    have hm := IsElementaryAbelian.map (p := 2) (A := fusionCore z) e.toMonoidHom
    rwa [map_fusionCore] at hm
  refine ⟨he, (Nat.card_congr f.toEquiv).symm.trans d.card, ?_, ?_⟩
  · intro t ht ht1
    have ht' : t ∈ (fusionCore z).map e.toMonoidHom := map_fusionCore e z ▸ ht
    obtain ⟨s, hs, rfl⟩ := ht'
    exact e.toMonoidHom.map_isConj (d.fusion s hs (fun he => ht1 (he ▸ e.map_one)))
  · have hset : e '' (fusionCore z : Set G) = (fusionCore (e z) : Set K) := by
      exact congrArg SetLike.coe (map_fusionCore e z)
    rw [← hset, ← map_centralizer, d.centralizer_eq, map_fusionCore]

public theorem centralizer_le_normalizer_canonical (r : G) :
    Centralizer r ≤ normalizer (fusionCore r : Set G) := by
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (fusionCore r).map (MulAut.conj t).toMonoidHom = fusionCore r
  rw [map_fusionCore]
  have he : (MulAut.conj t) r = r :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp ht)
  rw [he]

variable [Finite G] {z : G}

public theorem fixed_core_sylow (h : Hypotheses z) (P : Sylow 3 (Centralizer z)) :
    Core z ⊓ centralizer (P : Set (Centralizer z)) = zpowers (distinguished z) := by
  obtain ⟨t, rfl⟩ := MulAction.exists_smul_eq (Centralizer z) h.X P
  have he := congrArg (Subgroup.map (MulAut.conj t).toMonoidHom) h.fixed
  rw [map_inf _ _ _ (MulAut.conj t).injective, map_centralizer,
    MonoidHom.map_zpowers] at he
  have hQ : (Core z).map (MulAut.conj t).toMonoidHom = Core z :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; trivial)
  have hz : (MulAut.conj t) (distinguished z) = distinguished z := by
    apply Subtype.ext
    change (t : G) * z * (t : G)⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp t.property)
  rw [hQ, MulEquiv.coe_toMonoidHom, hz] at he
  exact he

public theorem fixed_core_three (h : Hypotheses z) (Y : Subgroup G)
    (hY : Y ≤ Centralizer z) (hc : Nat.card Y = 3) :
    coreInG z ⊓ centralizer (Y : Set G) = zpowers z := by
  let P : Sylow 3 (Centralizer z) := Sylow.ofCard (Y.subgroupOf (Centralizer z)) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv, hc, h.centralizer_card]
    decide +kernel)
  have hf := fixed_core_sylow h P
  have hYmap : (P : Subgroup (Centralizer z)).map (Centralizer z).subtype = Y :=
    map_subgroupOf_eq_of_le hY
  apply le_antisymm
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := ht.1
    have hs' : s ∈ Core z ⊓ centralizer (P : Set (Centralizer z)) := by
      refine ⟨hs, ?_⟩
      intro y hy
      apply Subtype.ext
      exact ht.2 y (hYmap ▸ mem_map_of_mem _ hy)
    have hsz : s ∈ zpowers (distinguished z) := hf ▸ hs'
    have hm := mem_map_of_mem (Centralizer z).subtype hsz
    simpa only [MonoidHom.map_zpowers, Subgroup.coe_subtype, distinguished] using hm
  · refine le_inf (zpowers_le.mpr h.involution_mem_coreInG) (zpowers_le.mpr ?_)
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hY hy)

public theorem fixed_fusion_three (h : Hypotheses z) (Y : Subgroup G)
    (hY : Y ≤ Centralizer z) (hc : Nat.card Y = 3) :
    fusionCore z ⊓ centralizer (Y : Set G) = zpowers z := by
  apply le_antisymm
  · exact (inf_le_inf_right _ (fusionCore_le z)).trans (fixed_core_three h Y hY hc).le
  · refine le_inf (zpowers_le.mpr h.involution_mem_fusionCore) (zpowers_le.mpr ?_)
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hY hy)

public theorem fixed_fusion_three_conjugate (h : Hypotheses z) {r : G}
    (hr : IsConj z r) (Y : Subgroup G) (hY : Y ≤ Centralizer r) (hc : Nat.card Y = 3) :
    fusionCore r ⊓ centralizer (Y : Set G) = zpowers r := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hr
  let e : G ≃* G := MulAut.conj g
  let Y0 := Y.comap e.toMonoidHom
  have hmap : Y0.map e.toMonoidHom = Y := map_comap_eq_self_of_surjective e.surjective Y
  have hY0 : Y0 ≤ Centralizer z := by
    intro t ht
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    rw [map_mul, map_mul]
    exact mem_centralizer_singleton_iff.mp (hY ht)
  have hc0 : Nat.card Y0 = 3 := by
    calc
      Nat.card Y0 = Nat.card (Y0.map e.toMonoidHom) := Nat.card_congr (e.subgroupMap Y0).toEquiv
      _ = 3 := by rw [hmap, hc]
  have hf := congrArg (Subgroup.map e.toMonoidHom) (fixed_fusion_three h Y0 hY0 hc0)
  rw [map_inf _ _ _ e.injective, map_fusionCore, map_centralizer,
    MonoidHom.map_zpowers] at hf
  have hset : e '' (Y0 : Set G) = (Y : Set G) := congrArg SetLike.coe hmap
  rw [hset] at hf
  exact hf

/-- The source's two actual elementary eights carry the required cubic and
involution actions. The second eight is the canonical fusion core at c.u. -/
public theorem cubicEightContexts (h : Hypotheses z) (d : FusionEightData z)
    {a : SourceGeometry h} (c : CommutingCubicData h a) :
    CubicEightContext z c.u (cubicInG h) ∧ CubicEightContext c.u z c.X1 := by
  have hn (r : G) := centralizer_le_normalizer_canonical r
  have hc : c.u ∈ Centralizer z := mem_centralizer_singleton_iff.mpr c.u_commutes_z
  have hcz : z ∈ Centralizer c.u := mem_centralizer_singleton_iff.mpr c.u_commutes_z.symm
  have hX1 : c.X1 ≤ Centralizer c.u := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (c.u_centralizes_X1 t ht).symm
  have du : FusionEightData c.u := by
    obtain ⟨g, hg⟩ := isConj_iff.mp c.u_fused
    have de := fusionEightData_map (MulAut.conj g) d
    change FusionEightData (g * z * g⁻¹) at de
    exact hg ▸ de
  have huF : c.u ∈ fusionCore c.u := by
    obtain ⟨g, hg⟩ := isConj_iff.mp c.u_fused
    have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom h.involution_mem_fusionCore
    rw [map_fusionCore] at hm
    change g * z * g⁻¹ ∈ fusionCore (g * z * g⁻¹) at hm
    exact hg ▸ hm
  constructor
  · exact {
      elementary := d.elementary
      card := d.card
      base_mem := h.involution_mem_fusionCore
      base_order := h.involution
      cubic_card := cubicInG_card h
      cubic_normalizes := (cubicInG_le h).trans (hn z)
      cubic_fixed := fixed_fusion_three h _ (cubicInG_le h) (cubicInG_card h)
      involution_order := c.u_order
      involution_normalizes := hn z hc
      inverts := c.u_inverts_X }
  · exact {
      elementary := du.elementary
      card := du.card
      base_mem := huF
      base_order := c.u_order
      cubic_card := c.card_X1
      cubic_normalizes := hX1.trans (hn c.u)
      cubic_fixed := fixed_fusion_three_conjugate h c.u_fused c.X1 hX1 c.card_X1
      involution_order := h.involution
      involution_normalizes := hn c.u hcz
      inverts := c.z_inverts_X1 }

/-- Multiplying the source choice by z does not put it into the core. -/
public theorem selected_involution_not_core {h : Hypotheses z} {a : SourceGeometry h} (c : CommutingCubicData h a) :
    c.u ∉ coreInG z := by
  rcases c.u_choice with he | he
  · exact he ▸ a.u_not_core
  · rw [he]
    intro hu
    exact a.u_not_core ((mul_mem_cancel_right h.involution_mem_coreInG).mp hu)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.LocalGluing
