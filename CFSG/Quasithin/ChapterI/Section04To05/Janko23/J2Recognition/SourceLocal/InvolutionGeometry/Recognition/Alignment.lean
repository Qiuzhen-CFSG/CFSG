module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.Contracts
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Aligning the recognized root-four geometry with the fixed vertex

An actual A₄ factor of the root-core normalizer embeds in the full centralizer
of the A₅ component. That centralizer is contained in C_G(z), since z belongs
to the component. Its order therefore has three-part exactly three. A Sylow
three-subgroup maps to a subgroup of order three in C_G(z), where Sylow
conjugacy aligns it with the specified seed vertex X.

Transport uses actual subgroup equivalences and carries the intrinsic core,
component layer, both factor embeddings and ambient fusion marking. This
proves selection from `UnalignedGeometry`; it does not construct that geometry.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1(1), p.260.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition
variable {G : Type*} [Group G]

private theorem map_centralizer (e : G ≃* G) (s : Set G) :
    (centralizer s).map e.toMonoidHom = centralizer (e '' s) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e y) ⟨y, hy, rfl⟩

private theorem map_layer_le {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    (componentLayer H).map e.toMonoidHom ≤ componentLayer K := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro J hJ
  exact map_le_iff_le_comap.mp (le_sSup (hJ.map_equiv e))

private theorem map_layer {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    (componentLayer H).map e.toMonoidHom = componentLayer K := by
  apply le_antisymm (map_layer_le e)
  have hm := map_mono (f := e.toMonoidHom) (map_layer_le e.symm)
  simpa [map_map] using hm

private noncomputable def centralizerEquiv (e : G ≃* G) (t : G) :
    involutionCentralizer t ≃* involutionCentralizer (e t) :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (by
    change (centralizer ({t} : Set G)).map e.toMonoidHom = centralizer ({e t} : Set G)
    simpa only [Set.image_singleton] using map_centralizer e ({t} : Set G)))

private theorem rootCore_map (e : G ≃* G) (t : G) :
    (rootCore t).map e.toMonoidHom = rootCore (e t) := by
  rw [rootCore, rootCore, pCoreIn, pCoreIn,
    ← pCore_map_iso 2 (centralizerEquiv e t), map_map, map_map]
  rfl

private theorem rootComponent_map (e : G ≃* G) (t : G) :
    (rootComponent t).map e.toMonoidHom = rootComponent (e t) := by
  rw [rootComponent, rootComponent, ← map_layer (centralizerEquiv e t),
    map_map, map_map]
  rfl


variable [Finite G]

private noncomputable def transportModel {D : Seed G} {t : G}
    (C : SecondCentralizer D t) (e : G ≃* G) (hz : e D.z = D.z) :
    SecondCentralizer D (e t) where
  equiv := (centralizerEquiv e t).symm.trans C.equiv
  fusion := by
    intro u hu
    have he : IsConj D.z (u : G) ↔
        IsConj D.z ((centralizerEquiv e t).symm u : G) := by
      have hz' : e.symm D.z = D.z := e.injective (by rw [e.apply_symm_apply, hz])
      constructor
      · intro h
        have hm := e.symm.toMonoidHom.map_isConj h
        change IsConj (e.symm D.z) (e.symm (u : G)) at hm
        change IsConj D.z (e.symm (u : G))
        rwa [hz'] at hm
      · intro h
        have hm := e.toMonoidHom.map_isConj h
        change IsConj (e D.z) (e (e.symm (u : G))) at hm
        simpa only [hz, e.apply_symm_apply] using hm
    rw [he]
    exact C.fusion _ (((centralizerEquiv e t).symm.orderOf_eq u).trans hu)

private theorem fiveFactor_transport {D : Seed G} {t : G}
    (C : SecondCentralizer D t) (e : G ≃* G) (hz : e D.z = D.z) :
    (transportModel C e hz).fiveFactor = C.fiveFactor.map e.toMonoidHom := by
  simp only [SecondCentralizer.fiveFactor, map_map]
  rfl

namespace UnalignedGeometry
variable {D : Seed G} {t : G} (S : UnalignedGeometry D t)

include S in
/-- The whole component centralizer is inside the original involution centralizer. -/
theorem centralizer_le : centralizer (rootComponent t : Set G) ≤ involutionCentralizer D.z :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr S.z_mem_component)

private noncomputable def transport (e : G ≃* G) (hz : e D.z = D.z) :
    UnalignedGeometry D (e t) := by
  let ne : normalizer (rootCore t : Set G) ≃*
      normalizer (rootCore (e t) : Set G) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (by
      change (normalizer (rootCore t : Set G)).map e.toMonoidHom = _
      rw [map_equiv_normalizer_eq, rootCore_map]))
  refine {
    model := transportModel S.model e hz
    component_eq := ?_
    z_mem_component := ?_
    normalizerEquiv := ne.symm.trans S.normalizerEquiv
    normalizer_component := ?_
    normalizer_core := ?_ }
  · rw [fiveFactor_transport, ← S.component_eq, rootComponent_map]
  · rw [← hz, ← rootComponent_map]
    exact mem_map_of_mem _ S.z_mem_component
  · have hm := congrArg (Subgroup.map e.toMonoidHom) S.normalizer_component
    rw [rootComponent_map, map_map] at hm
    exact hm
  · have hm := congrArg (Subgroup.map e.toMonoidHom) S.normalizer_core
    rw [rootCore_map, map_map] at hm
    exact hm


include S in
/-- The centralizer of the component has exactly one factor of three in its order. -/
theorem centralizer_three_part :
    (Nat.card (centralizer (rootComponent t : Set G))).factorization 3 = 1 := by
  let C := centralizer (rootComponent t : Set G)
  let N := normalizer (rootCore t : Set G)
  let F : A4 × A5 →* G := N.subtype.comp S.normalizerEquiv.symm.toMonoidHom
  let f : A4 →* G := F.comp (MonoidHom.inl A4 A5)
  have hf : Function.Injective f :=
    (N.subtype_injective.comp S.normalizerEquiv.symm.injective).comp
      (fun _ _ h => congrArg Prod.fst h)
  have hc (a : A4) : f a ∈ C := by
    change f a ∈ centralizer (rootComponent t : Set G)
    rw [← S.normalizer_component]
    rintro _ ⟨b, hb, rfl⟩
    change F b * F (a, 1) = F (a, 1) * F b
    rw [← map_mul, ← map_mul]
    apply congrArg F
    have hb1 : b.1 = 1 := hb.1
    exact Prod.ext (by simp [hb1]) (by simp)
  let fC : A4 →* C := f.codRestrict C hc
  have hdiv : Nat.card A4 ∣ Nat.card C := card_dvd_of_injective fC
    (fun a b h => hf (congrArg (fun x : C => (x : G)) h))
  have hA4 : Nat.card A4 = 12 := by rw [nat_card_alternatingGroup]; norm_num
  have hthree : 3 ∣ Nat.card C := dvd_trans (by rw [hA4]; norm_num) hdiv
  have hupper : Nat.card C ∣ 1920 := by
    simpa only [D.localType.centralizer_card] using card_dvd_of_le S.centralizer_le
  have hfac := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (by decide : 1920 ≠ 0)).mpr hupper 3
  have hf1920 : Nat.factorization 1920 3 = 1 := by decide +kernel
  have hlower := (Nat.prime_three.dvd_iff_one_le_factorization Nat.card_pos.ne').mp hthree
  rw [hf1920] at hfac
  exact le_antisymm hfac hlower

/-- Align the component's cubic centralizer with the originally prescribed vertex.
Conjugation is taken inside C_G(z), so the distinguished involution is retained. -/
noncomputable def select (ht : OtherInvolution D t) : SelectedGeometry D := by
  let C := centralizer (rootComponent t : Set G)
  let P : Sylow 3 C := Classical.choice inferInstance
  let Y : Subgroup G := (P : Subgroup C).map C.subtype
  have hY : Nat.card Y = 3 := by
    rw [card_map_of_injective C.subtype_injective, P.card_eq_multiplicity,
      S.centralizer_three_part, pow_one]
  have hYH : Y ≤ involutionCentralizer D.z :=
    (map_subtype_le _).trans S.centralizer_le
  let g := Classical.choose (D.conjugate_of_le_centralizer Y hY hYH)
  have hg := Classical.choose_spec (D.conjugate_of_le_centralizer Y hY hYH)
  let e : G ≃* G := (MulAut.conj (g : G)).symm
  have hz : e D.z = D.z := by
    apply (MulAut.conj (g : G)).injective
    change (MulAut.conj (g : G)) ((MulAut.conj (g : G)).symm D.z) = _
    rw [MulEquiv.apply_symm_apply]
    exact (mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp g.property)).symm
  have hYmap : Y.map e.toMonoidHom = D.X := by
    have hh : D.X.map (MulAut.conj (g : G)).toMonoidHom = Y := hg
    rw [← hh, map_map]
    simp [e]
  let S' := S.transport e hz
  let C' := centralizer (rootComponent (e t) : Set G)
  have hC : C.map e.toMonoidHom = C' := by
    change (centralizer (rootComponent t : Set G)).map e.toMonoidHom =
      centralizer (rootComponent (e t) : Set G)
    rw [map_centralizer, ← rootComponent_map e t]
    rfl
  let ce : C ≃* C' := (e.subgroupMap C).trans (MulEquiv.subgroupCongr hC)
  let P' : Sylow 3 C' := P.mapSurjective (f := ce.toMonoidHom) ce.surjective
  have hP' : (P' : Subgroup C').map C'.subtype = D.X := by
    change ((P : Subgroup C).map ce.toMonoidHom).map C'.subtype = D.X
    rw [map_map]
    have he : C'.subtype.comp ce.toMonoidHom = e.toMonoidHom.comp C.subtype := rfl
    rw [he, ← map_map]
    exact hYmap
  refine {
    t := e t
    other := ⟨(e.orderOf_eq t).trans ht.1, ?_⟩
    model := S'.model
    component_eq := S'.component_eq
    z_mem_component := S'.z_mem_component
    X_centralizes_component := ?_
    X_sylow := ⟨P', hP'⟩
    normalizerEquiv := S'.normalizerEquiv
    normalizer_component := S'.normalizer_component
    normalizer_core := S'.normalizer_core }
  · intro h
    apply ht.2
    have hh := e.symm.toMonoidHom.map_isConj h
    change IsConj (e.symm D.z) (e.symm (e t)) at hh
    have hz' : e.symm D.z = D.z := e.injective (by rw [e.apply_symm_apply, hz])
    simpa only [hz', e.symm_apply_apply] using hh
  · rw [← hP']
    exact map_subtype_le _

end UnalignedGeometry
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition
