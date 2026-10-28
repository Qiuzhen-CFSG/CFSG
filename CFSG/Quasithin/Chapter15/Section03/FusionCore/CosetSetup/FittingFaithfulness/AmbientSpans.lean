module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness.DualApplication
public import Theory.Frattini.OmegaProducts
public import Theory.GroupTheory.SubgroupCenterImageBound

/-!
# The original ambient extraspecial conjugate spans

Restrict the source subgroups to H, apply the faithful extraspecial dual-action
argument, and map its conclusions through the literal inclusion H → G.
The transport preserves the central involution subgroup, omega subgroup,
centers, normalizers, and both distinct conjugate spans. The earlier 15.3.48
Frattini and action-kernel conclusions remain in their intrinsic form.

Source: Aschbacher–Smith, proof of 15.3.49(c)–(d), printed p.1143.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness

/-- The two intrinsic conjugate spans give the original ambient spans. -/
theorem ambient_extraspecial_spans_of_emptyLf_and_omega_bound
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (H V A S : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hVH : V ≤ H) (hAH : A ≤ H)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hAQ : A ≤ H.pCoreIn 2) (hAS : A ≤ centralizer (S : Set G))
    (hOmegaS : omegaOneAmbient (H.pCoreIn 2) ≤ S)
    (hZA : centralInvolutions T ≤ A)
    (hHZ : H ≤ centralizer (centralInvolutions T : Set G))
    (hZcard : Nat.card (centralInvolutions T) = 2)
    (hPhi : (frattini (localSpan (A.subgroupOf H) ⊤)).map
      (localSpan (A.subgroupOf H) ⊤).subtype ≤ (centralInvolutions T).subgroupOf H)
    (hcomm : ⁅localSpan A H, H.pCoreIn 2⁆ ≤ centralInvolutions T)
    (hsmall : ∀ h : H, (∀ u ∈ localSpan (A.subgroupOf H) ⊤,
      ⁅u,h⁆ ∈ (centralInvolutions T).subgroupOf H) ↔ h ∈ pCore 2 H)
    (hQV : H.pCoreIn 2 ≤ normalizer (V : Set G))
    (hweak : ∀ g ∈ H, V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) →
      V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
    localSpan A H ≤ (center (omegaOneAmbient (H.pCoreIn 2))).map
        (omegaOneAmbient (H.pCoreIn 2)).subtype ∧
      IsElementaryAbelian 2 (localSpan A H) ∧
      localSpan V H ≤ H.pCoreIn 2 ∧ IsElementaryAbelian 2 (localSpan V H) := by
  let Z := (centralInvolutions T).subgroupOf H
  let : Z.Normal := layer_normal H (centralInvolutions T) hHZ
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  have hAQ' : A.subgroupOf H ≤ pCore 2 H := by
    intro a ha
    exact (mem_map_iff_mem H.subtype_injective).mp (hAQ ha)
  have hAS' : A.subgroupOf H ≤ centralizer (S.subgroupOf H : Set H) := by
    intro a ha s hs
    exact Subtype.ext (hAS ha s hs)
  have hOmap : (omegaOneAmbient (pCore 2 H)).map H.subtype =
      omegaOneAmbient (H.pCoreIn 2) :=
    map_omegaOneAmbient_injective H.subtype H.subtype_injective (pCore 2 H)
  have hOmegaS' : omegaOneAmbient (pCore 2 H) ≤ S.subgroupOf H := by
    intro a ha
    apply hOmegaS
    rw [←hOmap]
    exact mem_map_of_mem H.subtype ha
  have hZQ : Z ≤ pCore 2 H := (comap_mono hZA).trans hAQ'
  have hZcenter : Z ≤ center H := by
    intro z hz
    apply mem_center_iff.mpr
    intro h
    exact Subtype.ext ((hHZ h.property z hz).symm)
  have hZcard' : Nat.card Z = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe (hZA.trans hAH)).toEquiv).trans hZcard
  have hZsyl : centralInvolutions (T.subtype hTH) ≤ Z := by
    intro z hz
    have hm := mem_map_of_mem H.subtype hz
    rwa [centralInvolutions_subtype_map T H hTH] at hm
  have hcomm' : ⁅pCore 2 H, localSpan (A.subgroupOf H) ⊤⁆ ≤ Z := by
    apply commutator_le.mpr
    intro q hq u hu
    have huG : (u : G) ∈ localSpan A H := by
      rw [←map_localSpan_subgroupOf A H hAH]
      exact mem_map_of_mem H.subtype hu
    have hb : ⁅H.pCoreIn 2, localSpan A H⁆ ≤ centralInvolutions T := by
      rwa [commutator_comm]
    exact hb (commutator_mem_commutator (mem_map_of_mem H.subtype hq) huG)
  have hsmall' : centralizerModulo ⊤ (localSpan (A.subgroupOf H) ⊤) Z ≤ pCore 2 H := by
    intro x hx
    exact (hsmall x).mp (mem_centralizerModulo_iff.mp hx).2
  have hQV' : pCore 2 H ≤ normalizer (V.subgroupOf H : Set H) := by
    rw [←subgroupOf_normalizer_eq hVH]
    intro q hq
    exact hQV (mem_map_of_mem H.subtype hq)
  have hweak' : ∀ g : H,
      (V.subgroupOf H).map (MulAut.conj g).toMonoidHom ≤
        normalizer (V.subgroupOf H : Set H) →
      (V.subgroupOf H).map (MulAut.conj g).toMonoidHom ≤
        centralizer (V.subgroupOf H : Set H) := by
    intro g hg
    have hn : V.map (MulAut.conj (g : G)).toMonoidHom ≤ normalizer (V : Set G) := by
      rintro _ ⟨v,hv,rfl⟩
      have hh := hg (mem_map_of_mem (MulAut.conj g).toMonoidHom
        (show (⟨v,hVH hv⟩ : H) ∈ V.subgroupOf H from hv))
      rw [←subgroupOf_normalizer_eq hVH] at hh
      exact hh
    rintro _ ⟨v,hv,rfl⟩ u hu
    exact Subtype.ext (hweak g g.property hn
      (mem_map_of_mem (MulAut.conj (g : G)).toMonoidHom hv) u hu)
  obtain ⟨hcenter,hEA,hVQ,hEV⟩ := extraspecial_spans_of_emptyLf_and_omega_bound
    T H hTH hc hempty (V.subgroupOf H) (A.subgroupOf H) Z (S.subgroupOf H)
    hAQ' hAS' hOmegaS' hZQ hZcenter hZcard' hZsyl hPhi hcomm' hsmall' hQV' hweak'
  refine ⟨?_,?_,?_,?_⟩
  · have hm := map_mono (f := H.subtype) hcenter
    rw [map_localSpan_subgroupOf A H hAH,
      map_subgroup_center_eq H.subtype H.subtype_injective, hOmap] at hm
    exact hm
  · let := hEA
    rw [←map_localSpan_subgroupOf A H hAH]
    exact IsElementaryAbelian.map H.subtype
  · have hm := map_mono (f := H.subtype) hVQ
    rw [map_localSpan_subgroupOf V H hVH] at hm
    exact hm
  · let := hEV
    rw [←map_localSpan_subgroupOf V H hVH]
    exact IsElementaryAbelian.map H.subtype

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness
