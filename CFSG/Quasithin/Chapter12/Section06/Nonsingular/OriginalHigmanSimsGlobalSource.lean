module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsGlobalNative
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsImageGeometry
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleHigmanSimsCentralizer
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original HS module escapes the selected singular centralizer core

The actual moved module maps to a pure elementary sixteen-subgroup in HS.
The selected centralizer maps onto the full native point centralizer, with
its entire covering kernel retained. Were the original V contained in the
ambient point centralizer's two-core, restriction and this same map would
put that pure sixteen-subgroup in the native point core, contradicting the
verified native action.

Source: the original HS alternative in Aschbacher--Smith 12.6.12,
printed pp.825--826. This is a source consequence in the contrary branch;
the final global HS exclusion remains separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- For the actual selected HS point centralizer, the original full module
does not lie in its intrinsic two-core. No ambient component assumption or
nonsingular-centralizer control is used. -/
theorem SourceHypothesis.nonsingular_hs_selected_module_not_le_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G)))
    (z : V) (hz : (z : G) ∈ (center ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype)).map ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype).subtype)
    (hznot : (z : G) ∉ centralizer (Kv (v : G) : Set G)) :
    ¬ V ≤ (Gv (z : G)).pCoreIn 2 := by
  let C := Kv (v : G)
  let W := (Vv L V (v : G)).subgroupOf C
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  let B := (Gv (z : G)).subgroupOf C
  let a := nonsingularModelAction (v : G) e
  have hWC := (H.nonsingular_component_rank D v hv).1
  obtain ⟨j,hj,_,ha,_,himage,_,_,_,_,_,_⟩ :=
    H.nonsingular_hs_selected_centralizer_image D v hv hK e S z hz
      (elemPow_eq_one_of_isElementaryAbelian (z : G) z.property) hznot
  have hjW : j ∈ W.map q := by
    have hjE : MulAut.conj j ∈ (V.subgroupOf (Gv (v : G))).map a := by
      rw [←ha ((V_le_Gv v) z.property)]
      exact mem_map_of_mem a z.property
    have hi := (H.nonsingular_hs_original_inner_part D v hv hK e).2.2.1
    have hh : MulAut.conj j ∈ ((Vv L V (v : G)).subgroupOf (Gv (v : G))).map a :=
      hi ▸ ⟨hjE,⟨j,rfl⟩⟩
    rw [nonsingularModelAction_map (v : G) e _ hWC] at hh
    obtain ⟨y,⟨x,hx,rfl⟩,hxj⟩ := hh
    exact ⟨x,hx,(MulAut.conj_injective_of_center_eq_bot
      Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot) hxj⟩
  let := Vv_elementary H.chosen.normalizes (v : G)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hWC
  let : IsElementaryAbelian 2 (W.map q) := IsElementaryAbelian.map q
  have hcard : Nat.card (W.map q) = 16 := by
    rw [show W.map q = (W.map (QuotientGroup.mk' (center C))).map e.toMonoidHom from
      (map_map _ _ _).symm,card_map_of_injective e.injective]
    exact H.nonsingular_hs_moved_image_card D v hv ⟨e⟩
  obtain ⟨p,hp⟩ := H.nonsingular_hs_moved_image_fixed_point D v hv hK e
  have hpure : ∀ x ∈ W.map q, ∃ p : Fin 100, (x : Equiv.Perm (Fin 100)) p = p := by
    rintro x ⟨y,hy,rfl⟩
    exact ⟨p,hp y hy⟩
  have hne : j ≠ 1 := by
    intro hh
    rw [hh,orderOf_one] at hj
    omega
  have hn := OriginalHigmanSimsGlobalNative.pure_sixteen_not_le_point_core
    (W.map q) inferInstance hcard hpure j hjW hne
  have hqker : q.ker = center C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hk : IsPGroup 2 q.ker := by
    rw [hqker]
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [H.nonsingular_hs_ru_center_card D v hv hK (.inl ⟨e⟩)]
    decide
  intro hV
  have hWcore : W ≤ B.pCoreIn 2 := by
    have hB : B = (C ⊓ Gv (z : G)).subgroupOf C := by
      ext x
      exact ⟨fun hx => ⟨x.property,hx⟩,fun hx => hx.2⟩
    rw [hB,pCoreIn_subgroupOf 2 _ C inf_le_left]
    intro x hx
    exact (inf_pCoreIn_le_of_le 2 (show C ⊓ Gv (z : G) ≤ Gv (z : G) from inf_le_right))
      ⟨⟨x.property,(V_le_Gv z) ((Vv_le_V H.chosen.normalizes _) hx)⟩,
        hV ((Vv_le_V H.chosen.normalizes _) hx)⟩
  apply hn
  have hm := map_mono (f := q) hWcore
  rwa [map_pCoreIn_of_ker_isPGroup q hk,himage] at hm

end CFSG.Quasithin.Chapter12.Section06
