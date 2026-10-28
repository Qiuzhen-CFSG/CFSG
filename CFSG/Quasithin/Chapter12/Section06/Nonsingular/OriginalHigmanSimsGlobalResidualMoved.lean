module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsGlobalResidualAction

/-!
# The original module moves the literal common HS residual

Restriction to the actual component centralizer retains its full two-core
and central-cover map. The S5 quotient detects any subgroup centralizing
its A5 residual modulo the core. Combined with the native pure-sixteen
obstruction, the original module's commutator with the literal common
residual cannot lie in the singular centralizer's two-core.

Source: the original HS comparison in Aschbacher--Smith 12.6.12,
printed pp.825--826. No common-residual/core equality is assumed.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem selected_moved_not_le_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G)))
    (z : V) (hz : (z : G) ∈ (center ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype)).map ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype).subtype)
    (hznot : (z : G) ∉ centralizer (Kv (v : G) : Set G)) :
    ¬ ((Vv L V (v : G)).subgroupOf (Kv (v : G))) ≤
      ((Gv (z : G)).subgroupOf (Kv (v : G))).pCoreIn 2 := by
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
  intro hWcore
  apply hn
  have hm := map_mono (f := q) hWcore
  rwa [map_pCoreIn_of_ker_isPGroup q hk,himage] at hm

/-- The original V moves the common residual above the whole two-core of
its actual singular centralizer. -/
theorem SourceHypothesis.nonsingular_hs_common_residual_moved
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G)))
    (z : V) (hz : (z : G) ∈ (center ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype)).map ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype).subtype)
    (hznot : (z : G) ∉ centralizer (Kv (v : G) : Set G)) :
    let B := Gv (v : G) ⊓ Gv (z : G)
    let J := (primeToResidual 3 B).map B.subtype
    ¬ ⁅V,J⁆ ≤ (Gv (z : G)).pCoreIn 2 := by
  let C := Kv (v : G)
  let A := (Gv (z : G)).subgroupOf C
  let U := ((Vv L V (v : G)).subgroupOf C).subgroupOf A
  let f : A →* Gv (z : G) := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : Gv (z : G) => (a : G)) hh
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  obtain ⟨j,hj,hjc,_,_,himage,_,_,_,_,_,_⟩ :=
    H.nonsingular_hs_selected_centralizer_image D v hv hK e S z hz
      (elemPow_eq_one_of_isElementaryAbelian (z : G) z.property) hznot
  let F := centralizer ({j} : Set Sporadic.LeechRelated.HS.Carrier)
  let r : A →* F := (MulEquiv.subgroupCongr himage).toMonoidHom.comp (q.subgroupMap A)
  have hr : Function.Surjective r := (MulEquiv.subgroupCongr himage).surjective.comp
    (q.subgroupMap_surjective A)
  have hqk : q.ker = center C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hk : IsPGroup 2 r.ker := by
    have he : r.ker = (center C).comap A.subtype := by
      ext x
      change (⟨q x.val,?_⟩ : F) = 1 ↔ x.val ∈ center C
      rw [Subtype.ext_iff]
      exact show q x.val = 1 ↔ x.val ∈ center C from by rw [←hqk]; rfl
    rw [he]
    apply IsPGroup.comap_subtype
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [H.nonsingular_hs_ru_center_card D v hv hK (.inl ⟨e⟩)]
    decide
  obtain ⟨d⟩ := OriginalHigmanSimsSingularComponents.twoCentral_core_quotient_symmetricFive j hj hjc
  let eA := (r.pCoreQuotientEquiv hr hk).trans d
  let B := Gv (v : G) ⊓ Gv (z : G)
  let J := (primeToResidual 3 B).map B.subtype
  let i : A →* G := C.subtype.comp A.subtype
  have hres : (primeToResidual 3 A).map i = J := by
    rw [show (primeToResidual 3 A).map i = ((primeToResidual 3 A).map A.subtype).map C.subtype
      from (map_map _ _ _).symm,map_embedded_primeToResidual_of_hom,subgroupOf_map_subtype,
      inf_comm (Gv (z : G)) C]
    exact H.nonsingular_hs_intersection_primeToResidual D v hv hK e (Gv (z : G))
  change ¬ ⁅V,J⁆ ≤ (Gv (z : G)).pCoreIn 2
  intro hc
  have hcore : (pCore 2 (Gv (z : G))).comap f ≤ pCore 2 A :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective f hf⟩
  have hcomm : ⁅U,primeToResidual 3 A⁆ ≤ pCore 2 A := by
    apply le_trans _ hcore
    intro x hx
    have hm : i x ∈ ⁅V,J⁆ := by
      have he := mem_map_of_mem i hx
      rw [map_commutator,hres] at he
      exact (commutator_mono (show U.map i ≤ V from by
        rintro _ ⟨y,hy,rfl⟩
        exact (Vv_le_V H.chosen.normalizes _) hy) le_rfl) he
    have hh := hc hm
    obtain ⟨a,ha,hea⟩ := hh
    have he : f x = a := Subtype.ext hea.symm
    change f x ∈ pCore 2 (Gv (z : G))
    exact he.symm ▸ ha
  have hU := OriginalHigmanSimsGlobal.le_core_of_residual_commutator_le eA U hcomm
  apply selected_moved_not_le_core H D v hv hK e S z hz hznot
  intro x hx
  have hxz : x ∈ A := (V_le_Gv z) ((Vv_le_V H.chosen.normalizes _) hx)
  exact mem_map_of_mem A.subtype (hU (show (⟨x,hxz⟩ : A) ∈ U from hx))

end CFSG.Quasithin.Chapter12.Section06
