module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsCommonCoreSource
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsResidualOuterNative
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsResidualOuterTransfer

/-!
# The native outer involution acts on the actual common-residual star image

The pure sixteen-subgroup supplies an outer witness on the native residual.
It is lifted through the full central covering map. The exact kernel of the
original star map is its whole intrinsic two-core, so the same witness acts
outer on the literal original residual image in the singular quotient.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem normal_quotient_inner_congr
    (A B : Subgroup G) [A.Normal] [B.Normal] (h : A = B) (x : G) :
    normalQuotientAction A (pCore 2 A) x ∈ MulAut.innerSubgroup (A ⧸ pCore 2 A) ↔
      normalQuotientAction B (pCore 2 B) x ∈ MulAut.innerSubgroup (B ⧸ pCore 2 B) := by
  subst B
  rfl

omit [Finite G] in
private theorem normalizer_outer_congr
    (A B : Subgroup G) (h : A = B) (x : G) (hx : x ∈ normalizer (A : Set G))
    (ho : A.normalizerMonoidHom ⟨x,hx⟩ ∉ MulAut.innerSubgroup A) :
    ∃ hy : x ∈ normalizer (B : Set G),
      B.normalizerMonoidHom ⟨x,hy⟩ ∉ MulAut.innerSubgroup B := by
  subst B
  exact ⟨hx,ho⟩

/-- The original moved hyperplane supplies an outer actor on the literal
common-residual image, with the complete singular quotient kernel retained. -/
theorem SourceHypothesis.nonsingular_hs_outer_on_common_star
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (hZ : ZV L V = ⊥)
    (v : V) (hv : D.Nonsingular v) (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G))) (z : V) (hz0 : z ≠ 1)
    (hz : (z : G) ∈ (center ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype)).map ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype).subtype)
    (hznot : (z : G) ∉ centralizer (Kv (v : G) : Set G))
    (hpolar : (D.fullSetup hZ T z).V₅ ≤ (Gv (z : G)).pCoreIn 2) :
    let X := Gv (z : G)
    let B := Gv (v : G) ⊓ X
    let J := (primeToResidual 3 B).map B.subtype
    let Jstar := Nonabelian.Setup.star X J
    ∃ x : X, (x : G) ∈ Vv L V (v : G) ∧
      ∃ hn : QuotientGroup.mk' (pCore 2 X) x ∈ normalizer (Jstar : Set (X ⧸ pCore 2 X)),
        Jstar.normalizerMonoidHom ⟨QuotientGroup.mk' (pCore 2 X) x,hn⟩ ∉
          MulAut.innerSubgroup Jstar := by
  classical
  let C := Kv (v : G)
  let W := (Vv L V (v : G)).subgroupOf C
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  let A := (Gv (z : G)).subgroupOf C
  let a := nonsingularModelAction (v : G) e
  let X := Gv (z : G)
  let i : A →* G := C.subtype.comp A.subtype
  have hWC := (H.nonsingular_component_rank D v hv).1
  have hWA : W ≤ A := fun x hx => (V_le_Gv z) ((Vv_le_V H.chosen.normalizes _) hx)
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
  let F := centralizer ({j} : Set Sporadic.LeechRelated.HS.Carrier)
  let r : A →* F := (MulEquiv.subgroupCongr himage).toMonoidHom.comp (q.subgroupMap A)
  have hr : Function.Surjective r := (MulEquiv.subgroupCongr himage).surjective.comp
    (q.subgroupMap_surjective A)
  have hqk : q.ker = center C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hrk : r.ker = (center C).comap A.subtype := by
    ext x
    change (⟨q x.val,?_⟩ : F) = 1 ↔ x.val ∈ center C
    rw [Subtype.ext_iff]
    exact show q x.val = 1 ↔ x.val ∈ center C from by rw [←hqk]; rfl
  have hk : IsPGroup 2 r.ker := by
    rw [hrk]
    apply IsPGroup.comap_subtype
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [H.nonsingular_hs_ru_center_card D v hv hK (.inl ⟨e⟩)]
    decide
  have hmapW : (W.subgroupOf A).map r = (W.map q).subgroupOf F := by
    ext x
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact mem_map_of_mem q hw
    · rintro ⟨w,hw,hew⟩
      exact ⟨⟨w,hWA hw⟩,hw,Subtype.ext hew⟩
  let R := primeToResidual 3 A
  have hrR : R.map r = primeToResidual 3 F := map_primeToResidual_of_surjective 3 r hr
  obtain ⟨w,hw,houter⟩ := OriginalHigmanSimsResidualOuterNative.pure_sixteen_has_outer_residual_action
    (W.map q) inferInstance hcard hpure j hjW hne
  obtain ⟨x,hx,hxw⟩ := (show w ∈ (W.subgroupOf A).map r from hmapW.symm ▸ hw)
  have houterA : normalQuotientAction R (pCore 2 R) x ∉
      MulAut.innerSubgroup (R ⧸ pCore 2 R) := by
    intro hin
    have hh := (OriginalHigmanSimsResidualOuterTransfer.quotient_action_inner_iff_of_two_kernel
      r hr hk R x).mpr hin
    let : (R.map r).Normal := (inferInstance : R.Normal).map r hr
    have hh' := (normal_quotient_inner_congr (R.map r) (primeToResidual 3 F) hrR (r x)).mp hh
    rw [hxw] at hh'
    exact houter hh'
  let B := Gv (v : G) ⊓ X
  let J := (primeToResidual 3 B).map B.subtype
  have hres : R.map i = J := by
    rw [show R.map i = (R.map A.subtype).map C.subtype from (map_map _ _ _).symm,
      map_embedded_primeToResidual_of_hom,subgroupOf_map_subtype,inf_comm X C]
    exact H.nonsingular_hs_intersection_primeToResidual D v hv hK e X
  have hi : Function.Injective i := C.subtype_injective.comp A.subtype_injective
  have hip : IsPGroup 2 i.ker := by
    rw [i.ker_eq_bot hi]
    exact IsPGroup.of_subsingleton 2 _
  have hJX : J ≤ X := by
    rw [←hres]
    rintro _ ⟨a,_,rfl⟩
    exact a.property
  let iX : A →* X := {
    toFun := fun a => ⟨a.val.val,a.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hiX : Function.Injective iX := fun a b h => Subtype.ext (Subtype.ext
    (congrArg (fun y : X => (y : G)) h))
  let f := (QuotientGroup.mk' (pCore 2 X)).comp iX
  have hJcore := H.nonsingular_hs_common_core_le_singular_core
    D hZ v hv hK e S z hz0 hz hznot hpolar
  have hfk : (f.comp R.subtype).ker = pCore 2 R := by
    have htwo : IsPGroup 2 (f.comp R.subtype).ker := by
      change IsPGroup 2 (((QuotientGroup.mk' (pCore 2 X)).comp
        (iX.comp R.subtype)).ker)
      rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_of_injective _ (hiX.comp R.subtype_injective)
    have hle : (f.comp R.subtype).ker ≤ pCore 2 R := le_sSup ⟨inferInstance,htwo⟩
    apply le_antisymm hle
    intro y hy
    have hyJ : i (y : A) ∈ J.pCoreIn 2 := by
      rw [←hres,←map_pCoreIn_of_ker_isPGroup i hip]
      exact mem_map_of_mem i (mem_map_of_mem R.subtype hy)
    obtain ⟨b,hb,heb⟩ := hJcore hyJ
    change QuotientGroup.mk' (pCore 2 X) (iX (y : A)) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    have he : iX (y : A) = b := Subtype.ext heb.symm
    rwa [he]
  have hRX : R.map iX = J.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hJX]
    exact hres
  have himage : R.map f = Nonabelian.Setup.star X J := by
    rw [show R.map f = (R.map iX).map (QuotientGroup.mk' (pCore 2 X)) from
      (map_map _ _ _).symm,hRX]
    rfl
  have ho := (OriginalHigmanSimsResidualOuterTransfer.image_action_inner_iff f R hfk x).not.mpr houterA
  have hn : f x ∈ normalizer (R.map f : Set (X ⧸ pCore 2 X)) := by
    apply R.le_normalizer_map f
    exact mem_map_of_mem f (by rw [normalizer_eq_top]; exact mem_top x)
  change (R.map f).normalizerMonoidHom ⟨f x,hn⟩ ∉ MulAut.innerSubgroup (R.map f) at ho
  refine ⟨iX x,hx,?_⟩
  exact normalizer_outer_congr _ _ himage (f x) hn ho

end CFSG.Quasithin.Chapter12.Section06
