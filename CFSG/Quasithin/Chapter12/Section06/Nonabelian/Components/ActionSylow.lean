module
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Components.ActionTransport
public import Theory.GroupTheory.SylowCentralSupplement

/-!
# A Sylow center in the faithful selected-component action

The original component projection maps a Sylow subgroup of K-star onto
a Sylow subgroup of K-hat. If V-star centralizes that original Sylow,
its marked action centralizes the image. Since L₁-hat and V-hat also
centralize V-hat, the full centralizer supplements the normal K-hat.
It therefore has odd index and contains a Sylow two-subgroup of X-hat.
The actual elementary V-hat lies in the center of that Sylow subgroup.

Source: Aschbacher--Smith, condition (*) in 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup.SelectedComponent.ActionMarking
variable {G : Type*} [Group G] [Finite G] {E : Setup G} {H : Subgroup G}
  {c : E.SelectedComponent H} (a : c.ActionMarking)

/-- The marked involution is central in a Sylow of the actual faithful action range. -/
theorem exists_sylow_module_central
    (P : Sylow 2 (star H c.K))
    (hP : star H E.V ≤ centralizer ((P : Subgroup (star H c.K)).map
      (star H c.K).subtype : Set (Hstar H))) :
    let U := ((E.V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
    ∃ S : Sylow 2 a.action.range, U ≤ (S : Subgroup a.action.range) ∧
      U ≤ centralizer (S : Set a.action.range) := by
  let f := a.action.rangeRestrict
  let K := (c.K.subgroupOf c.localActor).map f
  let A := (E.L₁.subgroupOf c.localActor).map f
  let U := (E.V.subgroupOf c.localActor).map f
  let C := centralizer (U : Set a.action.range)
  let : (c.K.subgroupOf c.localActor).Normal := a.component_normal
  let : K.Normal := Subgroup.Normal.map inferInstance f a.action.rangeRestrict_surjective
  have hKX : c.K ≤ c.localActor := le_sup_left.trans le_sup_left
  have hAX : E.L₁ ≤ c.localActor := le_sup_right.trans le_sup_left
  have hVX : E.V ≤ c.localActor := le_sup_right
  have hgen : K ⊔ A ⊔ U = ⊤ := by
    rw [←Subgroup.map_sup,←Subgroup.map_sup]
    rw [←subgroupOf_sup hKX hAX,
      ←subgroupOf_sup (sup_le hKX hAX) hVX]
    change (c.localActor.subgroupOf c.localActor).map f = ⊤
    rw [subgroupOf_self,map_top_of_surjective _ a.action.rangeRestrict_surjective]
  have hAC : A ≤ C := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨v,hv,rfl⟩
    exact Subtype.ext (a.residual_centralizes (mem_map_of_mem a.action hx)
      (a.action v) (mem_map_of_mem a.action hv))
  let : IsElementaryAbelian 2 E.V := E.elementary
  let : IsElementaryAbelian 2 (E.V.subgroupOf c.localActor) := IsElementaryAbelian.subgroupOf hVX
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map f
  have hUC : U ≤ C := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hKC : K ⊔ C = ⊤ := by
    apply top_unique
    rw [←hgen]
    exact sup_le (sup_le le_sup_left (hAC.trans le_sup_right)) (hUC.trans le_sup_right)
  let e := (subgroupOfEquivOfLe
    (show (c.K.subgroupOf c.localActor).map a.action ≤ a.action.range from map_le_range _ _)).symm
  have he : ((c.K.subgroupOf c.localActor).map a.action).subgroupOf a.action.range = K :=
    (a.map_rangeRestrict c.K).symm
  let eK := e.trans (MulEquiv.subgroupCongr he)
  let k : star H c.K →* K := eK.toMonoidHom.comp
    (a.componentQuotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (center (star H c.K))))
  have hk : Function.Surjective k := eK.surjective.comp
    (a.componentQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
  have hconj (b : star H c.K) : ((k b : a.action.range) : MulAut (star H c.K)) = MulAut.conj b :=
    a.componentQuotientEquiv_mk b
  let Q := P.mapSurjective hk
  have hQC : (Q : Subgroup K).map K.subtype ≤ C := by
    rintro _ ⟨_,⟨b,hb,rfl⟩,rfl⟩ _ ⟨v,hv,rfl⟩
    apply Subtype.ext
    change a.action v * ((k b : a.action.range) : MulAut (star H c.K)) =
      ((k b : a.action.range) : MulAut (star H c.K)) * a.action v
    rw [hconj]
    have hfix : a.action v b = b := by
      apply Subtype.ext
      rw [a.conjugation]
      have hvstar : QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le v) ∈ star H E.V :=
        mem_map_of_mem _ hv
      have hcomm := hP hvstar b.val (mem_map_of_mem (star H c.K).subtype hb)
      rw [←hcomm,mul_inv_cancel_right]
    apply MulEquiv.ext
    intro y
    change a.action v (b*y*b⁻¹) = b*a.action v y*b⁻¹
    rw [map_mul,map_mul,map_inv,hfix]
  obtain ⟨S,hSC⟩ := exists_sylow_le_of_normal_supplement K C hKC Q hQC
  have hUS : U ≤ (S : Subgroup a.action.range) := by
    let : (U.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer (Subgroup.centralizer_le_normalizer _)
    have hp : IsPGroup 2 (U.subgroupOf C) :=
      (IsElementaryAbelian.isPGroup 2 U).comap_subtype
    have hle := hp.le_sylow_of_normal (S.subtype hSC)
    intro u hu
    exact hle (show (⟨u,hUC hu⟩ : C) ∈ U.subgroupOf C from hu)
  rw [←a.map_rangeRestrict E.V]
  exact ⟨S,hUS,le_centralizer_iff.mpr hSC⟩

end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup.SelectedComponent.ActionMarking
