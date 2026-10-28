module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsResidualNativeOrdinary
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsGlobalMovedComponent

/-!
# The actual common residual forces an ordinary singular overcomponent

The full central covering map is restricted to the original component
centralizer. Its kernel is killed only after its actual containment in the
singular two-core has been supplied. The nontrivial residual image then
uses the native involution generation theorem to exclude the nonordinary
SQTK components. All quotients are by the unchanged intrinsic two-cores.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original selected HS residual has a nontrivial image in every
containing C-component modulo the full singular core. If the actual
covering center lies in that core, this component is ordinary. -/
theorem SourceHypothesis.nonsingular_hs_overcomponent_quasisimple
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hZ : ZV L V = ⊥) (z : V) (hz : z ≠ 1)
    (hHz : Gv (z : G) ∈ (D.fullSetup hZ T z).Hz)
    (u : V) (hu : D.Nonsingular u)
    (hC : IsQuasisimple (Kv (u : G)))
    (e : ((Kv (u : G)) ⧸ center (Kv (u : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (u : G)))
    (hzS : (z : G) ∈ (center ((S : Subgroup (Gv (u : G))).map
      (Gv (u : G)).subtype)).map ((S : Subgroup (Gv (u : G))).map
      (Gv (u : G)).subtype).subtype)
    (hznot : (z : G) ∉ centralizer (Kv (u : G) : Set G))
    (hcenter : (center (Kv (u : G))).map (Kv (u : G)).subtype ≤
      (Gv (z : G)).pCoreIn 2)
    {K : Subgroup G} (hKG : K ≤ Gv (z : G))
    (hK : (K.subgroupOf (Gv (z : G))).IsCComponent)
    (hJK : (primeToResidual 3 (Gv (u : G) ⊓ Gv (z : G) : Subgroup G)).map
      (Gv (u : G) ⊓ Gv (z : G)).subtype ≤ K) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  classical
  let C := Kv (u : G)
  let A := (Gv (z : G)).subgroupOf C
  let B := Gv (u : G) ⊓ Gv (z : G)
  let J := (primeToResidual 3 B).map B.subtype
  let R := primeToResidual 3 A
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  let i : A →* G := C.subtype.comp A.subtype
  have hres : R.map i = J := by
    rw [show R.map i = (R.map A.subtype).map C.subtype from (map_map _ _ _).symm,
      map_embedded_primeToResidual_of_hom,subgroupOf_map_subtype,
      inf_comm (Gv (z : G)) C]
    exact H.nonsingular_hs_intersection_primeToResidual D u hu hC e (Gv (z : G))
  obtain ⟨j,hj,hjc,_,_,himage,_,_,_,_,_,_⟩ :=
    H.nonsingular_hs_selected_centralizer_image D u hu hC e S z hzS
      (elemPow_eq_one_of_isElementaryAbelian (z : G) z.property) hznot
  let F := centralizer ({j} : Set Sporadic.LeechRelated.HS.Carrier)
  let f : A →* F := (MulEquiv.subgroupCongr himage).toMonoidHom.comp (q.subgroupMap A)
  have hf : Function.Surjective f := (MulEquiv.subgroupCongr himage).surjective.comp
    (q.subgroupMap_surjective A)
  let R₀ := primeToResidual 3 F
  have hRf : R.map f = R₀ := map_primeToResidual_of_surjective 3 f hf
  let r : R →* R₀ := (MulEquiv.subgroupCongr hRf).toMonoidHom.comp (f.subgroupMap R)
  have hr : Function.Surjective r := (MulEquiv.subgroupCongr hRf).surjective.comp
    (f.subgroupMap_surjective R)
  let X := Gv (z : G)
  let π := QuotientGroup.mk' (pCore 2 X)
  let K₀ := K.subgroupOf X
  let K₁ := K₀.map π
  let b₀ : R →* K₀ := {
    toFun := fun x => ⟨⟨i x.val,x.val.property⟩,by
      change i x.val ∈ K
      apply hJK
      change i x.val ∈ J
      rw [←hres]
      exact mem_map_of_mem i x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let b : R →* K₁ := (π.subgroupMap K₀).comp b₀
  have hker : r.ker ≤ b.ker := by
    intro x hx
    have hxq : q x.val.val = 1 := congrArg (fun a : R₀ => (a.val : Sporadic.LeechRelated.HS.Carrier)) hx
    have hxZ : x.val.val ∈ center C := by
      have hkq : q.ker = center C := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
      exact hkq ▸ hxq
    have hxcore := hcenter (mem_map_of_mem C.subtype hxZ)
    have hxcore' : (b₀ x).val ∈ pCore 2 X := by
      obtain ⟨y,hy,he⟩ := hxcore
      have hxy : (b₀ x).val = y := Subtype.ext he.symm
      exact hxy.symm ▸ hy
    change b x = 1
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr hxcore'
  let a : R₀ →* K₁ := r.liftOfSurjective hr ⟨b,hker⟩
  have hab (x : R) : a (r x) = b x := by simp [a,MonoidHom.liftOfSurjective]
  have hane : a.range ≠ ⊥ := by
    intro ha
    have hJcore : J ≤ X.pCoreIn 2 := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := hres.symm ▸ hx
      have hb : b ⟨y,hy⟩ = 1 := by
        rw [←hab]
        exact mem_bot.mp (ha ▸ (show a (r ⟨y,hy⟩) ∈ a.range from ⟨r ⟨y,hy⟩,rfl⟩))
      have hh : π (b₀ ⟨y,hy⟩).val = 1 := congrArg Subtype.val hb
      exact mem_map_of_mem X.subtype ((QuotientGroup.eq_one_iff _).mp hh)
    have hm := H.nonsingular_hs_common_residual_moved D u hu hC e S z hzS hznot
    apply hm
    exact (commutator_mono le_rfl hJcore).trans
      (le_normalizer_iff_commutator_le_right.mp
        ((V_le_Gv z).trans (X.le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))))
  let : Group.IsNilpotent (pCore 2 X) := pCore_isPGroup.isNilpotent
  have hK₁ : K₁.IsCComponent := hK.map_quotient _
  have hordinary := OriginalHigmanSimsResidualOrdinary.quasisimple_of_native_residual_image
    (H.original_star_sqtk D hZ z hz hHz) (pCore_quotient_pCore_eq_bot 2) hK₁ j hj hjc a hane
  let eK : K ≃* K₀ := (subgroupOfEquivOfLe hKG).symm
  let d : (K ⧸ pCore 2 K) ≃* K₁ :=
    (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans
      (cComponentTwoCoreQuotientEquiv hK)
  exact hordinary.of_mulEquiv d.symm

end CFSG.Quasithin.Chapter12.Section06
