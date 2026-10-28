module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.CoverGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.FullAmbient
/-!
# Terminal symplectic geometry with the central attachment retained

Fixed-point lifting on the actual symplectic cover replaces the former
injectivity assumption on V → V/C_V(L). Alignment gives the centralizer
bound and V₂ ≤ [V,A]V₁. Every G₁-conjugate of V contains V₁, so this is
enough to identify V ∩ Vᵍ = V₂. Carrying V₁ through the reverse calculation
then supplies the original transporter in N_G(V₂).

The faithful full action has kernel O₂(L) before the block step. Its two
local radical images therefore give the R₂ displacement and R₁ separation
without O₂(L)=V. The resulting noncommuting contradiction retains the
original unique noncentral L₂ component. The final theorem combines it
with the established commuting branch, whose core-identification premise
remains explicit. Neither C_V(L)=1 nor K=L₁ is assumed.

Source: Aschbacher--Smith 11.5.7, printed pp.783--784, with the central-cover
fixed-point lifting of I.2.3(1). Final source assembly remains with
qt-d-1222-natural-closure-sp4.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Representation
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (m : MarkedFlag E)

/-- A fixed vector of the original natural quotient has every lift fixed. -/
theorem component_fixed_of_projection_fixed (l : L) (x : V)
    (hx : (LocalGeometry.Coordinates.sp4 m.action).projection
        (V.normalizerMonoidHom (inclusion D.normalizes l) x) =
      (LocalGeometry.Coordinates.sp4 m.action).projection x) :
    V.normalizerMonoidHom (inclusion D.normalizes l) x = x := by
  let w := (D.spaceEquiv.symm x).toAdd
  have he := (LocalGeometry.Coordinates.sp4 m.action).projection_component_conjugation l x
  change ((LocalGeometry.Coordinates.sp4 m.action).projection
    (V.normalizerMonoidHom (inclusion D.normalizes l) x)).toAdd =
    (toLinear (PointModel.quotientMap m l))
      ((LocalGeometry.Coordinates.sp4 m.action).projection x).toAdd at he
  have hf : PointModel.quotientMap m l • CoverGeometry.projection m w =
      CoverGeometry.projection m w := by
    change (toLinear (PointModel.quotientMap m l))
      ((LocalGeometry.Coordinates.sp4 m.action).projection x).toAdd = _
    rw [← he, hx]
    rfl
  have hh := CoverGeometry.fixed_of_projection_fixed m (PointModel.quotientMap m l) w hf
  have hs := congrArg (fun v : D.space =>
    CoverGeometry.spaceMap (D := D) (Multiplicative.ofAdd v)) hh
  rw [CoverGeometry.spaceMap_action] at hs
  have hw : CoverGeometry.spaceMap (D := D) (Multiplicative.ofAdd w) = x.val :=
    congrArg Subtype.val (D.spaceEquiv.apply_symm_apply x)
  rw [hw] at hs
  exact Subtype.ext hs

/-- A realized symplectic action fixes every lift of a fixed coordinate vector. -/
theorem realizes_fixed_of_projection_fixed (s : Sp E.input.field.Carrier)
    (a : normalizer (V : Set G)) (b : Sp E.input.field.Carrier)
    (hr : Realizes (markedProjection E m s) a b) (x : V)
    (hx : b • (markedProjection E m s x).toAdd = (markedProjection E m s x).toAdd) :
    V.normalizerMonoidHom a x = x := by
  obtain ⟨l,hl⟩ := m.action.groupEquiv.surjective.comp
    (QuotientGroup.mk'_surjective (pCore 2 L)) (s⁻¹*b*s)
  change PointModel.quotientMap m l = s⁻¹*b*s at hl
  have he : V.normalizerMonoidHom a =
      V.normalizerMonoidHom (inclusion D.normalizes l) := by
    apply RadicalAction.FullAmbient.full_action_eq_of_projection_eq m
    intro v
    apply Multiplicative.toAdd.injective
    apply (toLinear s).injective
    have h := hr v
    change (toLinear s) ((LocalGeometry.Coordinates.sp4 m.action).projection
      (V.normalizerMonoidHom a v)).toAdd = _ at h
    rw [h, (LocalGeometry.Coordinates.sp4 m.action).projection_component_conjugation]
    change (toLinear b) ((toLinear s)
      ((LocalGeometry.Coordinates.sp4 m.action).projection v).toAdd) =
      (toLinear s) ((toLinear (PointModel.quotientMap m l))
        ((LocalGeometry.Coordinates.sp4 m.action).projection v).toAdd)
    rw [hl]
    simp only [map_mul,map_inv,LinearEquiv.mul_apply]
    exact ((toLinear s).apply_symm_apply _).symm
  rw [he]
  apply component_fixed_of_projection_fixed m
  apply Multiplicative.toAdd.injective
  apply (toLinear s).injective
  have h := hr x
  rw [hx,he] at h
  exact h

namespace PointCoordinates
variable {m : MarkedFlag E} (p : PointCoordinates E m)
include p
/-- Align an escaping radical element on the full cover. Its displacement,
together with the original point, contains the entire plane preimage. -/
theorem align_mod_point (A : Subgroup G) (hA : A ≤ E.R₁)
    (hz : ¬ A ≤ centralizer (E.V₃ : Set G)) :
    ∃ l ∈ E.L₁,
      V ⊓ centralizer (A.map (MulAut.conj l).toMonoidHom : Set G) ≤ E.V₂ ∧
      E.V₂ ≤ ⁅V,A.map (MulAut.conj l).toMonoidHom⁆ ⊔ E.V₁ := by
  let π := markedProjection E m p.basis
  obtain ⟨a,ha,han⟩ : ∃ a ∈ A, a ∉ centralizer (E.V₃ : Set G) := by
    simpa only [SetLike.le_def,not_forall,exists_prop] using hz
  let aN : normalizer (V : Set G) := ⟨a,radical_normalizes_seed E (hA ha)⟩
  obtain ⟨u,v,z,hr⟩ := p.radical ⟨a,hA ha⟩
  have huv : u ≠ 0 ∨ v ≠ 0 := by
    by_contra! huv
    apply han
    intro x hx
    have hxV := D.centralQuotientPreimage_le E.threeSpace hx
    let xV : V := ⟨x,hxV⟩
    have he : V.normalizerMonoidHom aN xV = xV := by
      apply realizes_fixed_of_projection_fixed m p.basis aN _ hr
      rw [huv.1,huv.2]
      exact PlaneModel.central_fixes_three z _ ((p.three xV).mp hx)
    have he' : a*x*a⁻¹=x := congrArg Subtype.val he
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  obtain ⟨b,hb⟩ := PlaneModel.align_radical u v z huv
  obtain ⟨l,hl⟩ := p.levi b
  let lN : normalizer (V : Set G) := ⟨l.val,D.normalizes (E.L₁_le l.property)⟩
  let a' : normalizer (V : Set G) := lN*aN*lN⁻¹
  have hrep : Realizes π a' (PlaneModel.radical 1 0 z) := by
    have he := hl.conj hr
    rw [hb] at he
    exact he
  have ha' : a'.val ∈ A.map (MulAut.conj l.val).toMonoidHom :=
    mem_map_of_mem (MulAut.conj l.val).toMonoidHom ha
  refine ⟨l.val,l.property,?_,?_⟩
  · rintro x ⟨hx,hxc⟩
    let xV : V := ⟨x,hx⟩
    apply (p.plane xV).mpr
    apply (PlaneModel.aligned_fixed z _).mp
    rw [←hrep]
    change (π (V.normalizerMonoidHom a' xV)).toAdd = (π xV).toAdd
    apply congrArg (fun t : V => (π t).toAdd)
    apply Subtype.ext
    change a'.val*x*a'.val⁻¹=x
    rw [hxc a'.val ha',mul_inv_cancel_right]
  · intro x hx
    have hxV := D.centralQuotientPreimage_le E.plane hx
    let xV : V := ⟨x,hxV⟩
    obtain ⟨w,hw⟩ := PlaneModel.aligned_displacement z (π xV).toAdd ((p.plane xV).mp hx)
    obtain ⟨y,hy⟩ := markedProjection_surjective E m p.basis (Multiplicative.ofAdd w)
    change π y = Multiplicative.ofAdd w at hy
    let d : V := V.normalizerMonoidHom a' y * y⁻¹
    have he : π d = π xV := by
      apply Multiplicative.toAdd.injective
      change (π (V.normalizerMonoidHom a' y * y⁻¹)).toAdd = _
      rw [map_mul,map_inv,toAdd_mul,toAdd_inv,hrep]
      simpa only [hy,toAdd_ofAdd,sub_eq_add_neg] using hw
    have hmem : d.val ∈ ⁅V,A.map (MulAut.conj l.val).toMonoidHom⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator ha' y.property
    let k : V := xV*d⁻¹
    have hk : (k : G) ∈ E.V₁ := by
      apply (p.point k).mpr
      have hπ : π k = 1 := by
        change π (xV*d⁻¹) = 1
        rw [map_mul,map_inv,he,mul_inv_cancel]
      change (π k).toAdd ∈ _
      rw [hπ]
      exact Submodule.zero_mem _
    have hh := (⁅V,A.map (MulAut.conj l.val).toMonoidHom⁆ ⊔ E.V₁).mul_mem
      (mem_sup_right hk) (mem_sup_left hmem)
    change x*d.val⁻¹*d.val ∈ _ at hh
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh


end PointCoordinates
/-- The marked point is contained in every relevant conjugate of the seed. -/
theorem point_le_conjugate {g : G} (hg : g ∈ E.G₁) :
    E.V₁ ≤ V.map (MulAut.conj g).toMonoidHom := by
  have hp := mem_normalizer_iff_map_conj_eq.mp hg
  exact hp.symm.le.trans (map_mono E.V₁_le)

/-- The point absorbs the central attachment in the displacement sandwich. -/
theorem intersection_eq_plane_mod_point (hn : E.W ≤ normalizer (V : Set G))
    {g : G} (hg : g ∈ E.G₁)
    (hfixed : V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) ≤ E.V₂)
    (hmoved : E.V₂ ≤ ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔ E.V₁) :
    V ⊓ V.map (MulAut.conj g).toMonoidHom = E.V₂ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔ E.V₁ = E.V₂ := by
  let := D.elementary
  let : IsMulCommutative (V.map (MulAut.conj g).toMonoidHom) := inferInstance
  have hi : V ⊓ V.map (MulAut.conj g).toMonoidHom ≤ E.V₂ :=
    (inf_le_inf_left V (V.map (MulAut.conj g).toMonoidHom).le_centralizer).trans hfixed
  have hc : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔ E.V₁ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom :=
    sup_le (commutator_le_intersection E hn hg)
      (le_inf E.V₁_le (point_le_conjugate (E := E) hg))
  exact ⟨le_antisymm hi (hmoved.trans hc),le_antisymm (hc.trans hi) hmoved⟩

omit [Finite G] in
private theorem conjugate_cancel_cover (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [he,map_id]

private theorem plane_not_le_point (m : MarkedFlag E) : ¬ E.V₂ ≤ E.V₁ := by
  intro h
  rw [m.plane_preimage,m.point_preimage] at h
  have hs := (LocalGeometry.Coordinates.sp4 m.action).preimage_le_iff _ _ |>.mp h
  let : Module.Finite E.input.field.Carrier
      (LocalGeometry.Coordinates.sp4 m.action).Space :=
    inferInstanceAs (Module.Finite E.input.field.Carrier (Vector E.input.field.Carrier))
  have hn := Submodule.finrank_mono hs
  rw [m.flag.dimension 1,m.flag.dimension 0] at hn
  norm_num at hn

namespace PointCoordinates
variable {m : MarkedFlag E} (p : PointCoordinates E m)
include p

/-- The reverse-plane calculation retains V₁ in both displacement equations. -/
theorem reverse_plane_mod_point (hcore : E.W ≤ E.G₁.pCoreIn 2)
    (g : G) (hg : g ∈ E.G₁)
    (hd : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔ E.V₁ = E.V₂) :
    ∃ l ∈ L,
      (E.V₂.map (MulAut.conj l).toMonoidHom).map (MulAut.conj g).toMonoidHom = E.V₂ := by
  let A := V.map (MulAut.conj g⁻¹).toMonoidHom
  have hA : A ≤ E.W := by
    rintro _ ⟨v,hv,rfl⟩
    exact subset_closure ⟨g⁻¹,E.G₁.inv_mem hg,v,hv,rfl⟩
  have hAR : A ≤ E.R₁ := hA.trans (closure_le_R₁ E m hcore)
  have hp : E.V₁.map (MulAut.conj g⁻¹).toMonoidHom = E.V₁ :=
    mem_normalizer_iff_map_conj_eq.mp (E.G₁.inv_mem hg)
  have hback : ⁅V,A⁆ ⊔ E.V₁ = E.V₂.map (MulAut.conj g⁻¹).toMonoidHom := by
    have he := congrArg (map (MulAut.conj g⁻¹).toMonoidHom) hd
    rw [Subgroup.map_sup,map_commutator,conjugate_cancel_cover,commutator_comm,hp] at he
    exact he
  have hbad : ¬ A ≤ centralizer (E.V₃ : Set G) := by
    intro hz
    have he : E.V₂.map (MulAut.conj g⁻¹).toMonoidHom ≤ E.V₁ := by
      rw [←hback]
      exact sup_le (p.commutator_le_point A hAR hz) le_rfl
    have he' := map_mono (f := (MulAut.conj g).toMonoidHom) he
    have hp' : E.V₁.map (MulAut.conj g).toMonoidHom = E.V₁ :=
      mem_normalizer_iff_map_conj_eq.mp hg
    have hcancel : (E.V₂.map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj g).toMonoidHom = E.V₂ := by
      simpa only [inv_inv] using conjugate_cancel_cover E.V₂ g⁻¹
    rw [hcancel,hp'] at he'
    exact plane_not_le_point m he'
  obtain ⟨l,hl,hf,hm⟩ := p.align_mod_point A hAR hbad
  have hlg : l*g⁻¹ ∈ E.G₁ := E.G₁.mul_mem
    (((residualIn_le _).trans inf_le_right) hl) (E.G₁.inv_mem hg)
  have hmap : V.map (MulAut.conj (l*g⁻¹)).toMonoidHom =
      A.map (MulAut.conj l).toMonoidHom := by
    rw [map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  have hplane := (intersection_eq_plane_mod_point (E := E)
    (closure_normalizes_seed E m hcore) hlg (by rwa [hmap]) (by rwa [hmap])).2
  rw [hmap] at hplane
  have hVl : V.map (MulAut.conj l).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (D.normalizes (E.L₁_le hl))
  have hpl : E.V₁.map (MulAut.conj l).toMonoidHom = E.V₁ :=
    mem_normalizer_iff_map_conj_eq.mp (E.L₁_le_G₁ hl)
  have he : (E.V₂.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj l).toMonoidHom = E.V₂ := by
    rw [←hback,Subgroup.map_sup,map_commutator,hVl,hpl,hplane]
  have he' := congrArg (map (MulAut.conj l⁻¹).toMonoidHom) he
  rw [conjugate_cancel_cover] at he'
  refine ⟨l⁻¹,L.inv_mem (E.L₁_le hl),?_⟩
  rw [←he']
  simpa only [inv_inv] using conjugate_cancel_cover E.V₂ g⁻¹
end PointCoordinates
namespace RadicalGeometry
open LocalGeometry
/-- The local core bounds use the faithful full-cover action; they require no
identification of the component core with the chosen seed. -/
theorem local_action_core_bounds_cover (m : MarkedFlag E)
    (U : Subgroup G) (hT : (T : Subgroup G) ≤ normalizer (U : Set G)) :
    let J := actionImage (V := V) (localResidual L U)
    let Q := actionImage (V := V) (localRadical T L U)
    J ≤ normalizer (Q : Set (MulAut V)) ∧
    J.pCoreIn 2 ≤ Q ∧ ⁅Q,J⁆ ≤ J.pCoreIn 2 ∧ IsPGroup 2 Q := by
  dsimp only
  obtain ⟨hLN,hRN,hLR,hRL,hcoreR⟩ := local_normalizations (E := E) U hT
  have hLR' := actionImage_normalizes _ _ hLN hRN hLR
  have hRL' := actionImage_normalizes _ _ hRN hLN hRL
  have htwo := actionImage_two (V := V) (localRadical T L U)
    (isPGroup_pCoreIn 2 (localResidual L U ⊔ (T : Subgroup G)))
  refine ⟨hLR', ?_, commutator_le_localCore _ _ htwo hLR' hRL', htwo⟩
  rw [← FullAction.core_image m _ ((localResidual_le U).trans inf_le_left)]
  exact actionImage_mono hcoreR

/-- The calculation for a common faithful model of the two literal local action images. -/
theorem displacement_of_local_images_cover (m : MarkedFlag E)
    (j : Sp E.input.field.Carrier →* MulAut V) (hj : Function.Injective j)
    (hpoint : (pointLocal (F := E.input.field.Carrier)).map j = actionImage (V := V) E.L₁)
    (hplane : (planeLocal (F := E.input.field.Carrier)).map j = actionImage (V := V) E.L₂) :
    RadicalDisplacement E := by
  have hT1 : (T : Subgroup G) ≤ normalizer (E.V₁ : Set G) := m.sylow_le_point_normalizer
  have hT2 : (T : Subgroup G) ≤ normalizer (E.V₂ : Set G) := by
    rw [m.plane_preimage]
    exact m.flag.invariant 1
  obtain ⟨hn1,_,_,htwo1⟩ := local_action_core_bounds_cover m E.V₁ hT1
  obtain ⟨_,hcore2,hcomm2,_⟩ := local_action_core_bounds_cover m E.V₂ hT2
  change actionImage (V := V) E.L₁ ≤ normalizer (actionImage (V := V) E.R₁ : Set (MulAut V)) at hn1
  change IsPGroup 2 (actionImage (V := V) E.R₁) at htwo1
  change (actionImage (V := V) E.L₂).pCoreIn 2 ≤ actionImage (V := V) E.R₂ at hcore2
  change ⁅actionImage (V := V) E.R₂,actionImage (V := V) E.L₂⁆ ≤
    (actionImage (V := V) E.L₂).pCoreIn 2 at hcomm2
  have hc1 : (actionImage (V := V) E.L₁).pCoreIn 2 = (pointRadical (F := E.input.field.Carrier)).map j := by
    rw [← hpoint, ← map_pCoreIn_of_injective 2 _ j hj]
    congr 1
    exact congrArg (Subgroup.map pointLocal.subtype)
      (pointLocal_core_eq E.input.field.card_eq E.input.nonbinary)
  have hc2 : (actionImage (V := V) E.L₂).pCoreIn 2 = (planeRadical (F := E.input.field.Carrier)).map j := by
    rw [← hplane, ← map_pCoreIn_of_injective 2 _ j hj]
    congr 1
    exact congrArg (Subgroup.map planeLocal.subtype)
      (planeLocal_core_eq E.input.field.card_eq E.input.nonbinary)
  let jp := j.comp (planeLocal (F := E.input.field.Carrier)).subtype
  have hjp : Function.Injective jp := hj.comp Subtype.val_injective
  have hrange : jp.range = actionImage (V := V) E.L₂ := by
    rw [MonoidHom.range_comp, range_subtype]
    exact hplane
  have hrad : Plane.radical.map jp = (planeRadical (F := E.input.field.Carrier)).map j := by
    rw [map_map]
  have hmove : ⁅(planeRadical (F := E.input.field.Carrier)).map j,
      actionImage (V := V) E.L₂⁆ = (planeRadical (F := E.input.field.Carrier)).map j := by
    rw [← hrad, ← hrange, MonoidHom.range_eq_map, ← map_commutator,
      Plane.radical_commutator_eq E.input.field.card_eq E.input.nonbinary]
  have hd : ⁅actionImage (V := V) E.R₂,actionImage (V := V) E.L₂⁆ =
      (planeRadical (F := E.input.field.Carrier)).map j := by
    refine le_antisymm (hcomm2.trans hc2.le) ?_
    rw [← hmove]
    exact commutator_mono (hc2.symm.le.trans hcore2) le_rfl
  refine ⟨?_, ?_⟩
  · intro B hB hm hne
    rw [hd]
    have hBrad : B ≤ Plane.radical.map jp := by
      rw [hrad, ← hd]
      exact hm.symm.le.trans (commutator_mono hB le_rfl)
    rw [← hrange] at hm
    exact (plane_moved_image E.input.field.card_eq E.input.nonbinary jp hjp B hBrad hm hne).trans hrad
  · rw [hd]
    intro hR
    have hJ : (planeRadical (F := E.input.field.Carrier)).map j ≤ actionImage (V := V) E.L₁ := by
      rw [← hpoint]
      exact map_mono planeRadical_le_pointLocal
    have hc := (le_inf hR hJ).trans (inf_le_localCore _ _ htwo1 hn1)
    rw [hc1] at hc
    exact planeRadical_not_le_pointRadical ((map_le_map_iff_of_injective hj).mp hc)

end RadicalGeometry

/-- The same literal quotient markings give radical separation on the entire
chosen cover before identifying O₂(L) with V. -/
theorem radicalDisplacement_cover (m : MarkedFlag E)
    (σ : MulAut (Sp E.input.field.Carrier))
    (hpoint : (E.L₁.subgroupOf L).map
      (σ.toMonoidHom.comp (RadicalGeometry.componentQuotient m)) = pointLocal)
    (hplane : (E.L₂.subgroupOf L).map
      (σ.toMonoidHom.comp (RadicalGeometry.componentQuotient m)) = planeLocal) :
    RadicalDisplacement E := by
  let j := (FullAction.modelHom m).comp σ.symm.toMonoidHom
  have him (A : Subgroup G) (hA : A ≤ L) :
      (((A.subgroupOf L).map (σ.toMonoidHom.comp
        (RadicalGeometry.componentQuotient m))).map j) = actionImage (V := V) A := by
    rw [← FullAction.image_eq m A hA,PointModel.image,map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro l
    exact congrArg (FullAction.modelHom m) (σ.symm_apply_apply _)
  apply RadicalGeometry.displacement_of_local_images_cover m j
    ((FullAction.modelHom_injective m).comp σ.symm.injective)
  · rw [← hpoint]
    exact him E.L₁ E.L₁_le
  · rw [← hplane]
    exact him E.L₂ ((residualIn_le _).trans inf_le_left)

/-- A moving conjugate determines the literal intersection plane, with its
central attachment retained in the point factor. -/
theorem exists_crossing_plane_cover (m : MarkedFlag E) (p : PointCoordinates E m)
    (hcore : E.W ≤ E.G₁.pCoreIn 2) (hc : ⁅V,E.U⁆ ≠ ⊥) :
    ∃ g ∈ E.G₁, V ⊓ V.map (MulAut.conj g).toMonoidHom = E.V₂ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔ E.V₁ = E.V₂ := by
  obtain ⟨g,hg,hm⟩ := exists_conjugate_moving_threeSpace E hc
  have hn := closure_normalizes_seed E m hcore
  have hA : V.map (MulAut.conj g).toMonoidHom ≤ E.W := by
    rintro _ ⟨v,hv,rfl⟩
    exact subset_closure ⟨g,hg,v,hv,rfl⟩
  obtain ⟨l,hl,hf,hd⟩ := p.align_mod_point _ (hA.trans (closure_le_R₁ E m hcore)) hm
  have he : V.map (MulAut.conj (l*g)).toMonoidHom =
      (V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj l).toMonoidHom := by
    rw [map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mul_inv_rev, mul_assoc]
  have hlg : l*g ∈ E.G₁ := E.G₁.mul_mem (E.L₁_le_G₁ hl) hg
  refine ⟨l*g,hlg,intersection_eq_plane_mod_point (E := E) hn hlg ?_ ?_⟩
  · rwa [he]
  · rwa [he]

/-- The original V₂ normalizer contradiction works for every central cover. -/
theorem noncommuting_impossible_cover (m : MarkedFlag E) (p : PointCoordinates E m)
    (r : RadicalDisplacement E) (hcore : E.W ≤ E.G₁.pCoreIn 2)
    (hu : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved : ⁅V,E.L₂⁆ = V) (hc : ⁅V,E.U⁆ ≠ ⊥) : False := by
  obtain ⟨g,hg,_,hd⟩ := exists_crossing_plane_cover m p hcore hc
  obtain ⟨_,_,he,hn⟩ := plane_rechoice_moved E hu hmoved g
    (p.reverse_plane_mod_point hcore g hg hd)
  rw [he] at hn
  have hA : V.map (MulAut.conj g).toMonoidHom ≤ E.W := by
    rintro _ ⟨v,hv,rfl⟩
    exact subset_closure ⟨g,hg,v,hv,rfl⟩
  have hne : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
    intro hz
    have hb := commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hz)
    rw [hb,bot_sup_eq] at hd
    exact plane_not_le_point m hd.symm.le
  exact false_of_moved_seed E m r _ (hA.trans (closure_le_R₁ E m hcore))
    (hA.trans (closure_normalizes_seed E m hcore)) hn hne

/-- Both terminal branches, retaining the original full chosen module and
using only the preceding local markings and intermediate core conclusion. -/
theorem abelian_of_source_geometry_cover (m : MarkedFlag E)
    (p : PointCoordinates E m) (hcore : L.pCoreIn 2 = V)
    (σ : MulAut (Sp E.input.field.Carrier))
    (hpoint : (E.L₁.subgroupOf L).map
      (σ.toMonoidHom.comp (RadicalGeometry.componentQuotient m)) = pointLocal)
    (hplane : (E.L₂.subgroupOf L).map
      (σ.toMonoidHom.comp (RadicalGeometry.componentQuotient m)) = planeLocal)
    (hW : E.W ≤ E.G₁.pCoreIn 2) (hU : IsMulCommutative E.U)
    (hunique : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved₁ : ⁅V,E.L₁⁆ = E.V₃) (hmoved₂ : ⁅V,E.L₂⁆ = V)
    (hTI : ∀ g ∈ E.M,
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hcontrol : normalizer (E.V₃ : Set G) ⊓ normalizer (E.L₁ : Set G) ≤ E.M)
    (hroot : ¬ IsMulCommutative E.W → ⁅V,E.U⁆ = ⊥ →
      actionImage (V := V) E.W ≤ centralizer (actionImage (V := V) E.L₁ : Set (MulAut V))) :
    IsMulCommutative E.W := by
  by_contra hn
  by_cases hc : ⁅V,E.U⁆ = ⊥
  · exact hn (abelian_of_source_commuting E m hcore hU hc
      (root_action_commutator_le_core E m hW (hroot hn hc)) hmoved₁
      hTI hgen hcontrol)
  · exact noncommuting_impossible_cover m p
      (radicalDisplacement_cover m σ hpoint hplane)
      hW hunique hmoved₂ hc

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
