module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.PointExchange
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Actions
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.PointStabilizer
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Actions

/-!
# The original selected involution interchanges the orthogonal factors

The faithful action on H/O₂(H) is expressed in the supplied determinant
coordinates. The original conjugate actor is a two-group normal in the full
stabilizer of the marked binary point. That point is singular, and the same
F₄-line is V/Z(U). If the selected involution fixed this line pointwise,
the two disjoint commutator lines would force it to centralize V.

PointExchange therefore proves interchange of the two actual SL₂(4) factors.
The final application keeps the original selection i=zˣ, x=gkg, and its
literal subgroup memberships. No interchange premise is added. The diagonal
moved-module identification and marked-catalogue assembly remain subsequent
source obligations.

The private import of Actions is an intentional internal proof split: it
identifies the same previously constructed action without exposing its body.
Source: Aschbacher--Smith, Lemma 14.4.9, printed pp.1009--1010;
refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension CoreGeometry ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable [IsMulCommutative V]
local instance (F : InvariantFlag T V 3) : (F.U.subgroupOf F.H).Normal := F.U_normal

/-- The faithful star action in the original supplied determinant coordinates. -/
private def sourceStarAction (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hk : F.terminalHatAction.ker = pCore 2 F.H)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F) :
    (F.H ⧸ pCore 2 F.H) →* (Binary.V ≃ₗ[ZMod 2] Binary.V) :=
  let E := e.trans Binary.binaryCoordinates
  let ρ : Representation (ZMod 2) (F.H ⧸ pCore 2 F.H) Binary.V :=
    E.conjRingEquiv.toMonoidHom.comp (sourceAction F hk).representation
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Binary.V).toMonoidHom.comp ρ.asGroupHom

omit [Finite G] in
private theorem sourceStarAction_apply (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hk : F.terminalHatAction.ker = pCore 2 F.H)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (a : F.H ⧸ pCore 2 F.H) (v : Additive F.Uhat) :
    sourceStarAction F hk e a ((e.trans Binary.binaryCoordinates) v) =
      (e.trans Binary.binaryCoordinates) ((sourceAction F hk).representation a v) := by
  change (e.trans Binary.binaryCoordinates)
    ((sourceAction F hk).representation a ((e.trans Binary.binaryCoordinates).symm
      ((e.trans Binary.binaryCoordinates) v))) = _
  rw [LinearEquiv.symm_apply_apply]

omit [Finite G] in
private theorem sourceStarAction_injective (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hk : F.terminalHatAction.ker = pCore 2 F.H)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F) :
    Function.Injective (sourceStarAction F hk e) := by
  intro a b hab
  apply (sourceAction F hk).faithful
  apply LinearMap.ext
  intro v
  apply (e.trans Binary.binaryCoordinates).injective
  rw [←sourceStarAction_apply,←sourceStarAction_apply,hab]

/-- Relative normality in the original point stabilizer forces the selected
involution to interchange the two actual SL₂(4) factors. -/
private theorem source_orthogonal_selected_swaps (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (i : F.H) (hiX : (i:G) ∈ F.X g)
    (hiV : (i:G) ∉ centralizer (V : Set G)) :
    Binary.InvolutionResidual.SwapsFactors
      (sourceStarAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)
        e (QuotientGroup.mk' (pCore 2 F.H) i)) := by
  let := chosen.elementary
  let hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  let D := sourceAction F hk
  let E := e.trans Binary.binaryCoordinates
  let f := sourceStarAction F hk e
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  let K := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let : K.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  let X := ((F.X g).subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  have hqX : X.map q.toMonoidHom = F.terminalDot (F.X g) := by
    rw [Subgroup.map_map]
    rfl
  let κm : K ≃* Binary.G := κ.trans elementaryEquiv.symm
  have hm (k : K) (w : Additive F.Uhat) : E (D.representation k w) = Binary.action (κm k) (E w) := by
    change Binary.binaryCoordinates (e (D.representation k w)) = _
    rw [he]
    obtain ⟨b,hb⟩ := elementaryEquiv.surjective (κ k)
    have hb' : κm k = b := by
      change elementaryEquiv.symm (κ k) = b
      rw [←hb,elementaryEquiv.symm_apply_apply]
    rw [←hb,hb']
    exact toOrthogonal_coordinates b (e w)
  have himage : K.map f = Binary.linearAction.range := by
    apply le_antisymm
    · rintro _ ⟨k,hk',rfl⟩
      refine ⟨κm ⟨k,hk'⟩,?_⟩
      apply LinearEquiv.ext
      intro w
      obtain ⟨v,rfl⟩ := E.surjective w
      rw [Binary.linearAction_apply,sourceStarAction_apply]
      exact (hm ⟨k,hk'⟩ v).symm
    · rintro _ ⟨b,rfl⟩
      obtain ⟨k,hk'⟩ := κm.surjective b
      refine ⟨k,k.property,?_⟩
      apply LinearEquiv.ext
      intro w
      obtain ⟨v,rfl⟩ := E.surjective w
      rw [Binary.linearAction_apply,sourceStarAction_apply,hm,hk']
  obtain ⟨_,_,_,z,_,_,_,hs,hs₂,hv0,hvs,hline,hpoint,_⟩ :=
    source_orthogonal_seed_point d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  let s : F.U := ⟨MulAut.conj g⁻¹ z,hs⟩
  let v := hatElement F s
  have hv : v ≠ 0 := by
    intro h
    apply hv0
    change e v = 0
    rw [h,map_zero]
  have hline' : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) := by
    apply Submodule.map_injective_of_injective e.injective
    rw [hline,Submodule.map_span]
    simp only [Set.image_singleton]
    rfl
  obtain ⟨hXP,hXN⟩ := source_actor_normal_in_point_stabilizer d earlier hq chosen
    structural alternatives F hne hZ g hgP hgH v hv hline'
  have hNX := (normal_subgroupOf_iff_le_normalizer hXP).mp hXN
  have hXtwo : IsPGroup 2 X := by
    obtain ⟨_,heX,_,_,_⟩ := source_terminal_hypothesis F d earlier hq chosen
      structural alternatives hne g hgP hgH
    let := heX
    have htwo : IsPGroup 2 (X.map q.toMonoidHom) := by
      rw [hqX]
      exact IsElementaryAbelian.isPGroup 2 _
    exact htwo.of_injective (q.subgroupMap X).toMonoidHom (q.subgroupMap X).injective
  have hn (a : F.H ⧸ pCore 2 F.H) (ha : f a (E v) = E v) :
      a ∈ normalizer (X : Set (F.H ⧸ pCore 2 F.H)) := by
    have hvfix : F.terminalRepresentation (q a) v = v := by
      apply E.injective
      exact (sourceStarAction_apply F hk e a v).symm.trans ha
    have hh := hNX hvfix
    rw [←hqX,←map_equiv_normalizer_eq] at hh
    obtain ⟨b,hb,heq⟩ := hh
    exact q.injective heq ▸ hb
  have hfix : f (QuotientGroup.mk' (pCore 2 F.H) i) (E v) = E v := by
    rw [sourceStarAction_apply]
    have hiconj : F.uAction i s = s := by
      apply Subtype.ext
      change (i:G)*(s:G)*(i:G)⁻¹ = (s:G)
      rw [←F.X_le_plane_centralizer g (F.P_le_G₂ (by decide) L chosen.normalizes hgP) hiX s hs₂]
      exact mul_inv_cancel_right _ _
    change E (Additive.ofMul (F.uhatAction i (QuotientGroup.mk' (center F.U) s))) = _
    rw [F.uhatAction_apply_mk,hiconj]
    rfl
  have hmove : ∃ c : Binary.F,
      f (QuotientGroup.mk' (pCore 2 F.H) i) (c • E v) ≠ c • E v := by
    by_contra! hfixline
    have hfixV (w : Additive F.Uhat) (hw : w ∈ hatSpace F V) : F.uhatAction i w.toMul = w.toMul := by
      have hw' : e w ∈ (Submodule.span Binary.F {e v}).restrictScalars (ZMod 2) := hpoint ▸ ⟨w,hw,rfl⟩
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hw'
      have hwE : E w = c • E v := by
        change coordinates (e w) = c • coordinates (e v)
        rw [←hc,map_smul]
      apply Additive.ofMul.injective
      apply E.injective
      change E (D.representation (QuotientGroup.mk' (pCore 2 F.H) i) w) = E w
      rw [←sourceStarAction_apply,hwE,hfixline]
    let C := source_closure_geometry F d earlier hq chosen structural alternatives hne
    have hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU :=
      disjoint_iff.mpr (F.conjugate_point_inf_ZU (by decide) C.seed_center g (chosen.normalizes hg) hgH)
    have hcomm := (source_commutator_squares d earlier hq chosen structural alternatives F).1
    have hVE : V ≤ F.E g := (F.parabolic_seed_geometry L chosen.normalizes g hgP).1
    apply hiV
    intro w hw
    let u : F.U := ⟨w,le_conjugateSpanBy V F.H hw⟩
    have hf := hfixV (hatElement F u) ⟨u,hw,rfl⟩
    change F.uhatAction i (QuotientGroup.mk' (center F.U) u) = QuotientGroup.mk' (center F.U) u at hf
    rw [F.uhatAction_apply_mk] at hf
    have hc : F.uAction i u / u ∈ center F.U := QuotientGroup.eq_iff_div_mem.mp hf
    have hd : ((F.uAction i u / u : F.U) : G) = ⁅(i:G),w⁆ := by
      change ((i:G)*w*(i:G)⁻¹)/w = _
      simp only [commutatorElement_def,div_eq_mul_inv]
    have hz : ⁅(i:G),w⁆ ∈ F.ZU := ⟨_,hc,hd⟩
    have hr := commutator_X_E_le_conjugate_point F g hcomm (commutator_mem_commutator hiX (hVE hw))
    have hone := mem_bot.mp (hdis.le_bot ⟨hr,hz⟩)
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
  apply PointExchange.swaps_of_point_normal_two f (sourceStarAction_injective F hk e)
    (himage ▸ map_le_range f K) X hXtwo (E v)
    (fun hh => hv (E.injective (hh.trans E.map_zero.symm)))
    ((coordinates_det (e v)).trans hvs) hn (QuotientGroup.mk' (pCore 2 F.H) i)
    (mem_map_of_mem _ hiX) hfix ?_ hmove
  rw [←himage]
  exact K.le_normalizer_map f (mem_map_of_mem f (by rw [normalizer_eq_top]; trivial))

/-- Compatibility with the already constructed original determinant action. -/
theorem source_orthogonal_action_swaps (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (i : F.H) (hiX : (i:G) ∈ F.X g)
    (hiV : (i:G) ∉ centralizer (V : Set G)) :
    Binary.InvolutionResidual.SwapsFactors
      ((source_orthogonal_action d earlier hq chosen structural alternatives
        F hne hZ g hg hgP hgH κ e he).action i) := by
  exact source_orthogonal_selected_swaps d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he i hiX hiV

/-- The original selected involution, with x=gkg unchanged, exchanges the two determinant factors. -/
theorem source_orthogonal_selected_interchange (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
 :
    F.H.pCoreIn 2 = F.U ∧
      ∃ z : G, orderOf z = 2 ∧ F.Vi 1 = zpowers z ∧
        F.H = centralizer ({z} : Set G) ∧
        ∃ k : G, k ∈ (pResidual 2 F.H).map F.H.subtype ∧
          let x := g*k*g
          let i := LargerDimension.Orthogonal.conjugateElement z x
          orderOf i = 2 ∧ i ∈ F.X g ∧ i ∈ T ∧ i ∉ F.U ∧
          i ∉ centralizer (V : Set G) ∧ ∃ hiH : i ∈ F.H,
            Binary.InvolutionResidual.SwapsFactors
              ((source_orthogonal_action d earlier hq chosen structural alternatives
                F hne hZ g hg hgP hgH κ e he).action ⟨i,hiH⟩) := by
  obtain ⟨hcore,z,hzo,hzp,hH,k,hk,hio,hiX,hiT,hiU,hiV⟩ :=
    source_orthogonal_selected_involution d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  refine ⟨hcore,z,hzo,hzp,hH,k,hk,hio,hiX,hiT,hiU,hiV,F.invariant 1 hiT,?_⟩
  exact source_orthogonal_action_swaps d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he ⟨_,F.invariant 1 hiT⟩ hiX hiV

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
