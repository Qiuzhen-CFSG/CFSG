module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Selection
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel.ActionModel
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Actions.ChiefModules.Model
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.Symmetry
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.FlagAction


/-!
# The original and exchanged determinant actions

The original natural Ω₄⁺(4) coordinates and O₂(H)=U construct the full
H-action on the literal U/Z(U), with its actual two-residual image. Transport
by x⁻¹(·)x supplies the corresponding action of C_G(zˣ) on Uˣ/Z(Uˣ),
retaining exactly the source conjugator.

For the selected i∈Wᵍ which moves V, the binary fixed seed point and the
identity Ṽ=F₄·z̃ᵍ force a nontrivial field twist. Semilinear displacement
then has binary rank at least four. Since i is an involution on the
eight-dimensional quotient, the rank is exactly four and the literal
commutator image has sixteen elements. CentralizerComparison applies
these constructions to the original selected configuration.

Source: Aschbacher--Smith, Lemma 14.4.9, printed pp.1009--1010;
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Orthogonal CoreGeometry
open ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable [IsMulCommutative V]
local instance (F : InvariantFlag T V 3) : (F.U.subgroupOf F.H).Normal := F.U_normal

omit [Finite G] [IsMulCommutative V] in
/-- Transport the whole determinant action through an ambient automorphism.
Both central quotients use the induced maps on their original representatives. -/
private def transport_orthogonal_action (H U : Subgroup G)
    (m : ExchangedModel.CaseThreeAction H U) (f : G ≃* G) :
    ExchangedModel.CaseThreeAction (H.map f.toMonoidHom) (U.map f.toMonoidHom) := by
  let H' := H.map f.toMonoidHom
  let U' := U.map f.toMonoidHom
  let eH : H ≃* H' := f.subgroupMap H
  let eU : U ≃* U' := f.subgroupMap U
  let c : (U' ⧸ center U') ≃* (U ⧸ center U) :=
    QuotientGroup.congr _ _ eU.symm (map_center_equiv eU.symm)
  have hn : H' ≤ normalizer (U' : Set G) := by
    rintro _ ⟨h,hh,rfl⟩
    apply mem_normalizer_iff.mpr
    intro v
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨h*u*h⁻¹,(mem_normalizer_iff.mp (m.normalizes hh) u).mp hu,by simp⟩
    · intro hv
      have hv' : f (h * f.symm v * h⁻¹) ∈ U' := by simpa using hv
      have hh' : h * f.symm v * h⁻¹ ∈ U := by
        obtain ⟨u,hu,he⟩ := hv'
        exact f.injective he ▸ hu
      exact ⟨f.symm v,(mem_normalizer_iff.mp (m.normalizes hh) _).mpr hh',f.apply_symm_apply v⟩
  let C := m.components.map eH.toMonoidHom
  let hC : C.Normal := Normal.map m.components_normal _ eH.surjective
  letI := hC
  letI := m.components_normal
  refine {
    normalizes := hn
    coordinates := c.trans m.coordinates
    action := m.action.comp eH.symm.toMonoidHom
    equivariant := ?_
    kernel := ?_
    components := C
    components_normal := hC
    outer_two := m.outer_two.of_equiv (QuotientGroup.congr _ _ eH rfl)
    components_image := ?_ }
  · intro h u
    have he : eU.symm (U'.normalizerMonoidHom ⟨h,hn h.property⟩ u) =
        U.normalizerMonoidHom ⟨eH.symm h,m.normalizes (eH.symm h).property⟩ (eU.symm u) := by
      apply Subtype.ext
      change f.symm ((h:G)*(u:G)*(h:G)⁻¹) =
        f.symm (h:G) * f.symm (u:G) * (f.symm (h:G))⁻¹
      simp only [map_mul,map_inv]
    change m.coordinates (c (QuotientGroup.mk' (center U') _)) =
      Multiplicative.ofAdd (m.action (eH.symm h)
        (m.coordinates (c (QuotientGroup.mk' (center U') u))).toAdd)
    rw [show ∀ v : U', c (QuotientGroup.mk' (center U') v) =
      QuotientGroup.mk' (center U) (eU.symm v) from fun v => rfl]
    rw [he,m.equivariant]
    rfl
  · intro h hh
    have hu : (eH.symm h : G) ∈ U := m.kernel hh
    exact ⟨f.symm (h:G),hu,f.apply_symm_apply h⟩
  · change (m.components.map eH.toMonoidHom).map
      (m.action.comp eH.symm.toMonoidHom) = _
    rw [map_map]
    have he : (m.action.comp eH.symm.toMonoidHom).comp eH.toMonoidHom = m.action := by
      apply MonoidHom.ext
      intro h
      exact congrArg m.action (eH.symm_apply_apply h)
    rw [he,m.components_image]

private def matrixCoordinates (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (E : Additive F.Uhat ≃ₗ[ZMod 2] Binary.V) :
    F.Uhat ≃* Multiplicative Binary.V where
  toFun v := Multiplicative.ofAdd (E (Additive.ofMul v))
  invFun v := (E.symm v.toAdd).toMul
  left_inv v := E.symm_apply_apply v
  right_inv v := E.apply_symm_apply v
  map_mul' v w := E.map_add v w

/-- The original full local action in determinant coordinates, with kernel
contained in U and component image equal to the actual matrix group. -/
def source_orthogonal_action (d : Counterexample T L)
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
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    ExchangedModel.CaseThreeAction F.H F.U := by
  let := chosen.elementary
  have hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  have hcore := (source_orthogonal_twoCore d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he).2
  let D := sourceAction F hk
  let E := e.trans Binary.binaryCoordinates
  let ρ : Representation (ZMod 2) F.H Binary.V :=
    E.conjRingEquiv.toMonoidHom.comp (D.representation.comp (QuotientGroup.mk' (pCore 2 F.H)))
  let a : F.H →* (Binary.V ≃ₗ[ZMod 2] Binary.V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Binary.V).toMonoidHom.comp ρ.asGroupHom
  have ha (h : F.H) (v : Additive F.Uhat) :
      a h (E v) = E (D.representation (QuotientGroup.mk' (pCore 2 F.H) h) v) := by
    change E (D.representation (QuotientGroup.mk' (pCore 2 F.H) h) (E.symm (E v))) = _
    rw [E.symm_apply_apply]
  let K := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let κm : K ≃* Binary.G := κ.trans elementaryEquiv.symm
  have hm (k : K) (w : Additive F.Uhat) :
      E (D.representation k w) = Binary.action (κm k) (E w) := by
    change Binary.binaryCoordinates (e (D.representation k w)) = _
    rw [he]
    obtain ⟨b,hb⟩ := elementaryEquiv.surjective (κ k)
    have hb' : κm k = b := by
      change elementaryEquiv.symm (κ k) = b
      rw [←hb,elementaryEquiv.symm_apply_apply]
    rw [←hb,hb']
    exact toOrthogonal_coordinates b (e w)
  refine {
    normalizes := le_normalizer_conjugateSpanBy V F.H
    coordinates := matrixCoordinates F E
    action := a
    equivariant := ?_
    kernel := ?_
    components := pResidual 2 F.H
    components_normal := inferInstance
    outer_two := isPGroup_quotient_pResidual 2
    components_image := ?_ }
  · intro h u
    change E (Additive.ofMul (QuotientGroup.mk' (center F.U) _)) = a h (E (hatElement F u))
    rw [ha]
    exact congrArg (fun v => E (Additive.ofMul v)) (F.terminalHatAction_apply_mk h u).symm
  · intro h hh
    have hz : F.terminalHatAction h = 1 := by
      apply MulEquiv.ext
      intro v
      apply E.injective
      have hv := ha h (Additive.ofMul v)
      rw [show a h = 1 from hh] at hv
      exact hv.symm
    have hh' : h ∈ pCore 2 F.H := hk ▸ hz
    have hu : (h:G) ∈ F.H.pCoreIn 2 := mem_map_of_mem F.H.subtype hh'
    rwa [hcore] at hu
  · apply le_antisymm
    · rintro _ ⟨h,hh,rfl⟩
      let k : K := ⟨QuotientGroup.mk' (pCore 2 F.H) h,mem_map_of_mem _ hh⟩
      refine ⟨κm k,?_⟩
      apply LinearEquiv.ext
      intro v
      obtain ⟨w,rfl⟩ := E.surjective v
      exact (hm k w).symm.trans (ha h w).symm
    · rintro _ ⟨b,rfl⟩
      obtain ⟨k,hk⟩ := κm.surjective b
      obtain ⟨h,hh,hq⟩ := k.property
      refine ⟨h,hh,?_⟩
      apply LinearEquiv.ext
      intro v
      obtain ⟨w,rfl⟩ := E.surjective v
      rw [ha]
      change E (D.representation (QuotientGroup.mk' (pCore 2 F.H) h) w) = Binary.action b (E w)
      rw [hq,hm,hk]

/-- A selected member of Wᵍ moving V cannot be F₄-linear: it fixes the
marked binary point, and field linearity would fix its whole F₄-span Ṽ.
The resulting nontrivial field twist moves exactly four binary dimensions. -/
theorem source_orthogonal_moved_rank (d : Counterexample T L)
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
    (hiV : (i:G) ∉ centralizer (V : Set G)) (hio : orderOf (i:G) = 2) :
    let m := source_orthogonal_action d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
    finrank (ZMod 2) (LinearMap.range ((m.action i).toLinearMap - LinearMap.id)) = 4 ∧
      Nat.card (movedImage F.U (i:G)) = 16 := by
  let := chosen.elementary
  let m := source_orthogonal_action d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he
  let E := e.trans Binary.binaryCoordinates
  have ha (h : F.H) (w : Additive F.Uhat) :
      m.action h (E w) = E (Additive.ofMul (F.uhatAction h w.toMul)) := by
    change E (Additive.ofMul (F.uhatAction h (E.symm (E w)).toMul)) = _
    rw [E.symm_apply_apply]
  obtain ⟨_,_,_,z,_,_,_,hs,hs₂,_,_,_,hpoint,_⟩ :=
    source_orthogonal_seed_point d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  let s : F.U := ⟨MulAut.conj g⁻¹ z,hs⟩
  let v := hatElement F s
  have hiconj : F.uAction i s = s := by
    apply Subtype.ext
    change (i:G)*(s:G)*(i:G)⁻¹ = (s:G)
    rw [←F.X_le_plane_centralizer g (F.P_le_G₂ (by decide) L chosen.normalizes hgP) hiX s hs₂]
    exact mul_inv_cancel_right _ _
  have hfix : m.action i (E v) = E v := by
    rw [ha]
    change E (Additive.ofMul (F.uhatAction i (QuotientGroup.mk' (center F.U) s))) = _
    rw [F.uhatAction_apply_mk,hiconj]
    rfl
  have hnlin : ¬ ∀ (c : Binary.F) (w : Binary.V), m.action i (c • w) = c • m.action i w := by
    intro hlin
    have hfixV (w : Additive F.Uhat) (hw : w ∈ hatSpace F V) :
        F.uhatAction i w.toMul = w.toMul := by
      have hw' : e w ∈ (Submodule.span Binary.F {e v}).restrictScalars (ZMod 2) :=
        hpoint ▸ ⟨w,hw,rfl⟩
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hw'
      have hwE : E w = c • E v := by
        change coordinates (e w) = c • coordinates (e v)
        rw [←hc,map_smul]
      apply Additive.ofMul.injective
      apply E.injective
      rw [←ha,hwE,hlin,hfix]
      exact hwE.symm
    let C := source_closure_geometry F d earlier hq chosen structural alternatives hne
    have hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU :=
      disjoint_iff.mpr (F.conjugate_point_inf_ZU (by decide) C.seed_center g
        (chosen.normalizes hg) hgH)
    have hcomm := (source_commutator_squares d earlier hq chosen structural alternatives F).1
    have hVE : V ≤ F.E g := (F.parabolic_seed_geometry L chosen.normalizes g hgP).1
    apply hiV
    intro w hw
    let u : F.U := ⟨w,le_conjugateSpanBy V F.H hw⟩
    have hf := hfixV (hatElement F u) ⟨u,hw,rfl⟩
    change F.uhatAction i (QuotientGroup.mk' (center F.U) u) =
      QuotientGroup.mk' (center F.U) u at hf
    rw [F.uhatAction_apply_mk] at hf
    have hc : F.uAction i u / u ∈ center F.U := QuotientGroup.eq_iff_div_mem.mp hf
    have hd : ((F.uAction i u / u : F.U) : G) = ⁅(i:G),w⁆ := by
      change ((i:G)*w*(i:G)⁻¹)/w = _
      simp only [commutatorElement_def,div_eq_mul_inv]
    have hz : ⁅(i:G),w⁆ ∈ F.ZU := ⟨_,hc,hd⟩
    have hr := commutator_X_E_le_conjugate_point F g hcomm
      (commutator_mem_commutator hiX (hVE hw))
    have hone := mem_bot.mp (hdis.le_bot ⟨hr,hz⟩)
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
  obtain ⟨σ,hσ⟩ := Binary.normalizer_semilinear (m.action i) (m.action_normalizes i)
  have hσne : ∃ c : Binary.F, σ c ≠ c := by
    by_contra! h
    apply hnlin
    simpa only [h] using hσ
  have hl := NaturalTensor.finrank_le_twice_operatorFixedCodim
    (m.action i).toLinearMap σ.toRingHom hσne hσ
  rw [Binary.finrank_binary] at hl
  let t := m.action i
  let f : Binary.V →ₗ[ZMod 2] Binary.V := t.toLinearMap - LinearMap.id
  have ht : t ^ 2 = 1 := by
    rw [←map_pow]
    have hi2 : i ^ 2 = 1 := Subtype.ext (hio ▸ pow_orderOf_eq_one (i:G))
    rw [hi2,map_one]
  have hle : f.range ≤ f.ker := by
    rintro _ ⟨w,rfl⟩
    change t (t w - w) - (t w - w) = 0
    have htw : t (t w) = w := LinearEquiv.congr_fun ht w
    rw [map_sub,htw]
    apply sub_eq_zero.mpr
    exact sub_eq_sub_iff_add_eq_add.mpr (by
      apply Matrix.ext
      intro j k
      exact (CharTwo.add_self_eq_zero (w j k)).trans
        (CharTwo.add_self_eq_zero (t w j k)).symm)
  have hr := f.finrank_range_add_finrank_ker
  have hu := Submodule.finrank_mono hle
  rw [Binary.finrank_binary] at hr
  have hdim : finrank (ZMod 2) f.range = 4 := by
    change 8 ≤ 2 * finrank (ZMod 2) f.range at hl
    omega
  refine ⟨hdim,?_⟩
  rw [←m.subspace_card (movedImage F.U (i:G)),m.subspace_moved i hio,
    Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,hdim]
  norm_num

/-- The exchanged action is constructed on C_G(zˣ) and the same Uˣ,
by transporting the entire original case-(3) action through x⁻¹(·)x. -/
def source_orthogonal_exchanged_action (d : Counterexample T L)
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
    (z x : G) (hH : F.H = centralizer ({z} : Set G)) :
    ExchangedModel.CaseThreeAction
      (centralizer ({conjugateElement z x} : Set G)) (conjugateCore F.U x) := by
  let m := source_orthogonal_action d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he
  have a := transport_orthogonal_action F.H F.U m (MulAut.conj x⁻¹)
  change ExchangedModel.CaseThreeAction (conjugateCore F.H x) (conjugateCore F.U x) at a
  rwa [hH,LargerDimension.Orthogonal.conjugate_centralizer] at a


end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
