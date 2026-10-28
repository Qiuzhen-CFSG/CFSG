module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PairedData
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.QuotientTransport
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PairedInvariant
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.QuotientPlanes

/-!
# The actual polar coordinates and exchanged partner lines

The power form pairs E/Z and Eᵗ/Z perfectly. The full transvection action
on E/Z therefore acts naturally and contragrediently on their direct sum.
The source square-normalizer facts make t exchange both summands and the
two marked nonzero vectors. Their incidence follows because both marked
planes lie in the original elementary natural four-space.
Source: Aschbacher--Smith 15.3.56(4--7), printed p.1148.
-/
@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PairedCoordinates
open Recognition LocalRestrictions BinaryPairedTransvections BinaryLagrangianDualPair
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {Z ZS T V V₀ Y₁ : Subgroup G} {y : G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  {hk : (quotientAction Z ZS).ker=pCore 2 (centralizerH Z)} {s : ℕ}

/-- The polar construction on the literal source geometry and full X action.
The selected-source wrapper below discharges all geometric inputs. -/
theorem of_source_geometry
    (geometry : SelectedGeometry Z ZS T Y₁ y) (hV₀ : V₀=localSpan Z Y₁)
    (actionData : ExtraspecialAction.Data T Z ZS V₀ y s hk)
    (hXH : partnerX Z ZS y ≤ centralizerH Z)
    (hXN : partnerX Z ZS y ≤ normalizer (intersectionE Z ZS y:Set G))
    (t : centralizerH Z)
    (hXNt : partnerX Z ZS y ≤ normalizer (rightConjugate (intersectionE Z ZS y) (t:G):Set G))
    (hcompl : IsCompl (vectorSubspace Z ZS (intersectionE Z ZS y))
      (vectorSubspace Z ZS (rightConjugate (intersectionE Z ZS y) (t:G))))
    (hdim : Module.finrank (ZMod 2) (vectorSubspace Z ZS
      (rightConjugate (intersectionE Z ZS y) (t:G)))=
      Module.finrank (ZMod 2) (ESpace Z ZS y))
    (hextra : IsExtraspecial 2 (closureU Z ZS))
    (hcenter : center (closureU Z ZS)=Z.subgroupOf (closureU Z ZS))
    (hsquare : (t:G)^2∈normalizer (intersectionE Z ZS y:Set G))
    (hsquareV₀ : (t:G)^2∈normalizer (V₀:Set G))
    (hV₀V : V₀ ≤ V) (hVn : (t:G)∈normalizer (V:Set G))
    (hVe : IsElementaryAbelian 2 V) : Nonempty (Data Z ZS V₀ y t hk) := by
  let := hextra
  let E := vectorSubspace Z ZS (intersectionE Z ZS y)
  let F := vectorSubspace Z ZS (rightConjugate (intersectionE Z ZS y) (t:G))
  let ρ := actorRepresentation Z ZS hk
  let K := actorImage Z (partnerX Z ZS y)
  let qH := QuotientGroup.mk' (pCore 2 (centralizerH Z))
  let a := qH t
  have hZE : Z ≤ intersectionE Z ZS y :=
    (show Z ≤ localSpan Z Y₁ by rw [geometry.V₀_eq]; exact le_sup_left).trans geometry.V₀_le_E
  have hEU : intersectionE Z ZS y ≤ closureU Z ZS := by rw [geometry.E_eq]; exact inf_le_left
  have hZEt := point_le_conjugate Z _ hZE t
  have hEtU : rightConjugate (intersectionE Z ZS y) (t:G) ≤ closureU Z ZS := by
    rintro _ ⟨e,he,rfl⟩
    exact (mem_normalizer_iff.mp (H_normalizes_closureU Z ZS (t⁻¹).property) e).mp (hEU he)
  have hZV₀ : Z ≤ V₀ := by rw [hV₀,geometry.V₀_eq]; exact le_sup_left
  have hV₀U : V₀ ≤ closureU Z ZS := hV₀ ▸ geometry.V₀_le_U
  have hKE : K ≤ subspaceStabilizer ρ E := actorImage_le_subspaceStabilizer Z ZS hk _ _ hZE hEU hXN
  have hKF : K ≤ subspaceStabilizer ρ F := actorImage_le_subspaceStabilizer Z ZS hk _ _ hZEt hEtU hXNt
  obtain ⟨q,hB,hqi,hpow,_⟩ := exists_actor_power_form Z ZS hcenter hk
  let := geometry.E_elementary
  let : IsElementaryAbelian 2 (rightConjugate (intersectionE Z ZS y) (t:G)) :=
    IsElementaryAbelian.map (MulAut.conj (t:G)⁻¹).toMonoidHom
  have hqE : ∀e∈E,q e=0 := elementary_subspace_singular Z ZS _ q hpow
  have hqF : ∀f∈F,q f=0 := elementary_subspace_singular Z ZS _ q hpow
  let b := quadraticCoordinates q E F hB hcompl hqF hdim
  let c : E := actionData.centerVector
  have hc : c≠0 := fun h => actionData.center_ne_zero (congrArg Subtype.val h)
  have hbE (e : E) : b e=(e,0) := quadraticCoordinates_E q E F hB hcompl hqF hdim e
  have hbq (v : Space Z ZS) : BinaryNaturalDual.quadratic (b v)=q v :=
    quadraticCoordinates_quadratic q E F hB hcompl hqE hqF hdim v
  have hEimage (v : Space Z ZS) : v∈E ↔ (b v).2=0 :=
    coordinates_mem_E q.polarBilin E F hB hcompl _ hdim v
  have hFimage (v : Space Z ZS) : v∈F ↔ (b v).1=0 :=
    coordinates_mem_F q.polarBilin E F hB hcompl _ hdim v
  have hcenterimage (w : Space Z ZS) : w∈vectorSubspace Z ZS V₀ ↔
      ∃r:ZMod 2,b w=(r • c,0) := by
    rw [← actionData.center_span]
    constructor
    · intro hw
      obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hw
      refine ⟨r,?_⟩
      rw [← hr,map_smul,hbE]
      simp only [Prod.smul_mk,smul_zero]
      rfl
    · rintro ⟨r,hr⟩
      apply Submodule.mem_span_singleton.mpr
      refine ⟨r,b.injective ?_⟩
      rw [map_smul,hbE,hr]
      simp only [Prod.smul_mk,smul_zero]
      rfl
  let r := restrictedActor ρ E K hKE
  have hr (k : K) : r k∈centerGroup c := by
    obtain ⟨φ,hφ,he⟩ := actionData.is_transvection k
    apply (mem_centerGroup_iff c hc _).mpr
    exact ⟨φ,hφ,by ext e; exact he e⟩
  let pK : K →* centerGroup c := r.codRestrict (centerGroup c) hr
  have hpK : Function.Surjective pK := by
    rintro ⟨u,hu⟩
    obtain ⟨φ,hφ,rfl⟩ := (mem_centerGroup_iff c hc u).mp hu
    obtain ⟨k,hk⟩ := actionData.full φ hφ
    refine ⟨k,Subtype.ext ?_⟩
    ext e
    exact hk e
  let π : partnerX Z ZS y →* K :=
    (qH.comp (inclusion hXH)).codRestrict K (fun x => ⟨⟨x,hXH x.property⟩,x.property,rfl⟩)
  have hπ : Function.Surjective π := by
    rintro ⟨_,h,hh,rfl⟩
    exact ⟨⟨h,hh⟩,rfl⟩
  let p := pK.comp π
  have hxeq (x : partnerX Z ZS y) (w : VectorQuotient Z ZS) :
      b (Additive.ofMul (quotientAction Z ZS ⟨x,hXH x.property⟩ w))=
        pairedAction (p x).val (b (Additive.ofMul w)) :=
    quadraticCoordinates_equivariant ρ q E F hB hcompl hqF hdim K hKE hKF hqi (π x)
      (Additive.ofMul w)
  have hmodel : K.map (actor Z ZS hk b)=(centerGroup c).map pairedAction :=
    coordinateActor_image_center ρ q E F hB hcompl hqF hdim K hKE hKF hqi c hc
      actionData.is_transvection actionData.full
  have hqinv (k : ActorQuotient Z) (w : PairedSpace E) :
      BinaryNaturalDual.quadratic (actor Z ZS hk b k w)=BinaryNaturalDual.quadratic w := by
    change BinaryNaturalDual.quadratic (b (ρ k (b.symm w)))=_
    rw [hbq,hqi,← hbq,b.apply_symm_apply]
  have hexchange := actor_exchanges_subspaces Z ZS hk _ hZE t hsquare
  have hexE (e : E) : (actor Z ZS hk b a (e,0)).1=0 := by
    rw [← hbE,coordinateActor_apply,b.symm_apply_apply]
    exact (hFimage _).mp (hexchange.1 e e.property)
  have hexD (f : Module.Dual (ZMod 2) E) : (actor Z ZS hk b a (0,f)).2=0 := by
    rw [coordinateActor_apply]
    apply (hEimage _).mp
    apply hexchange.2
    apply (hFimage _).mpr
    simp only [b.apply_symm_apply]
  let δ : Module.Dual (ZMod 2) E := (actor Z ZS hk b a (c,0)).2
  have htc : actor Z ZS hk b a (c,0)=(0,δ) := Prod.ext (hexE c) rfl
  have hδ : δ≠0 := by
    intro hz
    have hz' : actor Z ZS hk b a (c,0)=0 := by rw [htc,hz]; rfl
    have := (actor Z ZS hk b a).map_eq_zero_iff.mp hz'
    exact hc (congrArg Prod.fst this)
  have hfix : ρ (a*a) (c:Space Z ZS)=c := by
    have hstab : qH (t^2)∈subspaceStabilizer ρ (vectorSubspace Z ZS V₀) := by
      change t^2∈(subspaceStabilizer ρ (vectorSubspace Z ZS V₀)).comap qH
      rw [stabilizer_preimage Z ZS hk V₀ hZV₀ hV₀U]
      exact hsquareV₀
    have hcm : (c:Space Z ZS)∈vectorSubspace Z ZS V₀ := by
      rw [← actionData.center_span]
      exact Submodule.mem_span_singleton_self _
    have hm := (hstab (c:Space Z ZS)).mpr hcm
    rw [map_pow,pow_two] at hm
    rw [← actionData.center_span] at hm
    rcases (BinaryTransvectionGroups.mem_centerLine_iff (c:Space Z ZS) _).mp hm with hz | he
    · have hi := (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom (a*a))).map_eq_zero_iff.mp hz
      exact False.elim (actionData.center_ne_zero hi)
    · exact he
  have htd : actor Z ZS hk b a (0,δ)=(c,0) := by
    rw [← htc,← LinearEquiv.mul_apply,← map_mul,← hbE,coordinateActor_apply,b.symm_apply_apply,hfix,hbE]
  have hincident : δ c=0 := by
    let := hVe
    have hv : (c:Space Z ZS)∈vectorSubspace Z ZS V := by
      apply (show vectorSubspace Z ZS V₀ ≤ vectorSubspace Z ZS V from
        fun _ hw => (show vectorImage Z ZS V₀ ≤ vectorImage Z ZS V from
          map_mono (comap_mono hV₀V)) hw)
      rw [← actionData.center_span]
      exact Submodule.mem_span_singleton_self _
    have hZN := hZV₀.trans hV₀V
    have hVUstab : ∀w∈vectorSubspace Z ZS V,ρ a w∈vectorSubspace Z ZS V := by
      intro w hw
      obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (closureU Z ZS)) w.toMul
      have hw' : w=Additive.ofMul (QuotientGroup.mk' _ u) := congrArg Additive.ofMul hu.symm
      rw [hw'] at hw ⊢
      rw [subspace_mk_mem Z ZS V hZN] at hw
      change Additive.ofMul (quotientAction Z ZS t (QuotientGroup.mk' _ u))∈_
      rw [quotientAction_mk,subspace_mk_mem Z ZS V hZN]
      exact (mem_normalizer_iff.mp hVn u).mp hw
    have hz := elementary_subspace_singular Z ZS V q hpow
      ((c:Space Z ZS)+ρ a c) ((vectorSubspace Z ZS V).add_mem hv (hVUstab c hv))
    rw [← hbq,map_add,hbE] at hz
    have hba : b (ρ a c)=(0,δ) := by
      simpa only [coordinateActor_apply,← hbE,b.symm_apply_apply] using htc
    rw [hba] at hz
    simpa only [Prod.mk_add_mk,add_zero,zero_add,BinaryNaturalDual.quadratic_apply] using hz
  exact ⟨⟨b,c,hc,δ,hδ,hincident,hEimage,hFimage,hcenterimage,hXH,p,hpK.comp hπ,
    hxeq,hmodel,hqinv,hexE,hexD,htc,htd⟩⟩

open CFSG.Quasithin.ChapterG.Section02
open Setup OrthogonalPlusFour Chapter15Collapse
variable {Zperp Y : Subgroup G} {g : G}

/-- The actual selected source datum: all coordinate, fullness, quadratic,
and exchange fields are derived from the same original pair and multiplicity. -/
theorem selected_data
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) (hspan : localSpan Z Y=V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g) (hΩ : omegaCenter T=Z)
    [((OrthogonalPlusFour.S₂ (Chapter15.setup Z Zperp Y T) g).subgroupOf
      ((Chapter15.setup Z Zperp Y T).S g)).Normal]
    [IsElementaryAbelian 2 (OrthogonalPlusFour.Quotient (Chapter15.setup Z Zperp Y T) g)]
    (f : SourceModuleData d)
    (hsame : f.decomposition.leftMultiplicity=f.decomposition.rightMultiplicity)
    (y : (Chapter15.setup Z Zperp Y T).I g) (hy : (y:G)∈leftResidual d)
    (hy3 : orderOf y=3) (hyc : matrixSection d y=MatrixOrbit.leftCubic)
    (t : centralizerH Z) (ht : (t:G)∈T)
    (hcap : intersectionE Z ZS (y:G) ⊓ rightConjugate (intersectionE Z ZS (y:G)) (t:G)=Z)
    (hsquarePlane : (t:G)^2∈normalizer (localSpan Z (leftResidual d):Set G))
    (hsquareE : (t:G)^2∈normalizer (intersectionE Z ZS (y:G):Set G))
    (hk : (quotientAction Z ZS).ker=pCore 2 (centralizerH Z)) :
    Nonempty (Data Z ZS (localSpan Z (leftResidual d)) (y:G) t hk) := by
  obtain ⟨geometry⟩ := selected_geometry hZS hperp hspan d hΩ y hy hyc
  obtain ⟨actionData⟩ := ExtraspecialAction.selected_action_data hZS hperp hspan d hΩ
    f hsame y hy hy3 hyc hk
  obtain ⟨hcompl,hE,hEt⟩ := selected_quotient_planes hZS hperp hspan d hΩ f hsame
    y hy hy3 hyc (t:G) ht hcap
  obtain ⟨hXN,hXNt⟩ := selected_partner_normalizes_both hZS hperp d y hy hyc (t:G) ht geometry
  obtain ⟨hextra,hcenter,_⟩ := PairGeometry.literal_extraspecial hZS hperp hspan d hΩ
  have hTH : T ≤ centralizerH Z := le_sup_right.trans d.base.local_le
  have hV₀V : localSpan Z (leftResidual d) ≤ V := by
    have hh := (selected_plane d y hy hyc).2.1.trans d.V_le_VL
    rwa [Chapter15.VL_eq hspan] at hh
  have hVn : (t:G)∈normalizer (V:Set G) := by
    have hh := T_normalizes_natural d ht
    rwa [Chapter15.VL_eq hspan] at hh
  have hVe : IsElementaryAbelian 2 V := (Chapter15.VL_eq hspan) ▸ d.VL_elementary
  exact of_source_geometry geometry rfl actionData (actionData.X_le_T.trans hTH)
    hXN t hXNt hcompl (hEt.trans hE.symm) hextra hcenter hsquareE hsquarePlane hV₀V hVn hVe

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PairedCoordinates
