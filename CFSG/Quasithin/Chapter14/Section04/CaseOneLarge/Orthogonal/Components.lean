module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Interchange
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Interchange
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.CentralizerComparison
public import Theory.GroupTheory.GeneralizedFitting.TwoQuotient
public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual

/-!
# The selected diagonal component in the original orthogonal quotient

The normal component square is the generalized Fitting subgroup: its quotient
is a two-group and the ambient two-core is trivial. The selected involution
interchanges the two actual determinant factors. Straightening its action on
the component coordinates identifies the fixed group with a diagonal A₅.
Perfectness then identifies that group with the two-residual of the centralizer.

The source application combines this calculation with the literal centralizer
comparison in H/O₂(H). It discharges the component premise of the existing
orthogonal contradiction for the original i=zˣ. The moved-module identification
remains explicit in the separately named conditional consumer; neither rank four
nor the group-coordinate straightening is used to assert that identification.
The private import of Interchange preserves its existing public boundary while
reusing the same faithful star action and the proved factor interchange.

Source: Aschbacher--Smith, Lemma 14.4.9, printed p.1010; refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Components
open Subgroup Theory.GroupTheory
open ClassicalOrthogonal.FourPlusMatrix ClassicalOrthogonal.FourPlusMatrix.QuotientLocal
open LargerDimension.Orthogonal
local notation "A" => alternatingGroup (Fin 5)

private instance : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)

private instance : IsQuasisimple A := {
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := ((QuotientGroup.quotientMulEquivOfEq
    (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }

private theorem product_fitting {S : Type*} [Group S] [IsQuasisimple S] :
    generalizedFitting (S × S) = ⊤ := by
  let N := (MonoidHom.inl S S).range
  let M := (MonoidHom.inr S S).range
  have hNi : Function.Injective (MonoidHom.inl S S) := fun _ _ h => congrArg Prod.fst h
  have hMi : Function.Injective (MonoidHom.inr S S) := fun _ _ h => congrArg Prod.snd h
  let : IsQuasisimple N := IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hNi)
  let : IsQuasisimple M := IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hMi)
  have hN : N.Normal := by
    constructor
    rintro _ ⟨a,rfl⟩ ⟨b,c⟩
    exact ⟨b*a*b⁻¹,by simp⟩
  have hM : M.Normal := by
    constructor
    rintro _ ⟨a,rfl⟩ ⟨b,c⟩
    exact ⟨c*a*c⁻¹,by simp⟩
  have hNF := component_le_generalizedFitting (S × S) N ⟨hN.isSubnormal,inferInstance⟩
  have hMF := component_le_generalizedFitting (S × S) M ⟨hM.isSubnormal,inferInstance⟩
  apply top_unique
  rintro ⟨a,b⟩ _
  have h := (generalizedFitting (S × S)).mul_mem (hNF ⟨a,rfl⟩) (hMF ⟨b,rfl⟩)
  simpa using h

private theorem square_fitting {Q : Type*} [Group Q] [Finite Q]
    (K : Subgroup Q) [K.Normal] (e : K ≃* A × A)
    (hq : IsPGroup 2 (Q ⧸ K)) (hc : pCore 2 Q = ⊥) :
    generalizedFitting Q = K := by
  have hK : generalizedFitting K = ⊤ := by
    have he := map_generalizedFitting_equiv e
    rw [product_fitting] at he
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [he,← MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr e.surjective]
  apply generalizedFitting_eq_of_le_two_quotient K ?_ hq hc
  have h := generalizedFitting_map_subtype_le_of_isSubnormal K
    (inferInstance : K.Normal).isSubnormal
  simpa only [hK,← MonoidHom.range_eq_map,Subgroup.range_subtype] using h

/-- The two-residual of the centralizer is exactly the fixed diagonal in the square. -/
private theorem centralizer_residual {Q : Type*} [Group Q] [Finite Q]
    (K : Subgroup Q) [K.Normal] (e : K ≃* A × A)
    (hq : IsPGroup 2 (Q ⧸ K)) (hc : pCore 2 Q = ⊥)
    (i : Q) (hi : componentAction K e i = swap) :
    (pResidual 2 (centralizer ({i} : Set Q))).map (centralizer ({i} : Set Q)).subtype = K ⊓ centralizer ({i} : Set Q) := by
  let f := componentAction K e
  have hf := componentAction_injective_of_generalizedFitting K e
    (square_fitting K e hq hc) (alternatingGroup.center_eq_bot (by simp))
  let D := K ⊓ centralizer ({i} : Set Q)
  have hd : D.map f = diagonalInner.range := fixed_component_image K e i hi
  have hdi : Function.Injective (diagonalInner (S:=A)) := by
    intro a b hab
    have he : MulAut.conj (a,a) = MulAut.conj (b,b) := hab
    have hinj := Theory.GroupTheory.conj_injective_of_center_eq_bot
      (show center (A × A) = ⊥ by rw [Subgroup.center_prod,alternatingGroup.center_eq_bot (by simp),bot_prod_bot])
    exact congrArg Prod.fst (hinj he)
  let ed : D ≃* A := (D.equivMapOfInjective f hf).trans
    ((MulEquiv.subgroupCongr hd).trans (MonoidHom.ofInjective hdi).symm)
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f:=ed.symm.toMonoidHom) ed.symm.surjective
  let C := centralizer ({i} : Set Q)
  have hrK : (pResidual 2 C).map C.subtype ≤ K := by
    have h := map_pResidual_le 2 C.subtype
    exact h.trans (sInf_le ⟨inferInstance,hq⟩)
  apply le_antisymm (le_inf hrK (map_subtype_le _))
  have hperf : (pResidual 2 D) = ⊤ := (pResidual_eq_top_iff 2 D).mpr
    (by
      intro N hN hqN
      let : N.Normal := hN
      by_contra hn
      let : Nontrivial (D ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
      let : Group.IsPerfect (D ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
      let : Group.IsNilpotent (D ⧸ N) := hqN.isNilpotent
      exact Group.IsPerfect.not_isSolvable (D ⧸ N) inferInstance)
  have h := map_pResidual_le 2 (inclusion (inf_le_right : D ≤ C))
  rw [hperf,← MonoidHom.range_eq_map] at h
  intro x hx
  exact ⟨⟨x,hx.2⟩,h ⟨⟨x,hx⟩,rfl⟩,rfl⟩


private theorem linearAction_injective : Function.Injective Binary.linearAction := by
  intro a b h
  apply Binary.action_injective
  apply LinearMap.ext
  intro v
  simpa only [Binary.linearAction_apply] using LinearEquiv.congr_fun h v

private theorem component_exchange {Q : Type*} [Group Q] [Finite Q]
    (K : Subgroup Q) [K.Normal] (e : K ≃* Binary.G)
    (f : Q →* (Binary.V ≃ₗ[ZMod 2] Binary.V))
    (he : ∀ k : K, f k = Binary.linearAction (e k))
    (i : Q) (hi : Binary.InvolutionResidual.SwapsFactors (f i)) :
    ∃ a b : MulAut A,
      componentAction K (e.trans (factorAlternatingEquiv.prodCongr factorAlternatingEquiv)) i =
        a.prodCongr b * (MulEquiv.prodComm : MulAut (A × A)) := by
  let E := e.trans (factorAlternatingEquiv.prodCongr factorAlternatingEquiv)
  let α := componentAction K E i
  rcases Theory.GroupTheory.AutomorphismSquare.normal_form
    (alternatingGroup.center_eq_bot (by simp)) α with ⟨a,b,hab⟩ | hex
  · exfalso
    obtain ⟨s,hs⟩ := exists_ne (1 : A)
    let k : K := E.symm (s,1)
    let k' : K := MulAut.conjNormal i k
    let B := factorAlternatingEquiv.prodCongr factorAlternatingEquiv
    have coord (r : K) : e r = B.symm (E r) := (B.symm_apply_apply (e r)).symm
    have hk : e k = (factorAlternatingEquiv.symm s,1) := by
      rw [coord,E.apply_symm_apply]
      exact Prod.ext rfl factorAlternatingEquiv.symm.map_one
    have hk' : e k' = (factorAlternatingEquiv.symm (a s),1) := by
      have h := MulEquiv.congr_fun hab (s,1)
      change E k' = (a s,b 1) at h
      rw [coord,h]
      exact Prod.ext rfl ((congrArg factorAlternatingEquiv.symm b.map_one).trans
        factorAlternatingEquiv.symm.map_one)
    have hleft : f k ∈ Binary.InvolutionResidual.leftFactor := by
      rw [he,hk]
      exact ⟨factorAlternatingEquiv.symm s,rfl⟩
    have hright : f k' ∈ Binary.InvolutionResidual.rightFactor := by
      rw [←hi.1]
      refine ⟨f k,hleft,?_⟩
      change f i * f (k:Q) * (f i)⁻¹ = f (i*(k:Q)*i⁻¹)
      simp only [map_mul,map_inv]
    obtain ⟨r,hr⟩ := hright
    change Binary.linearAction (1,r) = f k' at hr
    rw [he,hk'] at hr
    have hh := congrArg Prod.fst (linearAction_injective hr)
    have haa : a s = 1 := by
      have hh' := congrArg factorAlternatingEquiv hh
      simpa using hh'.symm
    exact hs (a.injective (haa.trans a.map_one.symm))
  · exact hex

/-- Component data with the centralizer residual proved, rather than assumed
as an additional marking premise. -/
theorem of_matrix_swap {Q : Type*} [Group Q] [Finite Q]
    (K : Subgroup Q) [K.Normal] (e : K ≃* Binary.G)
    (hq : IsPGroup 2 (Q ⧸ K)) (hc : pCore 2 Q = ⊥)
    (f : Q →* (Binary.V ≃ₗ[ZMod 2] Binary.V))
    (he : ∀ k : K, f k = Binary.linearAction (e k))
    (i : Q) (hi : i^2=1) (hs : Binary.InvolutionResidual.SwapsFactors (f i)) :
    Nonempty (QuotientModel.SelectedComponentData Q i
      ((pResidual 2 (centralizer ({i} : Set Q))).map (centralizer ({i} : Set Q)).subtype)) := by
  obtain ⟨a,b,hab⟩ := component_exchange K e f he i hs
  let E := e.trans (factorAlternatingEquiv.prodCongr factorAlternatingEquiv)
  let c : MulAut (A × A) := (MulEquiv.refl A).prodCongr a
  let E' := E.trans c
  have hcoords : componentAction K E' i = swap := by
    have hs : (a.prodCongr b * (MulEquiv.prodComm : MulAut (A × A))) ^ 2 = 1 := by
      rw [←hab,←map_pow,hi,map_one]
    have hh : componentAction K E' i = MulAut.congr c (componentAction K E i) := by
      apply MulEquiv.ext
      intro s
      rfl
    rw [hh,hab]
    exact straighten_exchange a b hs
  let Eo := E'.trans orthogonalAlternatingEquiv.symm
  have heo : Eo.trans orthogonalAlternatingEquiv = E' := by
    apply MulEquiv.ext
    intro k
    exact orthogonalAlternatingEquiv.apply_symm_apply _
  refine ⟨⟨K,inferInstance,Eo,square_fitting K E hq hc,?_,?_⟩⟩
  · rw [heo]
    exact hcoords
  · exact centralizer_residual K E' hq hc i hcoords

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Components

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
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

/-- The literal image of the selected residual has the source diagonal component
structure, with the original involution and quotient map unchanged. -/
theorem source_orthogonal_selected_components (d : Counterexample T L)
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
    (z : G) (hz : orderOf z = 2) (hzp : F.Vi 1 = zpowers z)
    (hH : F.H = centralizer ({z} : Set G))
    (i : F.H) (hiX : (i:G) ∈ F.X g)
    (hiV : (i:G) ∉ centralizer (V : Set G)) (hio : orderOf (i:G) = 2) :
    Nonempty (QuotientModel.SelectedComponentData (F.H ⧸ pCore 2 F.H)
      (QuotientGroup.mk' (pCore 2 F.H) i)
      (((diagonalResidual F.H (i:G)).subgroupOf F.H).map
        (QuotientGroup.mk' (pCore 2 F.H)))) := by
  let := chosen.elementary
  let hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  let D := sourceAction F hk
  let E := e.trans Binary.binaryCoordinates
  let f := sourceStarAction F hk e
  let K := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let : K.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
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
  have hf (k : K) : f k = Binary.linearAction (κm k) := by
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := E.surjective w
    rw [Binary.linearAction_apply,sourceStarAction_apply]
    exact hm k v
  have hquot : IsPGroup 2 ((F.H ⧸ pCore 2 F.H) ⧸ K) := by
    have hK : K = pResidual 2 (F.H ⧸ pCore 2 F.H) :=
      map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)
    exact (isPGroup_quotient_pResidual 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hK.symm)
  have hpow : (QuotientGroup.mk' (pCore 2 F.H) i)^2=1 := by
    rw [←map_pow]
    have hi2 : i^2=1 := Subtype.ext (hio ▸ pow_orderOf_eq_one (i:G))
    rw [hi2,map_one]
  have hs : Binary.InvolutionResidual.SwapsFactors
      (f (QuotientGroup.mk' (pCore 2 F.H) i)) :=
    source_orthogonal_selected_swaps d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he i hiX hiV
  have hr := diagonalResidual_image_of_comparison F.H z i hz hH.le
    (source_orthogonal_centralizer_comparison d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he z hzp hH i hiX hiV hio)
  rw [hr]
  exact Components.of_matrix_swap K κm hquot (pCore_quotient_pCore_eq_bot 2)
    f hf _ hpow hs

/-- The component premise of the original orthogonal exclusion is discharged.
The actual moved-module coordinates remain an explicit source obligation. -/
theorem source_selected_contradiction_of_moved_model (d : Counterexample T L)
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
    (z x : G) (hz : orderOf z = 2) (hzp : F.Vi 1 = zpowers z)
    (hH : F.H = centralizer ({z} : Set G))
    (hiT : conjugateElement z x ∈ T) (hout : conjugateElement z x ∉ F.U)
    (hiX : conjugateElement z x ∈ F.X g)
    (hiV : conjugateElement z x ∉ centralizer (V : Set G))
    (hKU : diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ≤
      normalizer (F.U : Set G))
    (m : MovedCoreModel F.U
      (diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x))
      (conjugateElement z x) hKU)
 : False := by
  have hio : orderOf (conjugateElement z x) = 2 := by
    simpa only [conjugateElement,MulEquiv.orderOf_eq] using hz
  have hc := fun hiH : conjugateElement z x ∈ F.H => source_orthogonal_selected_components d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he z hz hzp hH ⟨_,hiH⟩ hiX hiV hio
  rw [hH] at hc
  exact source_selected_contradiction_of_diagonal d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he z x hz hzp hH hiT hout hiX hiV hKU m (hc _).some

/-- The original selection i=z^(gkg), now with the diagonal component
constructed from its source geometry. No extra selection or component premise is used. -/
theorem source_orthogonal_selected_diagonal (d : Counterexample T L)
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
    F.H.pCoreIn 2 = F.U ∧
      ∃ z : G, orderOf z = 2 ∧ F.Vi 1 = zpowers z ∧
        F.H = centralizer ({z} : Set G) ∧
        ∃ k : G, k ∈ (pResidual 2 F.H).map F.H.subtype ∧
          let x := g*k*g
          let i := conjugateElement z x
          orderOf i = 2 ∧ i ∈ F.X g ∧ i ∈ T ∧ i ∉ F.U ∧
          i ∉ centralizer (V : Set G) ∧ ∃ hiH : i ∈ F.H,
            Nonempty (QuotientModel.SelectedComponentData (F.H ⧸ pCore 2 F.H)
              (QuotientGroup.mk' (pCore 2 F.H) ⟨i,hiH⟩)
              (((diagonalResidual F.H i).subgroupOf F.H).map
                (QuotientGroup.mk' (pCore 2 F.H)))) := by
  obtain ⟨hcore,z,hzo,hzp,hH,k,hk,hio,hiX,hiT,hiU,hiV⟩ :=
    source_orthogonal_selected_involution d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  refine ⟨hcore,z,hzo,hzp,hH,k,hk,hio,hiX,hiT,hiU,hiV,F.invariant 1 hiT,?_⟩
  exact source_orthogonal_selected_components d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he z hzo hzp hH ⟨_,F.invariant 1 hiT⟩ hiX hiV hio

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
