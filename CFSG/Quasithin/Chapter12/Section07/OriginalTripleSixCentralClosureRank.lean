module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureAction
public import Theory.Representation.HexacodeAction.WeightFourQuotientRank
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupTheory.PPerfectCubicImage

/-!
# Rank two or four in the original central-closure action

The original chart followed by the actual quotient projection gives a
surjective binary linear map onto the whole original U-image. Its kernel
contains the same scalar point and is invariant under the literal cubic
residual, by normality of the actual action kernel. The intrinsic quotient
rank calculation therefore gives order four or sixteen for this image.

Source: Aschbacher--Smith12.7.15(4), printed p.843. The ambient subgroups,
both conjugate closures and full quotient kernel are unchanged.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource Atlas.Codes Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem original_image_card (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z≠1) (hzT : (T : Subgroup G)≤centralizer ({(z:G)} : Set G))
    (H : Subgroup G) (hUH : U≤H) (hJH : tripleSixWeightFourResidual K z≤H)
    (N : Subgroup H) [N.Normal]
    (hVN : (tripleSixPoint D a z).subgroupOf H≤N)
    (hne : (U.subgroupOf H).map (QuotientGroup.mk' N)≠⊥) :
    Nat.card ((U.subgroupOf H).map (QuotientGroup.mk' N))=4 ∨
      Nat.card ((U.subgroupOf H).map (QuotientGroup.mk' N))=16 := by
  let J := tripleSixWeightFourResidual K z
  let C := K ⊓ centralizer ({(z:G)} : Set G)
  let V1 := tripleSixPoint D a z
  let q := QuotientGroup.mk' N
  let A := (U.subgroupOf H).map q
  let f := tripleSixPointCoordinates D a
  let v := (f z).toAdd
  let := D.elementary
  let : IsElementaryAbelian 2 (U.subgroupOf H) := IsElementaryAbelian.subgroupOf hUH
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  let b : Multiplicative hexacode →* A :=
    (q.subgroupMap (U.subgroupOf H)).comp
      (((subgroupOfEquivOfLe hUH).symm.toMonoidHom).comp f.symm.toMonoidHom)
  let ℓ : hexacode →ₗ[ZMod 2] Additive A := b.toAdditiveRight.toZModLinearMap 2
  have hℓ : Function.Surjective ℓ :=
    (q.subgroupMap_surjective (U.subgroupOf H)).comp
      ((subgroupOfEquivOfLe hUH).symm.surjective.comp f.symm.surjective)
  let E := ℓ.ker
  have hmem (w : hexacode) : w∈E ↔
      (⟨(f.symm (Multiplicative.ofAdd w):G),hUH (f.symm (Multiplicative.ofAdd w)).property⟩ : H)∈N := by
    change b (Multiplicative.ofAdd w)=1 ↔ _
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  have hPE : (Submodule.span Hexacode.F {v}).restrictScalars (ZMod 2)≤E := by
    intro w hw
    apply (hmem w).mpr
    apply hVN
    refine ⟨f.symm (Multiplicative.ofAdd w),?_,rfl⟩
    change (f (f.symm (Multiplicative.ofAdd w))).toAdd ∈ Submodule.span Hexacode.F {v}
    rw [f.apply_symm_apply]
    change w∈Submodule.span Hexacode.F {v} at hw ⊢
    exact hw
  let B := (pResidual 2 (Hexacode.fullWeightVectorStabilizer v)).map
    (Hexacode.fullWeightVectorStabilizer v).subtype
  have stable (g : HexEvenAutomorphisms) (hg : g∈B) (w : hexacode) (hw : w∈E) :
      Hexacode.evenAction g w∈E := by
    obtain ⟨r,hr,rfl⟩ := hg
    obtain ⟨c,hc,hcr⟩ := show r∈(J.subgroupOf C).map (tripleSixPointCentralizerProjection D a z) by
      rw [tripleSixWeightFourResidual_image D a z]
      exact hr
    let u := f.symm (Multiplicative.ofAdd w)
    let uH : H := ⟨u,hUH u.property⟩
    let cH : H := ⟨c,hJH hc⟩
    have huN : uH∈N := (hmem w).mp hw
    have hconj : cH*uH*cH⁻¹∈N := Subgroup.Normal.conj_mem inferInstance _ huN cH
    apply (hmem _).mpr
    have he : ((f.symm (Multiplicative.ofAdd (Hexacode.evenAction r.val w))):G)=
        (c:G)*(u:G)*(c:G)⁻¹ := by
      have hh := tripleSixPointCentralizerProjection_conjugate D a z c u
      rw [hcr] at hh
      change ((f.symm (Multiplicative.ofAdd (Hexacode.evenAction r.val (f u).toAdd))):G)=
        (c:G)*(u:G)*(c:G)⁻¹ at hh
      have hu : f u=Multiplicative.ofAdd w := f.apply_symm_apply _
      rw [hu] at hh
      exact hh
    have hh : (⟨(f.symm (Multiplicative.ofAdd (Hexacode.evenAction r.val w)):G),
        hUH (f.symm (Multiplicative.ofAdd (Hexacode.evenAction r.val w))).property⟩ : H)=
        cH*uH*cH⁻¹ := Subtype.ext he
    exact hh.symm ▸ hconj
  have hE : B≤subspaceStabilizer Hexacode.evenAction E := by
    intro g hg w
    constructor
    · intro hw
      have hh := stable g⁻¹ (B.inv_mem hg) (Hexacode.evenAction g w) hw
      simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] using hh
    · exact stable g hg w
  have hEne : E≠⊤ := by
    intro he
    apply hne
    apply _root_.eq_bot_iff.mpr
    intro x hx
    obtain ⟨w,hw⟩ := hℓ (Additive.ofMul (⟨x,hx⟩ : A))
    have hh : ℓ w=0 := by
      change w∈E
      rw [he]
      exact Submodule.mem_top
    have hx1 : (⟨x,hx⟩ : A)=1 := congrArg Additive.toMul (hw.symm.trans hh)
    exact congrArg Subtype.val hx1
  have hdim := Hexacode.weightFourResidualQuotient_finrank_two_or_four v
    (tripleSix_sylow_fixed_weightFour D a z hz hzT) E hPE hE hEne
  have hd : Module.finrank (ZMod 2) (hexacode ⧸ E)=Module.finrank (ZMod 2) (Additive A) :=
    (ℓ.quotKerEquivOfSurjective hℓ).finrank_eq
  have hcard := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive A)
  change Nat.card A=(Nat.card (ZMod 2))^Module.finrank (ZMod 2) (Additive A) at hcard
  rw [Nat.card_zmod] at hcard
  rw [hd] at hdim
  rcases hdim with hdim | hdim
  · left
    change Nat.card A=4
    simpa [hdim] using hcard
  · right
    change Nat.card A=16
    simpa [hdim] using hcard

/-- The original full action kernel has elementary U-image of rank two or
four, generated by the unchanged non-scalar cubic residual. -/
theorem original_tripleSix_central_closure_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z≠1)
    (hzT : (T : Subgroup G)≤centralizer ({(z:G)} : Set G))
    (hnot : ¬ U≤(centralizer ({(z:G)} : Set G)).pCoreIn 2) :
    let C := centralizer ({(z:G)} : Set G)
    let J := tripleSixWeightFourResidual K z
    let R := conjugateSpanBy U C
    let H := R ⊔ J ⊔ (T : Subgroup G)
    let V1 := tripleSixPoint D a z
    let W := conjugateSpanBy V1 R
    ∃ (N : Subgroup H) (hN : N.Normal),
      letI := hN
      (∀ x : H, x∈N ↔ ∀ w∈W, ⁅w,(x:G)⁆∈zpowers (z:G)) ∧
      pCore 2 (H ⧸ N)=⊥ ∧ (V1.subgroupOf H)≤N ∧
      let q := QuotientGroup.mk' N
      let A := (U.subgroupOf H).map q
      let Jstar := (J.subgroupOf H).map q
      A≠⊥ ∧ IsElementaryAbelian 2 A ∧ (Nat.card A=4 ∨ Nat.card A=16) ∧
        A=⁅A,Jstar⁆ ∧ Nat.card (Jstar ⧸ pCore 2 Jstar)=3 := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  have hUH : U≤H := D.le_sylow.trans le_sup_right
  have hJH : J≤H := le_sup_right.trans le_sup_left
  obtain ⟨N,hN,hmem,hcore,hVN,hne,helem,_,hmove⟩ :=
    original_tripleSix_central_closure_action h structural D a z hz hzT hnot
  let : N.Normal := hN
  let q := QuotientGroup.mk' N
  let A := (U.subgroupOf H).map q
  let Jstar := (J.subgroupOf H).map q
  change A=⁅A,Jstar⁆ at hmove
  have hJne : Jstar≠⊥ := by
    intro he
    apply hne
    simpa only [he,commutator_bot_right] using hmove
  let f : J →* Jstar := (q.subgroupMap (J.subgroupOf H)).comp
    (subgroupOfEquivOfLe hJH).symm.toMonoidHom
  have hf : Function.Surjective f :=
    (q.subgroupMap_surjective (J.subgroupOf H)).comp (subgroupOfEquivOfLe hJH).symm.surjective
  have hfn : f≠1 := by
    intro he
    apply hJne
    apply _root_.eq_bot_iff.mpr
    intro x hx
    obtain ⟨y,hy⟩ := hf ⟨x,hx⟩
    have hx1 : (⟨x,hx⟩ : Jstar)=1 := hy.symm.trans (congrArg (fun b : J →* Jstar => b y) he)
    exact congrArg Subtype.val hx1
  have hJ := original_tripleSix_weightFour_cubic_residual D a z hz hzT
  have hJcard : Nat.card (Jstar ⧸ pCore 2 Jstar)=3 :=
    cubic_core_quotient_of_twoPerfect_image hJ.2.2.1 hJ.2.2.2.1 f hf hfn
  exact ⟨N,hN,hmem,hcore,hVN,hne,helem,
    original_image_card D a z hz hzT H hUH hJH N hVN hne,hmove,hJcard⟩

end CFSG.Quasithin.Chapter12.Section07
