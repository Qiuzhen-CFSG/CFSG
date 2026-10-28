module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureDegreeFourCoreCentral
public import Theory.Representation.BinaryCentralNaturalKernel

/-!
# Excluding the original inner degree-four closure

The actual normal component has two-core kernel on the full linear quotient.
The proved core centralization descends its action on the entire W. Dual H1
vanishing and normality then identify the whole kernels on W and W/Z.
The unchanged U has quotient image order four but centralizer V1 of index
sixteen, a contradiction. No recognition or action-kernel premise is added.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The literal smaller closure in the original inner branch cannot have
order thirty-two. -/
theorem original_tripleSix_central_closure_not_card_thirtyTwo
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K)
    : Nat.card (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G))))≠32 := by
  intro hW32
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let W := conjugateSpanBy (tripleSixPoint D a z) R
  let Z := zpowers (z:G)
  obtain ⟨hHW,hZN,hr⟩ := original_tripleSix_central_closure_degreeFour_parabolic
    h structural D a z hz hzT hnot hinner hW32
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,e,r,hr,hformula,hker,hR,hU,b,hT,i,hJi⟩ := hr
  let := he
  let LinearActor := BinaryLinear.OuterCyclic.LinearGroup 4
  let : Finite LinearActor := Finite.of_injective
    (fun g : LinearActor => (g : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2))) DFunLike.coe_injective
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 4 (by decide)
  let : IsSimpleGroup LinearActor :=
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0<4)).symm.isSimpleGroup
  let : Group.IsPerfect LinearActor := BinaryLinear.linearGroup_isPerfect 4 (by decide)
  have hcenter : center LinearActor=⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun hh=>Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hh))
  let : IsQuasisimple LinearActor :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hcfg := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  have hWH : W≤H := hcfg.2.2.1.trans (pCoreIn_le 2 H)
  let WH := W.subgroupOf H
  let JH := J.subgroupOf H
  have hJH : J≤H := le_sup_right.trans le_sup_left
  let : WH.Normal := normal_subgroupOf_of_le_normalizer hHW
  let : IsElementaryAbelian 2 W :=
    (original_tripleSix_central_closure_elementary h structural D a z hz hzT hnot hinner).1
  let eW := subgroupOfEquivOfLe hWH
  let : IsElementaryAbelian 2 WH := IsElementaryAbelian.of_injective eW.toMonoidHom eW.injective
  let : IsElementaryAbelian 2 U := D.elementary
  have hzorder : orderOf (z:G)=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (z:G) z.property) (fun hh=>hz (Subtype.ext hh))
  have hH : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hcfg.1)).mp
      ((h.simpleQTKE.involution_centralizer_sqtk hzorder).subgroup (H.subgroupOf C))
  have hcomm : ⁅pCore 2 H,JH⁆≤WH := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,map_subgroupOf_eq_of_le hJH]
    exact original_tripleSix_central_closure_degreeFour_core h structural D a z hz hzT hnot hinner hW32
  have hJne : JH.map r≠⊥ := by
    intro hh
    have hc := BinaryLinear.OrderedResidualConjugators.four_node_cubic_core_length b i
    have hm := hc.2.1
    rw [←hJi,hh,mem_bot] at hm
    have ho := hc.1
    rw [hm,orderOf_one] at ho
    exact (by decide : (1:ℕ)≠3) ho
  obtain ⟨B,hB,hBn,hBimage,hBcomm⟩ :=
    ChapterA.Section03.cComponent_full_image_centralizes_core_section hH r hr WH JH hJne hcomm
  let : B.Normal := hBn
  let q := QuotientGroup.mk' (Z.subgroupOf W)
  let πW : W →* Multiplicative (Fin 4 → ZMod 2) := {
    toFun := fun w=>Multiplicative.ofAdd (e (Additive.ofMul (q w)))
    map_one' := by change e (Additive.ofMul (q 1))=0; rw [map_one]; exact e.map_zero
    map_mul' := by
      intro x y
      change e (Additive.ofMul (q (x*y)))=e (Additive.ofMul (q x))+e (Additive.ofMul (q y))
      rw [map_mul]
      exact e.map_add _ _ }
  let π := πW.comp eW.toMonoidHom
  have hπ : Function.Surjective π := by
    intro v
    obtain ⟨w,hw⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) (e.symm v.toAdd).toMul
    refine ⟨eW.symm w,?_⟩
    change πW (eW (eW.symm w))=v
    rw [eW.apply_symm_apply]
    change Multiplicative.ofAdd (e (Additive.ofMul (q w)))=v
    rw [hw]
    exact congrArg Multiplicative.ofAdd (e.apply_symm_apply v.toAdd)
  have hπker (w : WH) (hw : π w=1) : (w:H)∈center H := by
    have hwq : q (eW w)=1 := by
      apply Additive.ofMul.injective
      apply e.injective
      exact (congrArg Multiplicative.toAdd hw).trans e.map_zero.symm
    have hwZ : ((w:H):G)∈Z := (QuotientGroup.eq_one_iff (N:=Z.subgroupOf W) (eW w)).mp hwq
    have hHZ : H≤centralizer (Z : Set G) := by
      rw [show Z=zpowers (z:G) from rfl,zpowers_eq_closure,centralizer_closure]
      exact hcfg.1
    have hZC : Z≤centralizer (H : Set G) := le_centralizer_iff.mp hHZ
    exact mem_center_iff.mpr (fun g=>Subtype.ext ((hZC hwZ) g g.property))
  have hπformula (g : H) (w : WH) :
      (π ((MulAut.conjNormal g : MulAut WH) w)).toAdd=r g (π w).toAdd := by
    change e (Additive.ofMul (q (eW ((MulAut.conjNormal g : MulAut WH) w))))=
      r g (e (Additive.ofMul (q (eW w))))
    rw [hformula]
    rfl
  let rB := r.comp B.subtype
  have hrB : Function.Surjective rB := by
    intro g
    obtain ⟨b,hb,hbg⟩ := (show g∈B.map r from hBimage.symm ▸ mem_top g)
    exact ⟨⟨b,hb⟩,hbg⟩
  let e8 := (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0<4)).symm.trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  have hBk : rB.ker=pCore 2 B := by
    have hh := ChapterA.Section03.cComponent_alternating_eight_kernel hH hB
      (e8.toMonoidHom.comp rB) (e8.surjective.comp hrB)
    rw [MonoidHom.ker_comp_of_injective _ _ e8.injective] at hh
    exact hh
  have hcoreB : B.pCoreIn 2≤pCore 2 H := le_sSup
    ⟨inferInstanceAs ((pCore 2 B).map B.subtype).Normal,isPGroup_pCoreIn 2 B⟩
  have hkill : rB.ker≤((MulAut.conjNormal : H →* MulAut WH).comp B.subtype).ker := by
    intro b hb
    have hbQ : (b:H)∈pCore 2 H := hcoreB ⟨b,hBk ▸ hb,rfl⟩
    have hc := original_tripleSix_central_closure_degreeFour_core_central
      h structural D a z hz hzT hnot hinner hW32
    have hbC : ((b:H):G)∈centralizer (W : Set G) := hc ⟨b,hbQ,rfl⟩
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    apply Subtype.ext
    change ((b:H):G)*((w:H):G)*((b:H):G)⁻¹=((w:H):G)
    exact mul_inv_eq_of_eq_mul (hbC w w.property).symm
  have hfullker := Representation.kernel_fixes_of_normal_full_natural_central_section
    (by decide : 4≤4) WH B π hπ hπker r hBimage hπformula hkill
  have hUR : U≤R := le_conjugateSpanBy U C
  have hUH : U≤H := hUR.trans (le_sup_left.trans le_sup_left)
  have hfix := (original_tripleSix_central_closure_inner_intersections h structural D a z hz hzT hnot hinner).1
  have hkerU : r.ker ⊓ U.subgroupOf H=(tripleSixPoint D a z).subgroupOf H := by
    ext u
    constructor
    · rintro ⟨hu,huU⟩
      apply hfix.le
      refine ⟨huU,?_⟩
      intro w hw
      exact congrArg Subtype.val (hfullker hu ⟨w,hWH hw⟩ hw)
    · intro hu
      have hUu : (u:G)∈U := (tripleSixPoint_properties D a z hz).2.1 hu
      refine ⟨(hker u).mpr ?_,hUu⟩
      intro w hw
      have hc : w*(u:G)=(u:G)*w := (hfix.ge hu).2 w hw
      have hc0 : ⁅w,(u:G)⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr hc
      rw [hc0]
      exact one_mem _
  have hindex : r.ker.relIndex (U.subgroupOf H)=16 := by
    rw [←inf_relIndex_right,hkerU]
    rw [←relIndex_map_map_of_injective _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le ((tripleSixPoint_properties D a z hz).2.1.trans hUH),
      map_subgroupOf_eq_of_le hUH]
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (tripleSixPoint D a z) U bot_le
      (tripleSixPoint_properties D a z hz).2.1
    rw [relIndex_bot_left,relIndex_bot_left,(tripleSixPoint_properties D a z hz).2.2.1,
      Nat.card_congr (tripleSixPointCoordinates D a).toEquiv] at hh
    change 4*(tripleSixPoint D a z).relIndex U=Nat.card Atlas.Codes.hexacode at hh
    rw [Atlas.Codes.hexacode_card] at hh
    omega
  rw [relIndex_ker,hU] at hindex
  contradiction

/-- The unchanged original inner closure has precisely sixteen elements. -/
theorem original_tripleSix_central_closure_inner_card_sixteen
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K)
    : Nat.card (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G))))=16 := by
  exact (original_tripleSix_central_closure_inner_intersections h structural D a z hz hzT hnot hinner).2.2.2.resolve_right
    (original_tripleSix_central_closure_not_card_thirtyTwo h structural D a z hz hzT hnot hinner)

end CFSG.Quasithin.Chapter12.Section07
