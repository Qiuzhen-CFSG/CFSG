module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureDegreeFourCore
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CoreSectionComponent
public import Theory.GroupAction.PerfectNaturalSection

/-!
# The original degree-four two-core centralizes the whole W

A literal normal C-component carrying the unchanged full linear image is
constructed inside the centralizer of O2(H)/W. Thompson's lemma on the
whole elementary W, followed by transitivity on its nonzero quotient
vectors, forces O2(H) to centralize W. The complete representation kernel
is retained, with no solvability or core identification imposed on it.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- In degree four, the literal whole two-core centralizes the unchanged
original elementary closure. -/
theorem original_tripleSix_central_closure_degreeFour_core_central
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K)
    (hW32 : Nat.card (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G))))=32) :
    let C := centralizer ({(z:G)} : Set G)
    let J := tripleSixWeightFourResidual K z
    let R := conjugateSpanBy U C
    let H := R ⊔ J ⊔ (T : Subgroup G)
    let W := conjugateSpanBy (tripleSixPoint D a z) R
    H.pCoreIn 2≤centralizer (W : Set G) := by
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
  let := hB.perfect
  have hBp : IsPPerfect 2 B := by
    intro N hN hp
    let : N.Normal := hN
    by_contra hn
    let : Nontrivial (B ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
    let : Group.IsPerfect (B ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (B ⧸ N) := hp.isNilpotent
    exact Group.IsPerfect.not_isSolvable (B ⧸ N) inferInstance
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
  have hfix := Theory.GroupAction.centralizes_of_perfect_full_natural_section B (pCore 2 H) WH
    hBp pCore_isPGroup hBcomm π hπ hπker r hBimage hπformula
    (by simp only [Module.finrank_pi,Fintype.card_fin]; decide)
  apply le_centralizer_iff.mp
  intro w hw q hq
  obtain ⟨q,hq,rfl⟩ := hq
  exact congrArg Subtype.val (hfix (show (⟨w,hWH hw⟩:H)∈WH from hw) q hq)

end CFSG.Quasithin.Chapter12.Section07
