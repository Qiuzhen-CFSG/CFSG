module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourComponentSetup
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFullReducedOmega
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin
public import Theory.GroupTheory.ReducedNormal.ComponentSeed

/-!
# Placement of the original full Hermitian module in the C.2.7 radical

The original full reduced subgroup B is its moved layer, hence lies in L.
T normalizes LR and its core Q*. Thus Q* lies in O₂(LT), whose omega-center
is B. Characteristic two of LR gives B ≤ Q*, and radical saturation gives
Q* ≤ R. The actual component-kernel theorem also makes B reduced in LR.

Source: Aschbacher--Smith 6.1.4, printed p.666, with C.2.7.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ChapterA.Section04 RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ : Subgroup G} {n s : ℕ} [NeZero s]
local instance componentModuleFixedAlgebra : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.fixedField s) := ZMod.algebra _ 2
local instance componentModuleBinaryModule : Module (ZMod 2) (OrthogonalFourMinus.FiniteModel.Space s) :=
  Module.compHom (OrthogonalFourMinus.FiniteModel.Space s) (algebraMap (ZMod 2) (OrthogonalFourMinus.FiniteModel.fixedField s))

/-- C.2.7 acts on the literal full R₂(LT), which lies in its actual radical
and is reduced inside L O₂(M₁). No star-module identification is required. -/
theorem full_reduced_hermitian_component_module
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian s)) (hs : 1 < s)
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hF : twoGeneralizedFittingPreimage M₁ ≤ M) :
    let R := M₁.pCoreIn 2
    let B := reducedSubgroup (L ⊔ (T : Subgroup G))
    B ≤ (L ⊔ R).pCoreIn 2 ∧ (L ⊔ R).pCoreIn 2 ≤ R ∧
      IsPReduced 2 (B.subgroupOf (L ⊔ R)) := by
  let R := M₁.pCoreIn 2
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  let J := L ⊔ R
  let U := B.subgroupOf J
  have hi := full_reduced_hermitian_component_input h hout hm hs hM₁ hCM₁ hF
  have hT₁ : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have hRT : R ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hT₁] using
      pCoreIn_le_sylow M₁ (T.subtype hT₁)
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := hT₁.trans
    (M₁.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M₁ (pCore 2 M₁)))
  have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) :=
    (le_inf h.sylow_normalizes_L hTR).trans (normalizer_inf_normalizer_le_normalizer_sup L R)
  have hJLT : J ≤ L ⊔ (T : Subgroup G) := sup_le le_sup_left (hRT.trans le_sup_right)
  have hQ : J.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J) ((pCoreIn_le 2 J).trans hJLT)
      ((sup_le (le_sup_left.trans J.le_normalizer) hTJ).trans
        (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hBL : B ≤ L := by
    change reducedSubgroup (L ⊔ (T : Subgroup G)) ≤ L
    rw [←full_reduced_hermitian_layer_eq h hm]
    exact h.reduced_enlargement.layer_le_L
  have hBJ : B ≤ J := hBL.trans le_sup_left
  have hBC : B ≤ centralizer (J.pCoreIn 2 : Set G) := by
    intro b hb q hq
    have hbO := (mem_omegaOneCenterAmbient_iff _ _).mp
      (h.reduced_enlargement_eq_omega_core ▸
        (show b ∈ reducedSubgroup (L ⊔ (T : Subgroup G)) from hb))
    exact hbO.2.2 q (hQ hq)
  have hchar : centralizer (pCore 2 J : Set J) ≤ pCore 2 J :=
    centralizer_pCore_sup_le 2 L R
      (by rw [←hi.fitting]; exact centralizer_generalizedFitting_le L)
      (isPGroup_pCoreIn 2 M₁) hi.normalizes
  have hBQ : B ≤ J.pCoreIn 2 := by
    intro b hb
    have hbC : (⟨b,hBJ hb⟩ : J) ∈ centralizer (pCore 2 J : Set J) := by
      intro q hq
      exact Subtype.ext (hBC hb q (mem_map_of_mem J.subtype hq))
    exact mem_map_of_mem J.subtype (hchar hbC)
  let := h.L_normal
  have hQR : J.pCoreIn 2 ≤ R := ChapterC.C27Source.source_joinCore_le_radical hi
  have hBN : J ≤ normalizer (B : Set G) :=
    hJLT.trans (reduced_normalizes (reducedSubgroup_mem (L ⊔ (T : Subgroup G))))
  let : U.Normal := normal_subgroupOf_of_le_normalizer hBN
  let : IsElementaryAbelian 2 B := (reducedSubgroup_mem (L ⊔ (T : Subgroup G))).2.1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hBJ).toMonoidHom (subgroupOfEquivOfLe hBJ).injective
  let K := L.subgroupOf J
  let : K.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hi.normalizes)
  let e := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let := hi.quasisimple
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hK : K.IsCComponent := hi.component.2.subgroupOf_of_le le_sup_left hi.join_le
  have hgen : K ⊔ R.subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup (show L ≤ J from le_sup_left) le_sup_right, subgroupOf_self]
  have hQC : pCore 2 J ≤ centralizer (U : Set J) := by
    intro q hq b hb
    exact Subtype.ext ((hBC hb q (mem_map_of_mem J.subtype hq)).symm)
  have hmove : ⁅U,K⁆ ≠ ⊥ := by
    intro hz
    have hh := congrArg (map J.subtype) hz
    rw [map_commutator, map_subgroupOf_eq_of_le hBJ,
      map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left), Subgroup.map_bot] at hh
    exact h.reduced_enlargement_nontrivial hh
  refine ⟨hBQ,hQR,⟨inferInstance,inferInstance,?_⟩⟩
  apply (QuasisimpleKernel.normal_kernel_structure K (R.subgroupOf J)
    (centralizer (U : Set J)) hK (isPGroup_pCoreIn 2 M₁).comap_subtype hgen hQC ?_).2
  intro hh
  exact hmove (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
