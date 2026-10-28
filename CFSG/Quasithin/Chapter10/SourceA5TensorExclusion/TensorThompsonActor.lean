module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorThompsonSource
public import Theory.Representation.BinaryConjugationSection.FixedIndex
public import CFSG.Quasithin.ChapterB.Section02.RankLifting
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Embedding
public import Theory.GroupAction.NormalPChiefSeries.FixedCodimension
public import Theory.Representation.OrthogonalFourPlusMatrix.NearOffenderComplete

/-!
# The original Sylow action contains a rank-two involution

The tensor coordinates identify the actual maximal-local action with a
subgroup of the binary determinant-module normalizer. Its kernel is the
literal full-module centralizer. A moving member of the first Thompson
family therefore maps to a nontrivial elementary near-offender, by B.2.4.
The structural matrix calculation then supplies an involution of binary
displacement rank two in that same Sylow image.

The lifted Sylow element need not itself have order two: the conclusions
concern its action on the original full module.

Source: Aschbacher--Smith 9.2.1 and 9.2.4(2), printed p.730,
using B.2.4 and the field-four determinant-module case of H.1.1.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

def maximalNormalizerAction : D.maximalLocal →* linearNormalizer Binary.action := by
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Binary.V
  let q := e.symm.toMonoidHom.comp m.maximalAction
  have hi : Binary.linearAction.range.map e.symm.toMonoidHom = actionImage Binary.action := by
    ext a
    constructor
    · rintro ⟨_,⟨g,rfl⟩,rfl⟩
      refine ⟨g,?_⟩
      apply Units.ext
      apply LinearMap.ext
      intro v
      exact (Binary.linearAction_apply g v).symm
    · rintro ⟨g,rfl⟩
      refine ⟨Binary.linearAction g,⟨g,rfl⟩,?_⟩
      apply Units.ext
      apply LinearMap.ext
      intro v
      exact Binary.linearAction_apply g v
  refine q.codRestrict _ (fun x => ?_)
  have h := Subgroup.le_normalizer_map e.symm.toMonoidHom
    (Subgroup.mem_map_of_mem e.symm.toMonoidHom (m.maximalAction_mem_normalizer x))
  rw [hi] at h
  exact h

theorem maximalNormalizerAction_apply (x : D.maximalLocal) (v : Binary.V) :
    normalizerRepresentation Binary.action (m.maximalNormalizerAction x) v =
      m.maximalAction x v := by rfl

theorem maximalNormalizerAction_coordinates (x : D.maximalLocal) (v : D.fullModule) :
    normalizerRepresentation Binary.action (m.maximalNormalizerAction x)
        (m.sectionData.coordinates v).toAdd =
      (m.sectionData.coordinates (D.fullModule.normalizerMonoidHom
        ⟨x,D.maximalLocal_normalizes_fullModule x.property⟩ v)).toAdd :=
  m.maximalAction_coordinates x v

theorem maximalNormalizerAction_ker :
    m.maximalNormalizerAction.ker =
      centralizer (D.fullModule.subgroupOf D.maximalLocal : Set D.maximalLocal) := by
  have hVM : D.fullModule ≤ D.maximalLocal :=
    m.fullModule_le_sylow.trans m.tensor_hypothesisE61.sylow_le
  ext x
  constructor
  · intro hx a ha
    let v : D.fullModule := ⟨a,ha⟩
    have hc := m.maximalNormalizerAction_coordinates x v
    rw [show m.maximalNormalizerAction x = 1 from hx,map_one] at hc
    have hv := m.coordinates_injective (Multiplicative.toAdd.injective hc)
    have hh := congrArg Subtype.val hv
    change (a : G) = (x : G)*(a : G)*(x : G)⁻¹ at hh
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  · intro hx
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro w
    obtain ⟨v,hv⟩ := m.sectionData.onto (Multiplicative.ofAdd w)
    have hw : (m.sectionData.coordinates v).toAdd = w := congrArg Multiplicative.toAdd hv
    change normalizerRepresentation Binary.action (m.maximalNormalizerAction x) w = w
    rw [←hw,m.maximalNormalizerAction_coordinates]
    apply congrArg Multiplicative.toAdd
    apply congrArg m.sectionData.coordinates
    apply Subtype.ext
    change (x : G)*(v : G)*(x : G)⁻¹ = v
    have hh := congrArg Subtype.val (hx ⟨v,hVM v.property⟩ v.property)
    change (v : G)*(x : G) = (x : G)*(v : G) at hh
    rw [←hh,mul_inv_cancel_right]


private theorem near_maximal_image_bound
    (A : Subgroup D.maximalLocal)
    (hA : A ∈ ChapterB.thompsonFamily ((T : Subgroup G).subgroupOf D.maximalLocal) 1)
    (hne : A.map m.maximalNormalizerAction ≠ ⊥) :
    fixedCodim (normalizerRepresentation Binary.action) (A.map m.maximalNormalizerAction) ≤
      rank (A.map m.maximalNormalizerAction) + 1 := by
  let U := D.fullModule.subgroupOf D.maximalLocal
  have hVM : D.fullModule ≤ D.maximalLocal :=
    m.fullModule_le_sylow.trans m.tensor_hypothesisE61.sylow_le
  let : IsElementaryAbelian 2 D.fullModule := m.fullModule_elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVM
  let : U.Normal := normal_subgroupOf_of_le_normalizer D.maximalLocal_normalizes_fullModule
  let : IsElementaryAbelian 2 A := hA.2.1
  let c : U ≃* Multiplicative Binary.V :=
    (subgroupOfEquivOfLe hVM).trans
      (MulEquiv.ofBijective m.sectionData.coordinates ⟨m.coordinates_injective,m.sectionData.onto⟩)
  let E : Additive U ≃ₗ[ZMod 2] Binary.V :=
    { toFun := fun v => (c v.toMul).toAdd
      invFun := fun w => Additive.ofMul (c.symm (Multiplicative.ofAdd w))
      left_inv := fun _ => congrArg Additive.ofMul (c.symm_apply_apply _)
      right_inv := fun _ => congrArg Multiplicative.toAdd (c.apply_symm_apply _)
      map_add' := fun _ _ => congrArg Multiplicative.toAdd (c.map_mul _ _)
      map_smul' := ZMod.map_smul
        ({ toFun := fun v : Additive U => (c v.toMul).toAdd
           map_zero' := congrArg Multiplicative.toAdd c.map_one
           map_add' := fun _ _ => congrArg Multiplicative.toAdd (c.map_mul _ _) } :
             Additive U →+ Binary.V) }
  let ρ := NoncentralChiefRefinement.normalRepresentation U
  have hE (x : D.maximalLocal) (v : Additive U) :
      E (ρ x v) = normalizerRepresentation Binary.action (m.maximalNormalizerAction x) (E v) := by
    exact (m.maximalNormalizerAction_coordinates x ((subgroupOfEquivOfLe hVM) v.toMul)).symm
  have hb := ChapterB.lemma_B_2_4_1 ((T : Subgroup G).subgroupOf D.maximalLocal)
    U A (fun _ hx => m.fullModule_le_sylow hx) hA.1 1
    (by rw [hA.2.2.2,Nat.log_pow (by decide : 1 < 2)]; rfl)
    m.maximalNormalizerAction m.maximalNormalizerAction_ker hne
  rw [← NoncentralChiefRefinement.normalRepresentation_fixedCodim_eq_rank_difference U A] at hb
  have he := fixedCodim_map_equivariant ρ (normalizerRepresentation Binary.action)
    m.maximalNormalizerAction E hE A
  change fixedCodim ρ A - 1 ≤ rank (A.map m.maximalNormalizerAction) at hb
  rw [he] at hb
  omega

/-- The original moving J₁ family supplies a near-offender inside the actual Sylow action. -/
theorem exists_near_offender_of_generation_one
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hgen : generationParameter H = 1) :
    ∃ A : Subgroup (linearNormalizer Binary.action),
      A ≤ ((T : Subgroup G).subgroupOf D.maximalLocal).map m.maximalNormalizerAction ∧
      IsElementaryTwo A ∧
      fixedCodim (normalizerRepresentation Binary.action) A ≤ rank A + 1 := by
  have hmove := m.thompson_one_moves_of_generation_one hout hH hgen
  obtain ⟨B,hB,hmoveB⟩ : ∃ B ∈ ChapterB.thompsonFamily (T : Subgroup G) 1,
      ¬ B ≤ centralizer (D.fullModule : Set G) := by
    by_contra! h
    exact hmove (sSup_le h)
  have hTM := m.tensor_hypothesisE61.sylow_le
  have hBM := hB.1.trans hTM
  let A := B.subgroupOf D.maximalLocal
  have hA : A ∈ ChapterB.thompsonFamily ((T : Subgroup G).subgroupOf D.maximalLocal) 1 := by
    apply (ChapterB.thompsonFamily_map_iff_of_injective D.maximalLocal.subtype
      D.maximalLocal.subtype_injective _ A 1).mp
    simpa only [A,map_subgroupOf_eq_of_le hBM,map_subgroupOf_eq_of_le hTM] using hB
  let : IsElementaryAbelian 2 A := hA.2.1
  have hne : A.map m.maximalNormalizerAction ≠ ⊥ := by
    intro hz
    apply hmoveB
    intro b hb v hv
    have hbC : (⟨b,hBM hb⟩ : D.maximalLocal) ∈
        centralizer (D.fullModule.subgroupOf D.maximalLocal : Set D.maximalLocal) := by
      rw [← m.maximalNormalizerAction_ker]
      exact ((Subgroup.map_eq_bot_iff A).mp hz) hb
    let vM : D.maximalLocal := ⟨v,hTM (m.fullModule_le_sylow hv)⟩
    exact congrArg Subtype.val (hbC vM hv)
  exact ⟨A.map m.maximalNormalizerAction,map_mono hA.1,
    ⟨hne,IsElementaryAbelian.map m.maximalNormalizerAction⟩,
    m.near_maximal_image_bound A hA hne⟩

/-- The rank-two involution belongs to the image of the original Sylow group. -/
theorem exists_rank_two_sylow_action_of_generation_one
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hgen : generationParameter H = 1) :
    ∃ t : D.maximalLocal, (t : G) ∈ (T : Subgroup G) ∧
      m.maximalAction t ≠ 1 ∧ m.maximalAction t * m.maximalAction t = 1 ∧
      operatorFixedCodim (m.maximalAction t).toLinearMap = 2 := by
  obtain ⟨A,hAT,hA,hnear⟩ := m.exists_near_offender_of_generation_one hout hH hgen
  obtain ⟨a,ha,hne,hsq,hrank⟩ :=
    Binary.exists_rank_two_involution_of_near_offender A hA hnear
  obtain ⟨t,ht,he⟩ := hAT ha
  rw [←he] at hne hsq hrank
  refine ⟨t,ht,?_,?_,hrank⟩
  · intro ht1
    apply hne
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    change normalizerRepresentation Binary.action (m.maximalNormalizerAction t) v = v
    rw [m.maximalNormalizerAction_apply,ht1]
    rfl
  · apply LinearEquiv.ext
    intro v
    change m.maximalAction t (m.maximalAction t v) = v
    have hs := congrArg
      (fun a : linearNormalizer Binary.action => normalizerRepresentation Binary.action a v) hsq
    simpa only [map_mul,Module.End.mul_apply,map_one,Module.End.one_apply,
      m.maximalNormalizerAction_apply,LinearEquiv.mul_apply] using hs

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
