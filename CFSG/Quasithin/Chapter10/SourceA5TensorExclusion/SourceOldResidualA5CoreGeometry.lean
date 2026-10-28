module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualOvergroupCoreSetup
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartan
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Placement
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualRecognitionComplete
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanTwoCore.Tensor
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualA5CoreQuotient
public import Theory.Representation.OrthogonalFourPlusMatrix.CubicSylowLine
public import Theory.Representation.BinaryConjugationSection.DisplacementPreimage
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The tensor module and its old-residual orbit inside the two-cores

The original order-three Cartan subgroup centralizes the tensor line. Tensor
coordinates put its displacement of the full module in the derived subgroup
of the common Sylow subgroup. The A₅ residual quotient makes that derived
subgroup trivial modulo O₂(H∨A), and its cubic centralizer contains no
nonidentity two-element. Thus the full module lies in O₂(H∨A), hence O₂(H).
The genuine qrc theorem and tensor non-FF property then make its H-conjugate
span elementary. The original Sylow centralizer identity places the span in
O₂(L₀T).

The final source theorem uses the proved A₅ recognition and Cartan two-core
equality. The earlier Cartan normalization remains an explicit input; further
normality of this span under L is a separate part of the amalgam argument.
Source: Aschbacher–Smith, 9.3.1–9.3.3, printed pp.732–733.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterB ChapterE ClassicalOrthogonal.FourPlusMatrix
open SourceOldResidualOvergroup
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

private theorem tensor_cubic_commutator_mem
    (b : G) (hb : b ∈ localOrbit T L) (hb3 : b^3=1)
    (hbc : b ∈ centralizer (m.tensorLine : Set G)) (v : D.fullModule) :
    ⁅b,(v : G)⁆ ∈ ⁅⁅(T : Subgroup G) ⊓ localOrbit T L,zpowers b⁆,D.fullModule⁆ := by
  let R := localOrbit T L
  let S := (T : Subgroup G) ⊓ R
  let b₀ : R := ⟨b,hb⟩
  let C := ⁅S,zpowers b⁆
  have hSR : S ≤ R := inf_le_right
  have hCR : C ≤ R := by
    apply commutator_le.mpr
    intro s hs a ha
    exact R.mul_mem (R.mul_mem (R.mul_mem (hSR hs) ((zpowers_le.mpr hb) ha))
      (R.inv_mem (hSR hs))) (R.inv_mem ((zpowers_le.mpr hb) ha))
  have hCV : ⁅C,D.fullModule⁆ ≤ D.fullModule :=
    le_normalizer_iff_commutator_le_right.mp (hCR.trans m.sectionData.normalized)
  let M := normalizer (R : Set G)
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  obtain ⟨P,hP⟩ := (T.subtype hTM).exists_map_subtype_eq_inf_of_normalizes
    R.le_normalizer (show M ≤ normalizer (R : Set G) from le_rfl)
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] at hP
  let P₀ := P.mapSurjective m.onto
  have hfix : ∀ w ∈ fixedSpace Binary.action (P₀ : Subgroup Binary.G),
      Binary.action (m.quotient b₀) w = w := by
    intro w hw
    obtain ⟨z,hz⟩ := m.sectionData.onto (Multiplicative.ofAdd w)
    have hzw : (m.sectionData.coordinates z).toAdd = w := congrArg Multiplicative.toAdd hz
    have hzU : (z : G) ∈ m.tensorLine := by
      refine ⟨z.property,?_⟩
      intro s hs
      obtain ⟨p,hp,hps⟩ := hP.ge hs
      change (p : G)=s at hps
      subst s
      have hf := hw ⟨m.quotient p,mem_map_of_mem _ hp⟩
      change Binary.action (m.quotient p) w = w at hf
      have he := m.sectionData.equivariant p z
      change (m.sectionData.coordinates _).toAdd = Binary.action (m.quotient p)
        (m.sectionData.coordinates z).toAdd at he
      rw [hzw,hf] at he
      have he' := m.coordinates_injective (Multiplicative.toAdd.injective (he.trans hzw.symm))
      have he'' := congrArg Subtype.val he'
      exact mul_inv_eq_iff_eq_mul.mp he''
    have he := m.sectionData.equivariant b₀ z
    have hc : (⟨b*z*b⁻¹,
        (mem_normalizer_iff.mp (m.sectionData.normalized hb) z).mp z.property⟩ : D.fullModule)=z := by
      apply Subtype.ext
      change b * (z : G) * b⁻¹ = (z : G)
      rw [←hbc z hzU,mul_inv_cancel_right]
    rw [hc,hzw] at he
    exact he.symm
  have hb₀3 : (m.quotient b₀)^3=1 := by
    rw [←map_pow,show b₀^3=1 from Subtype.ext hb3,map_one]
  have hC : C.subgroupOf R = ⁅(P : Subgroup R),zpowers b₀⁆ := by
    apply map_injective R.subtype_injective
    rw [map_subgroupOf_eq_of_le hCR,map_commutator,hP,MonoidHom.map_zpowers]
    rfl
  have hV : m.sectionData.imageSpace D.fullModule = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨z,hz⟩ := m.sectionData.onto (Multiplicative.ofAdd w)
    exact (m.sectionData.mem_imageSpace_iff _ _).mpr
      ⟨z,z.property,congrArg Multiplicative.toAdd hz⟩
  have hi : m.sectionData.imageSpace ⁅C,D.fullModule⁆ =
      subspaceCommutator Binary.action ⊤ ⁅(P₀ : Subgroup Binary.G),zpowers (m.quotient b₀)⁆ := by
    rw [m.sectionData.imageSpace_commutator C D.fullModule hCR le_rfl,hV]
    change subspaceCommutator (Binary.action.comp m.quotient) ⊤ _ = _
    rw [subspaceCommutator_comp_map,hC,map_commutator,MonoidHom.map_zpowers]
    rfl
  have hm := Binary.sylow_line_cubic_displacement P₀
    (m.quotient b₀) hb₀3 hfix (m.sectionData.coordinates v).toAdd
  rw [←hi] at hm
  have hh := (m.sectionData.displacement_mem_imageSpace_iff ⁅C,D.fullModule⁆ hCV b₀ v).mp hm
  simpa only [sup_bot_eq] using hh


private theorem fullModule_le_commonTwo : D.fullModule ≤ commonTwo T L :=
  (le_inf m.fullModule_le_sylow
    (m.fullModule_le_component.trans (le_componentOrbit L T))).trans le_sup_left

theorem tensor_cubic_commutator_le_commonTwo_derived
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup G) (hBH : B ≤ H) (hBR : B ≤ sourceOrbitBorel T L)
    (hB3 : Nat.card B = 3) :
    ⁅B,D.fullModule⁆ ≤ ⁅commonTwo T L,commonTwo T L⁆ := by
  apply commutator_le.mpr
  intro b hb v hv
  have hb3 : b^3=1 := congrArg Subtype.val
    (show (⟨b,hb⟩ : B)^3=1 from hB3 ▸ pow_card_eq_one')
  have hbR : b ∈ localOrbit T L :=
    ((map_subtype_le _).trans inf_le_left) (hBR hb)
  have hbN : b ∈ normalizer (((T : Subgroup G) ⊓ localOrbit T L : Subgroup G) : Set G) :=
    ((map_subtype_le _).trans inf_le_right) (hBR hb)
  have hbC : b ∈ centralizer (m.tensorLine : Set G) :=
    m.hstar_cubic_centralizes_tensorLine hH b (hBH hb)
      (m.borel_normalizes_tensorLine (hBR hb)) hb3
  have hc : ⁅(T : Subgroup G) ⊓ localOrbit T L,zpowers b⁆ ≤ commonTwo T L :=
    (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hbN)).trans le_sup_left
  exact (commutator_mono hc m.fullModule_le_commonTwo)
    (m.tensor_cubic_commutator_mem b hbR hb3 hbC ⟨v,hv⟩)

omit m [Finite G] in
private theorem commonTwo_old_residual_core
    {H : Subgroup G}
    (A : Subgroup G)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (hS : commonTwo T L = ((T : Subgroup G) ⊓ (pResidual 2 H).map H.subtype) ⊔
      (H ⊔ A).pCoreIn 2) :
    let K := (pResidual 2 H).map H.subtype
    let R := (H ⊔ A).pCoreIn 2
    (K ⊔ R).pCoreIn 2 = R ∧ commonTwo T L ≤ K ⊔ R := by
  let K := (pResidual 2 H).map H.subtype
  let R := (H ⊔ A).pCoreIn 2
  have hHK : H ≤ normalizer (K : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
  have hKR : H ⊔ A ≤ normalizer (K : Set G) := sup_le hHK hAK
  have hRR : H ⊔ A ≤ normalizer (R : Set G) :=
    (H ⊔ A).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (H ⊔ A) (pCore 2 (H ⊔ A : Subgroup G)))
  have hXY : K ⊔ R ≤ H ⊔ A :=
    sup_le ((map_subtype_le _).trans le_sup_left) ((H ⊔ A).pCoreIn_le 2)
  have hXN : H ⊔ A ≤ normalizer ((K ⊔ R : Subgroup G) : Set G) :=
    (le_inf hKR hRR).trans (K.normalizer_inf_normalizer_le_normalizer_sup R)
  refine ⟨le_antisymm (pCoreIn_mono_of_normalizes hXY hXN)
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (H ⊔ A)) le_sup_right
      (hXY.trans hRR)), ?_⟩
  exact hS.le.trans (sup_le (inf_le_right.trans le_sup_left) le_sup_right)

/-- The actual cubic Cartan forces the tensor module into the core of H∨A. -/
theorem old_residual_fullModule_le_cartan_core
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G)) :
    D.fullModule ≤ (H ⊔ A).pCoreIn 2 := by
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  let K := (pResidual 2 H).map H.subtype
  let R := (H ⊔ A).pCoreIn 2
  have hS := m.source_cartan_twoCore_eq_old_residual hH eK A B hAB hA9 hBA hBK hB3 hAK
  obtain ⟨hc,hsY⟩ := commonTwo_old_residual_core A hAK hS
  obtain ⟨hder,hV⟩ := SourceA5TensorExclusion.a5_core_quotient_two_subgroup
    K (K ⊔ R) (commonTwo T L) B eK (by rw [hc])
    m.old_residual_commonTwo_isPGroup hsY hBK hB3
  rw [hc] at hder hV
  exact hV D.fullModule m.fullModule_le_commonTwo
    ((m.tensor_cubic_commutator_le_commonTwo_derived hH B
      (hBK.trans (map_subtype_le _)) (hBA.trans hAB) hB3).trans hder)

/-- The source Cartan core lies in the original Sylow and hence in O₂(H). -/
theorem old_residual_fullModule_le_twoCore_of_cartan
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G)) :
    D.fullModule ≤ H.pCoreIn 2 := by
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  have hS := m.source_cartan_twoCore_eq_old_residual hH eK A B hAB hA9 hBA hBK hB3 hAK
  have hRS : (H ⊔ A).pCoreIn 2 ≤ commonTwo T L := by
    rw [commonTwo,hS]
    exact le_sup_right
  have hRH : (H ⊔ A).pCoreIn 2 ≤ H :=
    hRS.trans ((m.old_residual_commonTwo_le_stabilizer.trans inf_le_left).trans hH.1.1.2)
  exact (m.old_residual_fullModule_le_cartan_core hH hlarge A B hAB hA9 hBA hBK hB3 hAK).trans
    ((le_inf hRH le_rfl).trans (inf_pCoreIn_le_of_le 2 le_sup_left))

open ChapterD ChapterD.UniqueFactor

/-- Core placement makes the actual conjugate span elementary and keeps it in the original local core. -/
theorem old_residual_span_elementary_le_local_core_of_placement
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hV : D.fullModule ≤ H.pCoreIn 2) :
    IsElementaryAbelian 2 (conjugateSpan H D.fullModule) ∧
      conjugateSpan H D.fullModule ≤ (localJoin T L).pCoreIn 2 := by
  let h := source_fullModule_qrcHypotheses D hH
  have hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → sourceFullModuleNormalizer D ≤ N →
      N = D.maximalLocal := fun N hN hle => source_fullModuleNormalizer_unique D hN hle
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  have hnf : letI := h.module_elementary
      ¬ IsFFModule (ChapterD.UniqueFactor.imageRepresentation (sourceFullModuleNormalizer D)
        D.fullModule h.module_normalized) :=
    m.fullModule_actionImage_notFF (sourceFullModuleNormalizer D)
      (le_sup_left.trans (source_localJoin_le_fullModuleNormalizer D)) inf_le_left
      (inf_le_left.trans D.maximalLocal_normalizes_fullModule)
  let := source_elementary_span_of_notFF d hV hnf
  refine ⟨inferInstance,?_⟩
  have hET : conjugateSpan H D.fullModule ≤ (T : Subgroup G) :=
    (span_le_right_core d hV).trans (right_core_le_sylow d)
  have hEC : conjugateSpan H D.fullModule ≤ centralizer (D.fullModule : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (le_conjugateSpan H D.fullModule))
  have hc := D.sylow_centralizer_module (source_module_nonsolvable_uniqueness D)
  rw [m.module_eq] at hc
  exact (le_inf hET hEC).trans hc.le

/-- The original H-orbit is elementary and lies in O₂(L₀T), under the earlier Cartan normalization. -/
theorem old_residual_span_elementary_le_local_core
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G)) :
    IsElementaryAbelian 2 (conjugateSpan H D.fullModule) ∧
      conjugateSpan H D.fullModule ≤ (localJoin T L).pCoreIn 2 :=
  m.old_residual_span_elementary_le_local_core_of_placement hH
    (m.old_residual_fullModule_le_twoCore_of_cartan hH hlarge A B hAB hA9 hBA hBK hB3 hAK)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
