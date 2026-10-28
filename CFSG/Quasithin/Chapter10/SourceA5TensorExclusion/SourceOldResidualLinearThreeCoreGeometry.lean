module
public import Theory.Representation.OrthogonalFourPlusMatrix.CubicSylowLine
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLinearThreeCoreGeometryRootAction
public import Theory.Representation.BinaryConjugationSection.DisplacementPreimage
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The full tensor module in the original PSL₃(4) two-core

A cubic in the original Cartan centralizes the tensor line. In the
four-dimensional field-four matrix model, its displacement lies in the
module commutator of its Sylow commutator. The literal quotient and
coordinate maps transport that containment to the original group, where
the Sylow--residual commutator already lies in O₂(H).

The actual PSL₃(4) cubic has no nonidentity fixed point on the full-module
image in the long-root group. Consequently the entire original module
lies in O₂(H). All cubic and Cartan premises in the final theorem are
supplied by the original H-star setup. This does not assert H-normality
of the module or finish the PSL₃(4) exclusion.

Source: Aschbacher--Smith, E.2.7 and 9.2.7, printed pp.219 and731--732;
the field-four cubic fixed-point calculation uses16.4.8, printed p.1188.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterB ChapterE ClassicalOrthogonal.FourPlusMatrix
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

/-- The original cubic Hall action on V factors through the Sylow intersection with the old residual. -/
theorem old_residual_linear_three_cubic_commutator_le_twoCore
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.sourceImage
        (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4)
    (B : Subgroup G) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBR : B ≤ sourceOrbitBorel T L) (hB3 : Nat.card B=3)
    (hBC : B ≤ centralizer (m.tensorLine : Set G)) :
    ⁅B,D.fullModule⁆ ≤ H.pCoreIn 2 := by
  let K := (pResidual 2 H).map H.subtype
  let S := (T : Subgroup G) ⊓ localOrbit T L
  have hHN : H ≤ normalizer (K : Set G) := by
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using
      (pResidual 2 H).le_normalizer_map H.subtype
  have hSK : S ≤ normalizer (K : Set G) := inf_le_left.trans (hH.1.1.2.trans hHN)
  have hBC' := m.old_residual_linear_three_sylow_residual_commutator_le_twoCore
    hH hlarge hK hm
  apply commutator_le.mpr
  intro b hb v hv
  have hb3 : b^3=1 := congrArg Subtype.val
    (show (⟨b,hb⟩ : B)^3=1 from hB3 ▸ pow_card_eq_one')
  have hbR : b ∈ localOrbit T L :=
    ((map_subtype_le _).trans inf_le_left) (hBR hb)
  have hbN : b ∈ normalizer (S : Set G) :=
    ((map_subtype_le _).trans inf_le_right) (hBR hb)
  have hCS : ⁅S,zpowers b⁆ ≤ S := le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hbN)
  have hCK : ⁅S,zpowers b⁆ ≤ K :=
    (commutator_mono le_rfl (zpowers_le.mpr (hBK hb))).trans
      (le_normalizer_iff_commutator_le_right.mp hSK)
  exact hBC' ((commutator_mono (le_inf (hCS.trans inf_le_left) hCK) le_rfl)
    (m.tensor_cubic_commutator_mem b hbR hb3 (hBC hb) ⟨v,hv⟩))

/-- In the original PSL₃(4) alternative the entire tensor module lies in the actual two-core. -/
theorem old_residual_linear_three_fullModule_le_twoCore
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.sourceImage
        (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4) :
    D.fullModule ≤ H.pCoreIn 2 := by
  obtain ⟨_,B,A,_,hBK,hBA,hAR,_,_,hB3,_,_,hBC⟩ := m.hstar_cartan hH hlarge
  have hcent : B ≤ centralizer (m.tensorLine : Set G) := hBC ▸ inf_le_right
  exact m.old_residual_linear_three_fullModule_le_twoCore_of_cubic_commutator hH hlarge hK hm
    B hBK hB3 (m.old_residual_linear_three_cubic_commutator_le_twoCore hH hlarge hK hm
      B hBK (hBA.trans hAR) hB3 hcent)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
