module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorGenerationOneComplete
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualOvergroupCoreSource
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualA5CoreGeometry
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualActorPair
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLine

/-!
# The original generation-two tensor overgroup

The actual H-star subgroup has generation two. Its cubic Hall subgroup
extends to the order-nine Cartan. Centralization of the tensor line forces
the Cartan join to have nonzero two-core, so the zero-core line argument
and the nonzero-core Cartan-normalization argument fit together without an
additional core assumption. The genuine A5/A5 amalgam containment then
supplies the nonzero core of the original overgroup.

The resulting data retain the literal old residual, Cartan, and overgroup.
The action theorems use the original Omega orbit and its centralizer
quotient. No normality of the H-conjugate span under L is asserted.
The three earlier source inputs remain explicit; the later model-row
exclusions are separate obligations.

Source: Aschbacher--Smith 9.2.7 and 9.3.1--7, printed pp.731--734.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The remaining nonzero-core part of source 9.3.1, on the actual Cartan. -/
@[expose] def NonzeroCoreCartanNormalization : Prop :=
  ∀ {H : Subgroup G}, H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal →
    1 < generationParameter H → ∀ A B : Subgroup G,
    A ≤ sourceOrbitBorel T L → Nat.card A = 9 → IsElementaryAbelian 3 A →
    Nat.card B = 3 → B ≤ (pResidual 2 H).map H.subtype →
    B = A ⊓ centralizer (m.tensorLine : Set G) →
    pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥ →
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G)

/-- The independent zero-core mixed A5/S3 branch of source 9.3.1. -/
@[expose] def ZeroCoreLineCentralization : Prop :=
  ∀ {H : Subgroup G}, H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal →
    1 < generationParameter H → ∀ A B : Subgroup G,
    A ≤ sourceOrbitBorel T L → Nat.card A = 9 → IsElementaryAbelian 3 A →
    Nat.card B = 3 → B ≤ (pResidual 2 H).map H.subtype →
    B = A ⊓ centralizer (m.tensorLine : Set G) →
    pCore 2 (H ⊔ A : Subgroup G) = ⊥ →
    (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G)

/-- The A5/A5 specialization of F.1.12 used in source 9.3.3. -/
@[expose] def A5PairContainment (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (P : Fin 2 → Subgroup G) (S : Subgroup G),
    ChapterF.Source.HypothesisF11 P S → IsQuasithin (ChapterF.Source.generated P S) →
    (∀ i, Nonempty ((P i ⧸ pCore 2 (P i)) ≃* alternatingGroup (Fin 5))) →
    (∃ j, ChapterF.Source.borel (P j) S ≤ normalizer (S : Set G)) → ∀ i, S ≤ P i

/-- A centralized tensor line is a nontrivial normal two-subgroup of HA. -/
theorem cartan_core_ne_bot_of_line_centralizes
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (A : Subgroup G) (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G)) :
    pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥ := by
  have hHU : H ≤ normalizer (m.tensorLine : Set G) := by
    rw [← source_hstar_residual_sup_sylow hH]
    exact sup_le (hKU.trans (Subgroup.centralizer_le_normalizer _)) m.tensorLine_normalized
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hU : m.tensorLine ≤ (H ⊔ A).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsPGroup.of_card (n := 2) m.card_tensorLine)
      (m.tensorLine_le_sylow.trans (hTH.trans le_sup_left)) (sup_le hHU hAU)
  intro hz
  apply m.tensorLine_ne_bot
  apply le_bot_iff.mp
  simpa only [pCoreIn, hz, Subgroup.map_bot] using hU

/-- The zero-core line theorem discharges the core premise of the
independent Cartan-normalization theorem. -/
theorem cartan_normalization_and_line
    (hnormal : m.NonzeroCoreCartanNormalization)
    (hzero : m.ZeroCoreLineCentralization)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G)) :
    pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥ ∧
      A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G) := by
  have hc : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥ := by
    intro hz
    exact m.cartan_core_ne_bot_of_line_centralizes hH A
      (hAB.trans m.borel_normalizes_tensorLine)
      (hzero hH hlarge A B hAB hA9 hAe hB3 hBK hBC hz) hz
  have hn := hnormal hH hlarge A B hAB hA9 hAe hB3 hBK hBC hc
  exact ⟨hc,hn,m.old_residual_centralizes_tensorLine_of_cartan_normalizes
    hH A B hAB hA9 hAe hB3 hBC hn⟩

/-- Source data for the actual overgroup M0=⟨L,O²(H),N_T(L)⟩.
Every field is constructed below from the three earlier source inputs. -/
structure GenerationTwoOvergroup where
  H : Subgroup G
  hstar : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal
  generation_two : generationParameter H = 2
  A : Subgroup G
  B : Subgroup G
  borel : A ≤ sourceOrbitBorel T L
  card_cartan : Nat.card A = 9
  elementary_cartan : IsElementaryAbelian 3 A
  card_hall : Nat.card B = 3
  cyclic_hall : IsCyclic B
  hall : IsHallSubgroup oddPrimes (B.subgroupOf (H ⊓ D.maximalLocal))
  hall_le_cartan : B ≤ A
  hall_le_residual : B ≤ (pResidual 2 H).map H.subtype
  hall_centralizer : B = A ⊓ centralizer (m.tensorLine : Set G)
  cartan_core_ne_bot : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥
  cartan_normalizes : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G)
  line_centralized : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G)
  M : Subgroup G
  generated : M = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
    ((T : Subgroup G) ⊓ normalizer (L : Set G))
  core_ne_bot : pCore 2 M ≠ ⊥

/-- Construct the genuine overgroup, using F.1.12 only for its actual
A5 pair and deriving both Cartan and residual markings from the tensor. -/
theorem exists_generationTwoOvergroup
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hnormal : m.NonzeroCoreCartanNormalization)
    (hzero : m.ZeroCoreLineCentralization) (hcontain : A5PairContainment G) :
    Nonempty (m.GenerationTwoOvergroup) := by
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  have hg := m.tensor_hstar_generation_eq_two hout hH
  have hlarge : 1 < generationParameter H := by omega
  obtain ⟨_,B,A,_,hBK,hBA,hAB,hA9,hAe,hB3,hBc,hhall,hBC⟩ := m.hstar_cartan hH hlarge
  obtain ⟨hAc,hAK,hKU⟩ := m.cartan_normalization_and_line hnormal hzero
    hH hlarge A B hAB hA9 hAe hB3 hBK hBC
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  let M := (L ⊔ (pResidual 2 H).map H.subtype) ⊔
    ((T : Subgroup G) ⊓ normalizer (L : Set G))
  have hcore := m.old_residual_overgroup_core_ne_bot_of_rank_two_containment
    hH eK A B hAB hA9 hBA hBK hB3 hAK M rfl hcontain
  exact ⟨⟨H,hH,hg,A,B,hAB,hA9,hAe,hB3,hBc,hhall,hBA,hBK,hBC,hAc,hAK,hKU,M,rfl,hcore⟩⟩

namespace GenerationTwoOvergroup
variable {m} (c : m.GenerationTwoOvergroup)

theorem large : 1 < generationParameter c.H := by rw [c.generation_two]; decide

/-- The literal overgroup escapes M because its old residual does. -/
theorem outside : ¬ c.M ≤ D.maximalLocal := by
  intro hm
  exact source_hstar_residual_not_le (le_normalizer_componentOrbit L T) c.hstar
    ((c.generated ▸ le_sup_of_le_left le_sup_right).trans hm)

/-- The original stabilizer is Sylow in this same overgroup. -/
theorem sylow : Chapter1.IsSylowIn 2
    ((T : Subgroup G) ⊓ normalizer (L : Set G)) c.M :=
  source_a5_local_outside_overgroup_sylow D e m.sylow_not_normalizes_component
    c.core_ne_bot (c.generated ▸ le_sup_of_le_left le_sup_left)
    (c.generated ▸ le_sup_right) c.outside

/-- Both original factors lie in the same literal residual component,
which supplements the original stabilizer in the overgroup. -/
theorem component_product :
    (pResidual 2 c.M).IsCComponent ∧
      L.subgroupOf c.M ≤ pResidual 2 c.M ∧
      ((pResidual 2 c.H).map c.H.subtype).subgroupOf c.M ≤ pResidual 2 c.M ∧
      ∀ g : c.M, ∃ k ∈ pResidual 2 c.M,
        ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M), k * r = g := by
  obtain ⟨eK⟩ := m.old_residual_a5 c.hstar c.large
  have hSyl := c.sylow.restrict le_sup_right
    (sup_le (c.generated ▸ le_sup_of_le_left le_sup_right) (c.generated ▸ le_sup_right))
  exact m.old_residual_component_product m.sylow_not_normalizes_component c.hstar eK hSyl
    c.M c.core_ne_bot c.generated c.line_centralized
    (m.old_residual_moves_tensorPlane c.hstar c.large)

/-- Retain the actual elementary H-span without asserting L-normality. -/
theorem elementary_span : IsElementaryAbelian 2 (ChapterD.conjugateSpan c.H D.fullModule) ∧
    ChapterD.conjugateSpan c.H D.fullModule ≤ (localJoin T L).pCoreIn 2 :=
  m.old_residual_span_elementary_le_local_core c.hstar c.large c.A c.B
    c.borel c.card_cartan c.hall_le_cartan c.hall_le_residual c.card_hall c.cartan_normalizes

/-- The complete four-field action selection on the original Omega orbit. -/
theorem fourField_models
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    m.tensorLine ≤ c.M.pCoreIn 2 ∧ c.M ∈ Chapter1.He G ∧
      generalizedFitting c.M = pCore 2 c.M ∧ center c.M = ⊥ ∧
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      m.tensorLine.subgroupOf c.M ≤ W ∧
      (pResidual 2 c.M).map (actionMk W) ≤ N ∧
      ChapterB.QuasisimpleSource.moved (ρ.comp N.subtype)
        (((pResidual 2 c.M).map (actionMk W)).subgroupOf N) = ⊤ ∧
      ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((pResidual 2 c.M).map (actionMk W)).subgroupOf N),
      SourceA5TensorExclusion.FourWayFourField (ρ.comp N.subtype)
        (((pResidual 2 c.M).map (actionMk W)).subgroupOf N) h.sectionData :=
  m.old_residual_overgroup_fourField_models_of_source_recognition c.hstar c.large hout
    c.M c.core_ne_bot c.generated c.line_centralized

/-- The surviving carriers refer to the literal residual action image,
not to an assumed identification of its kernel with a two-core. -/
theorem actor_models (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    let W := omegaOrbit (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal
      Nonempty (((pResidual 2 c.M).map (actionMk W)) ≃*
        SL(3,ChapterB.QuasisimpleSource.BinaryField.four.Carrier)) ∨
      Nonempty (((pResidual 2 c.M).map (actionMk W)) ≃*
        Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) ∨
      Nonempty (((pResidual 2 c.M).map (actionMk W)) ≃*
        Atlas.G2.Model ChapterB.QuasisimpleSource.BinaryField.four.Carrier) := by
  obtain ⟨_,_,_,_,hr,_,hKN,_,h,hs⟩ := c.fourField_models hout
  let := hr.normal
  let := hr.elementary
  refine ⟨hr,?_⟩
  let i := (subgroupOfEquivOfLe hKN).symm
  rcases hs.actor_models with ha | ha | ha
  · obtain ⟨a⟩ := ha
    exact Or.inl ⟨i.trans a⟩
  · obtain ⟨a⟩ := ha
    exact Or.inr (Or.inl ⟨i.trans a⟩)
  · obtain ⟨a⟩ := ha
    exact Or.inr (Or.inr ⟨i.trans a⟩)

end GenerationTwoOvergroup
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
