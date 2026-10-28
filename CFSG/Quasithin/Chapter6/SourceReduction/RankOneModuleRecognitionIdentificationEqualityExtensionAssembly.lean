module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionContracts
public import Theory.ElementaryAbelian.Join

/-!
# Conditional assembly of the equality extension and transfer argument

The centralizer product formula and elementary D make Q = O₂(LT)
elementary. The preparation module supplies D ≤ Q and D ∩ V = ⟨z⟩, and
maximal two-locality supplies normalizer control from the block result.
The remaining weak-closure, index and involution-fusion facts
then feed the literal elementary-four transfer exclusion.

Consequently D has order two, D = ⟨z⟩ and Q = V. Characteristic normality
of O₂(L) gives relative normality in M. Explicit quotient equivalences
transport the marked S₅ quotient and the centralizer quotient, preserving
the original quotient maps and the A₅ marking. This constructs CoreData
for the actual canonical P, without a splitting assumption.

The action, block and fusion structures are explicit intermediate inputs;
this conditional assembly does not establish their source producers.
Source: Aschbacher--Smith, proof of 6.2.13, printed pp.687--688.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

theorem equality_local_core_elementary_of_action
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hact : EqualityExtensionAction (T : Subgroup G) L R z)
    (hD : IsElementaryAbelian 2 (equalityCentralizer L R z)) :
    IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  rw [← equality_sylow_centralizer_eq_core h611 hnatural, hact.sylow_centralizer]
  let := h611.layer_elementary
  let := hD
  apply IsElementaryAbelian.sup_of_le_centralizer
  intro x hx v hv
  obtain ⟨xH, hxH, rfl⟩ := hx
  obtain ⟨vH, hvK, rfl⟩ := equality_layer_le_closure h611 hz hv
  exact congrArg Subtype.val (mem_centralizer_iff.mp hxH vH hvK)

theorem LocalAnalysis.equality_four_excluded_of_action_and_fusion
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcenter : coreCenter (equalityCore L R z) =
      (zpowers z).subgroupOf (centralizer ({z} : Set G)))
    (hact : EqualityExtensionAction (T : Subgroup G) L R z)
    (hblock : EqualityExtensionBlock (T : Subgroup G) L M R z)
    (hf : EqualityExtensionFourFusion (T : Subgroup G) L R z) :
    Nat.card (equalityCentralizer L R z) ≠ 4 := by
  exact elementary_four_centralizer_excluded h611 hz horder
    (equality_local_core_elementary_of_action h611 hnatural hz hact hblock.elementary)
    (A.equality_centralizer_le_local_core h611 hnatural hz hTH)
    (A.equality_centralizer_inf_layer h611 hz hcenter).le
    hf.weak_closure
    (equality_local_core_normalizer_normalizes_layer h611 hblock.kernel_normal hblock.layer_core)
    hf.index hf.fusion

theorem equality_layer_normal_of_core
    (h611 : Hypothesis611 κ T L M R n) (hV : layer L R = L.pCoreIn 2) :
    ((layer L R).subgroupOf M).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer (h611.layer_le_L.trans h611.L_le)).mpr
  rw [hV]
  exact ((normal_subgroupOf_iff_le_normalizer h611.L_le).mp h611.L_normal).trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))

/-- Conditional assembly of the extension calculation and its transfer
contradiction. The three intermediate inputs remain source obligations. -/
theorem LocalAnalysis.equality_extension_of_action_block_fusion
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hplus : Nonempty (QuaternionCentralProductData (equalityCore L R z)))
    (hcenter : coreCenter (equalityCore L R z) =
      (zpowers z).subgroupOf (centralizer ({z} : Set G)))
    (hact : EqualityExtensionAction (T : Subgroup G) L R z)
    (hblock : EqualityExtensionBlock (T : Subgroup G) L M R z)
    (hfour : Nat.card (equalityCentralizer L R z) = 4 →
      EqualityExtensionFourFusion (T : Subgroup G) L R z) :
    ∃ hnormal : ((layer L R).subgroupOf M).Normal,
      @CompatibleSymmetricFiveQuotient M inferInstance ((layer L R).subgroupOf M)
        (L.subgroupOf M) hnormal ∧
      CoreData (equalityCore L R z) ∧
      equalityCentralizer L R z = zpowers z ∧
      (L ⊔ (T : Subgroup G)).pCoreIn 2 = layer L R := by
  have hcard : Nat.card (equalityCentralizer L R z) = 2 := by
    rcases hblock.card with htwo | hfour'
    · exact htwo
    · exact (A.equality_four_excluded_of_action_and_fusion h611 hnatural hz horder hTH
        hcenter hact hblock (hfour hfour') hfour').elim
  have hD : equalityCentralizer L R z = zpowers z := by
    apply (eq_of_le_of_card_ge (equality_line_le_centralizer z L R) ?_).symm
    rw [Nat.card_zpowers, horder, hcard]
  have hQ : (L ⊔ (T : Subgroup G)).pCoreIn 2 = layer L R := by
    rw [← equality_sylow_centralizer_eq_core h611 hnatural, hact.sylow_centralizer,
      hD, sup_eq_left.mpr (zpowers_le.mpr hz.1)]
  have hDP : centralizer
      (equalityLayerClosure L R z : Set (centralizer ({z} : Set G))) ≤ equalityCore L R z := by
    intro x hx
    have hz' : (x : G) ∈ zpowers z := hD ▸ mem_map_of_mem _ hx
    have hc : x ∈ coreCenter (equalityCore L R z) := by rw [hcenter]; exact hz'
    exact map_subtype_le _ hc
  have hP : CoreData (equalityCore L R z) := by
    refine ⟨hplus, ?_, ?_, hact.cubic_centralizer⟩
    · obtain ⟨e⟩ := hact.quotient
      exact ⟨(QuotientGroup.quotientMulEquivOfEq (sup_eq_left.mpr hDP).symm).trans e⟩
    · rw [hact.core_centralizer]
      exact hDP
  let hnormal := equality_layer_normal_of_core h611 hblock.layer_core
  refine ⟨hnormal, ?_, hP, hD, hQ⟩
  refine ⟨subgroupOf_mono _ h611.layer_le_L, ?_⟩
  let := hblock.kernel_normal
  obtain ⟨e, he⟩ := hblock.marked_quotient
  let c : (M ⧸ (layer L R).subgroupOf M) ≃*
      (M ⧸ ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf M) :=
    QuotientGroup.quotientMulEquivOfEq (congrArg (fun B : Subgroup G => B.subgroupOf M) hQ.symm)
  refine ⟨c.trans e, ?_⟩
  have hm : (c.trans e).toMonoidHom.comp (QuotientGroup.mk' ((layer L R).subgroupOf M)) =
      e.toMonoidHom.comp (QuotientGroup.mk' (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf M)) := by
    apply MonoidHom.ext
    intro m
    change e (c (QuotientGroup.mk' ((layer L R).subgroupOf M) m)) =
      e (QuotientGroup.mk' (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf M) m)
    exact congrArg e (QuotientGroup.quotientMulEquivOfEq_mk _ m)
  rw [hm]
  exact he

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
