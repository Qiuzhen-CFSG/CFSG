module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.PSLTwoSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.LocalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSixSource
public import CFSG.Quasithin.ChapterI.Section02.SuzukiInvolutions

/-!
# The original moving-component exclusion in 13.6.6

The complete 1.1.5 and A.3.8 source theorems construct the actual model
comparison. The rank-one residual theorem excludes PSL₂; the Suzuki
central-cover calculation supplies involution lifts and elementary centers.
The paired Borel contradiction then uses only the original module and
Baumann normalizer data. Consequently C_T(v) normalizes the literal ambient
image of every component of C_G(v).

The final consumer obtains the larger-field alternative from the proved
initial sieve. Its only earlier inputs are the original flag/module,
local-source and fusion hypotheses. No A.3.18, component-orbit certificate,
cover-lifting assumption or action-image conclusion is supplied by the caller.
The normalized-component branch is separate from this theorem.

Source: Aschbacher--Smith, proof of 13.6.6, printed pp.926--927.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
open A5Module InitialSieve SuzukiPair SymplecticBorel.LocalInverter
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

theorem localT_normalizes_of_largeField
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (c : LocalConfiguration (normalizer (L : Set G)) d.flag)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (K : Subgroup (Gv (markedV d.flag.module)))
    (hK : IsComponent (Gv (markedV d.flag.module)) K)
    (a : ActionData d.flag.module (T : Subgroup G) K) (hlarge : LargeField K a) :
    localT (T : Subgroup G) (markedV d.flag.module) ≤ X K := by
  by_contra hmove
  let b := c.initialSetup hG (hm.V_le_core.trans (map_subtype_le _)) d.V_le_T
  have h115 := source_model_action b
    (fun hG H P M z h D hD => Chapter1.lemma_1_1_5_three_knownSimple hG H P M z h D hD)
    K hK a
  have h121 := Chapter1.Section02.proposition_1_2_1_three_of_A_3_8
    earlierConjugates_knownSimple
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG b.local115.mem_H) hK.isCComponent
  obtain ⟨m, i⟩ := ModelComparison.sourceInput_of_largeField b b.oddCore_eq_bot
    K hK a h115 hmove h121 hlarge
  have hcard : Nat.card (residual d.flag.module ⧸ pCore 2 (residual d.flag.module)) = 3 := by
    let e : residual d.flag.module ≃* Lv L (markedV d.flag.module) :=
      subgroupOfEquivOfLe (Lv_le_Gv L (markedV d.flag.module))
    rw [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact c.residual_card
  obtain ⟨p, _, _⟩ := exists_suzukiPair_of_original_source b i hcard
  have hi := (ModelComparison.moving_index_and_model _ K i.moving i.localModels).1
  let KA := K.map (Gv (markedV d.flag.module)).subtype
  have hKA : IsComponent (Gv (markedV d.flag.module))
      (KA.subgroupOf (Gv (markedV d.flag.module))) := by
    have heq : KA.subgroupOf (Gv (markedV d.flag.module)) = K :=
      comap_map_eq_self_of_injective (Gv (markedV d.flag.module)).subtype_injective K
    rwa [heq]
  let : IsQuasisimple K := hK.2
  let : IsQuasisimple KA := IsQuasisimple.of_mulEquiv
    (K.equivMapOfInjective (Gv (markedV d.flag.module)).subtype
      (Gv (markedV d.flag.module)).subtype_injective)
  obtain ⟨hcenter, hlift⟩ := ChapterI.SuzukiInvolutionLifts.center_elementary_and_involutions_lift
    p.parameter (by have hh := p.positive; omega) (ambientFactorEquiv K p.model)
  let := hcenter
  obtain ⟨f⟩ := p.nonempty_ambientFactors
  obtain ⟨g, hg, hg3, hgN, hfield⟩ := p.ambientCubic hK hi
  obtain ⟨r, hr⟩ := d.flag_relabel
  have hρ : ∀ (n : normalizer (V : Set G)) (w : BinaryPermutation.FiveCentralizerGeometry.Space),
      MulAut.conj (n : G) (d.flag.module.map (Multiplicative.ofAdd w)) =
      d.flag.module.map (Multiplicative.ofAdd
        (BinaryPermutation.coreRepresentation (Fin 5) ((d.relabel r).normalizerAction n) w)) := by
    intro n w
    rw [hr]
    exact (d.relabel r).normalizer_equivariant n w
  obtain ⟨hLC, hCL, hkernel⟩ := source_local_centralizer_laws d.flag.module d.flag.action_kernel
  apply f.false_of_cubic_field_action c.reductions.centralizerSylow c.reductions.sylow_image
    (map_subtype_le K) hKA hlift
    (baumann_le_Tv_of_alternatives T V V₂ (markedV d.flag.module)
      (d.flag.module.range_eq.le ⟨_, rfl⟩) d.flag.vector_mem earlier.baumann_alternatives)
    earlier.baumann_normalizer (by rw [c.reductions.local_centralizer]; exact inf_le_left)
    earlier.module_normalizer (source_local_action_pi d.flag.module _ hρ)
    hLC hCL hkernel g hg hgN (by simpa only [hg3] using pow_orderOf_eq_one g)
    p.cubic.field p.cubic.field_order hfield

theorem Tv_normalizes_of_earlier_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup (Gv (markedV d.flag.module)))
    (hK : IsComponent (Gv (markedV d.flag.module)) K)
    (a : ActionData d.flag.module (T : Subgroup G) K) (hlarge : LargeField K a) :
    Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (K.map (Gv (markedV d.flag.module)).subtype : Set G) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  have hn := localT_normalizes_of_largeField d V₃ earlier c hG hm K hK a hlarge
  intro t ht
  have htn := hn (show (⟨t, ht.2⟩ : Gv (markedV d.flag.module)) ∈
    localT (T : Subgroup G) (markedV d.flag.module) from ht.1)
  have hh := mem_normalizer_iff.mp htn
  apply mem_normalizer_iff.mpr
  intro k
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, (hh k).mp hk, rfl⟩
  · intro hk
    obtain ⟨j, hj, he⟩ := hk
    change (j : G) = t * k * t⁻¹ at he
    have hkG : k ∈ Gv (markedV d.flag.module) := by
      have hh := (Gv (markedV d.flag.module)).mul_mem
        ((Gv (markedV d.flag.module)).mul_mem
          ((Gv (markedV d.flag.module)).inv_mem ht.2) j.property) ht.2
      rw [he] at hh
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
    exact ⟨⟨k, hkG⟩, (hh _).mpr (by
      have he' : (⟨t, ht.2⟩ : Gv (markedV d.flag.module)) * ⟨k, hkG⟩ *
        (⟨t, ht.2⟩ : Gv (markedV d.flag.module))⁻¹ = j := Subtype.ext he.symm
      rwa [he']), rfl⟩
/-- Every original component is normalized: the proved initial sieve supplies
its larger-field model and literal central four-group internally. -/
theorem Tv_normalizes_component_of_earlier_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup (Gv (markedV d.flag.module)))
    (hK : IsComponent (Gv (markedV d.flag.module)) K) :
    Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (K.map (Gv (markedV d.flag.module)).subtype : Set G) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  obtain ⟨a, ha⟩ := (c.symmetricSixSource d V₃ earlier hG hm).largeField_knownSimple _ K hK
  exact Tv_normalizes_of_earlier_source d V₃ earlier hG hm hcounter hfusion K hK a ha
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
