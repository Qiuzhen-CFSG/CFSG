module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Centralizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Component
public import CFSG.Quasithin.Chapter10.SourceNormalizationAssembly

/-!
# Conditional construction of the actual A₅ replacement

From the original centralizer geometry, the literal wreath recognition and
the overgroup span identity, choose an actual C-component of K_zT. Its
quotient is A₅ and T moves it. Its orbit is K_z, so it escapes M and moves
the reduced module V_z. This proves faithfulness. The equality J_z=K_z
makes its orbit normal in every maximal two-local overgroup, proving
maximality in L(G,T). The original normalization assembly then consumes
this replacement without changing the ambient group or Sylow subgroup.

The three earlier-source inputs are explicit and remain to be proved.
Source: Aschbacher--Smith §10.3, final paragraph, printed pp.756--757.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

/-- All source inputs are applied to the same survivor and central involution.
The resulting R is constructed, with faithfulness and maximality proved. -/
theorem replacement_of_source_inputs
    (hgeometry : CentralizerGeometryAt T)
    (hwreath : WreathRecognitionAt T)
    (hovergroups : OvergroupSpanAt T) : SourceLinearThreeReplacementAt T := by
  intro hmany L D s
  obtain ⟨d⟩ := hgeometry hmany L D s
  obtain ⟨⟨e⟩, hstrict, hout, horbit⟩ := hwreath hmany L D s d
  let z := d.first * d.second
  let B := componentSpan T L z
  let J := componentJoin T L z
  let C := centralizer ({z} : Set G)
  obtain ⟨K,hK⟩ := exists_component_of_wreath e
  have hgen := horbit K hK
  have hKB : K ≤ B := (le_componentOrbit K T).trans_eq hgen
  obtain ⟨hlocal,hq,he,hn⟩ := component_of_wreath
    (T := T) (show (T : Subgroup G) ≤ J from le_sup_right) d.join_core_ne_bot e hK
  have hKC : K ∈ Chapter1.cComponentsIn C :=
    ⟨hKB.trans (componentSpan_le_centralizer z),
      component_in_overgroup hK.2 hKB le_sup_left (componentSpan_le_centralizer z)
        (le_normalizer_conjugateSpanBy _ _)⟩
  have hKM : ¬ K ≤ D.maximalLocal := by
    intro hle
    apply hout
    rw [←hgen]
    exact iSup_conjugates_le_of_le_normalizer K T D.maximalLocal hle
      ((le_normalizer_componentOrbit L T).trans D.maximalLocal.le_normalizer)
  have hf := faithful_of_reduced_movement (T := T) (D.simpleQTKE.evenCharacteristic T)
    hlocal hKC d.module_le_centralizer (d.reduced hstrict) (by
      intro hc
      exact hKM ((le_inf hKC.1 hc).trans d.module_centralizer))
  have hmax := maximal_of_orbit_normalizers hlocal hK
    (show J = componentOrbit K (T : Subgroup G) ⊔ (T : Subgroup G) by
      rw [hgen]; rfl) (by
        intro M hM hJM
        rw [hgen, ← hovergroups hmany L D s d ⟨e⟩ hstrict hout horbit M hM hJM]
        exact le_normalizer_conjugateSpanBy _ _)
  exact ⟨K,hmax,hf,hq,hn,he⟩

/-- Actual normalization consumer of the constructed replacement. The
earlier reduction, tensor exclusion and three §10.3 inputs remain explicit. -/
theorem normalizes_of_source_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : SourceA5TensorExclusionAt T)
    (hreduction : SourceNonnormalReductionAt T)
    (hgeometry : CentralizerGeometryAt T)
    (hwreath : WreathRecognitionAt T)
    (hovergroups : OvergroupSpanAt T)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) :=
  source_normalizes_of_source_branches_of_many hG hmany htensor hreduction
    (replacement_of_source_inputs hgeometry hwreath hovergroups) hL hf hq

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
