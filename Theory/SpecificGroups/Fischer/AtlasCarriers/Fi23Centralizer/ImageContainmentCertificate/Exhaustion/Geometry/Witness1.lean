module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness1.Cycles0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness1.Cycles1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness1.Cycles2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness1.Cycles3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness1.Cycles4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness1.Cycles5
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Witness1.Points

/-!
# Exact commuting action of witness 1

The unchanged saved inverse cycles are compared with proposed packed actions.
Every equality and support assertion is checked by the Lean kernel.
Source: `ImageContainmentCertificate/source/centralizer-data.g`, for
GLS3 Table 5.3u. Reproduction and license are recorded in `Geometry/source/`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Geometry.Witness1
open Sporadic.Fischer.AtlasCarriers
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.SourceActionCheck
open Sporadic.Fischer.Fi23.CentralizerSection.KernelCertificate.FixedLetterCheck
open Sporadic.Fischer.Fi23.CentralizerSection.GeneratorLiftCertificate
set_option Elab.async false

theorem action_eq (x : Fin 31671) : generator1 x = action x := by
  apply witness_action_of_checks cycleBlocks1 [cycles0, cycles1, cycles2, cycles3, cycles4, cycles5, cycles6, cycles7, cycles8, cycles9, cycles10, cycles11, cycles12, cycles13, cycles14, cycles15, cycles16, cycles17, cycles18, cycles19, cycles20, cycles21, cycles22, cycles23, cycles24, cycles25, cycles26, cycles27, cycles28, cycles29, cycles30, cycles31, cycles32, cycles33, cycles34, cycles35, cycles36, cycles37, cycles38, cycles39, cycles40, cycles41, cycles42, cycles43] [mask0, mask1, mask2, mask3, mask4, mask5, mask6, mask7, mask8, mask9, mask10, mask11, mask12, mask13, mask14, mask15, mask16, mask17, mask18, mask19, mask20, mask21, mask22, mask23, mask24, mask25, mask26, mask27, mask28, mask29, mask30, mask31, mask32, mask33, mask34, mask35, mask36, mask37, mask38, mask39, mask40, mask41, mask42, mask43] action
  · exact (List.Forall₂.cons decode0 (List.Forall₂.cons decode1 (List.Forall₂.cons decode2 (List.Forall₂.cons decode3 (List.Forall₂.cons decode4 (List.Forall₂.cons decode5 (List.Forall₂.cons decode6 (List.Forall₂.cons decode7 (List.Forall₂.cons decode8 (List.Forall₂.cons decode9 (List.Forall₂.cons decode10 (List.Forall₂.cons decode11 (List.Forall₂.cons decode12 (List.Forall₂.cons decode13 (List.Forall₂.cons decode14 (List.Forall₂.cons decode15 (List.Forall₂.cons decode16 (List.Forall₂.cons decode17 (List.Forall₂.cons decode18 (List.Forall₂.cons decode19 (List.Forall₂.cons decode20 (List.Forall₂.cons decode21 (List.Forall₂.cons decode22 (List.Forall₂.cons decode23 (List.Forall₂.cons decode24 (List.Forall₂.cons decode25 (List.Forall₂.cons decode26 (List.Forall₂.cons decode27 (List.Forall₂.cons decode28 (List.Forall₂.cons decode29 (List.Forall₂.cons decode30 (List.Forall₂.cons decode31 (List.Forall₂.cons decode32 (List.Forall₂.cons decode33 (List.Forall₂.cons decode34 (List.Forall₂.cons decode35 (List.Forall₂.cons decode36 (List.Forall₂.cons decode37 (List.Forall₂.cons decode38 (List.Forall₂.cons decode39 (List.Forall₂.cons decode40 (List.Forall₂.cons decode41 (List.Forall₂.cons decode42 (List.Forall₂.cons decode43 List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))
  · exact (List.Forall₂.cons support0 (List.Forall₂.cons support1 (List.Forall₂.cons support2 (List.Forall₂.cons support3 (List.Forall₂.cons support4 (List.Forall₂.cons support5 (List.Forall₂.cons support6 (List.Forall₂.cons support7 (List.Forall₂.cons support8 (List.Forall₂.cons support9 (List.Forall₂.cons support10 (List.Forall₂.cons support11 (List.Forall₂.cons support12 (List.Forall₂.cons support13 (List.Forall₂.cons support14 (List.Forall₂.cons support15 (List.Forall₂.cons support16 (List.Forall₂.cons support17 (List.Forall₂.cons support18 (List.Forall₂.cons support19 (List.Forall₂.cons support20 (List.Forall₂.cons support21 (List.Forall₂.cons support22 (List.Forall₂.cons support23 (List.Forall₂.cons support24 (List.Forall₂.cons support25 (List.Forall₂.cons support26 (List.Forall₂.cons support27 (List.Forall₂.cons support28 (List.Forall₂.cons support29 (List.Forall₂.cons support30 (List.Forall₂.cons support31 (List.Forall₂.cons support32 (List.Forall₂.cons support33 (List.Forall₂.cons support34 (List.Forall₂.cons support35 (List.Forall₂.cons support36 (List.Forall₂.cons support37 (List.Forall₂.cons support38 (List.Forall₂.cons support39 (List.Forall₂.cons support40 (List.Forall₂.cons support41 (List.Forall₂.cons support42 (List.Forall₂.cons support43 List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, action0, action1, action2, action3, action4, action5, action6, action7, action8, action9, action10, action11, action12, action13, action14, action15, action16, action17, action18, action19, action20, action21, action22, action23, action24, action25, action26, action27, action28, action29, action30, action31, action32, action33, action34, action35, action36, action37, action38, action39, action40, action41, action42, action43, Bool.and_self]
  · have hm : unionMasks [mask0, mask1, mask2, mask3, mask4, mask5, mask6, mask7, mask8, mask9, mask10, mask11, mask12, mask13, mask14, mask15, mask16, mask17, mask18, mask19, mask20, mask21, mask22, mask23, mask24, mask25, mask26, mask27, mask28, mask29, mask30, mask31, mask32, mask33, mask34, mask35, mask36, mask37, mask38, mask39, mask40, mask41, mask42, mask43] = supportMask := by decide +kernel
    rw [hm]
    exact pointChecks

theorem commutes
    (hA : ∀ x, generatorA x = sourceA x) (hB : ∀ x, generatorB x = sourceB x) :
    generator1 * inclusion candidate = inclusion candidate * generator1 := by
  apply commute_of_actions _ _ action candidateMap action_eq
  · intro x
    exact (candidateAction_eq hA hB x).symm.trans (candidateMap_eq_action x).symm
  · exact fun x => (pointChecks x).2

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Geometry.Witness1
