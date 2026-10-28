module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.WordSetup
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordEvaluation
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison

/-!+# Certifying the ambient words on the Fi₂₃ labels

The word evaluator preserves the exact carrier words, inverses, multiplication
order, and powers. This module applies its correctness theorems to the shared
label map, and then to the actual lifted subgroup orbit.

Two independent certificate obligations remain explicit: identifying the packed
signed generators with the original cycle-decoded permutations, and checking the
two packed candidate actions on every label. Neither obligation follows from the
definitions of the carrier or the evaluator. The unconditional ambient-action
theorems require both certificates; the full comparison additionally requires
identification of the source maps with the Fi₂₃ generators.

Source: GLS3 Table 5.3v and `Chapter5(sec3-).tex` around line 1053; retained
ATLAS F24G1-p306936B0.g1/.g2 tables and the exact `WordSetup` words.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

/-- Transfer the first numerical certificate to the literal ambient word. -/
theorem candidateA_apply_labelMap_of_certificates
    (hgen : ∀ c x, Ambient.letterMap c x = (Ambient.letterValue c).val x)
    (hcheck : ∀ i, Ambient.candidateAMap (labelMap i) = labelMap (sourceA i)) :
    ∀ i, candidateA.val (labelMap i) = labelMap (sourceA i) := by
  intro i
  exact (Ambient.candidateAMap_correct hgen (labelMap i)).symm.trans (hcheck i)

/-- Transfer the second numerical certificate, with its exact conjugation. -/
theorem candidateB_apply_labelMap_of_certificates
    (hgen : ∀ c x, Ambient.letterMap c x = (Ambient.letterValue c).val x)
    (hcheck : ∀ i, Ambient.candidateBMap (labelMap i) = labelMap (sourceB i)) :
    ∀ i, candidateB.val (labelMap i) = labelMap (sourceB i) := by
  intro i
  exact (Ambient.candidateBMap_correct hgen (labelMap i)).symm.trans (hcheck i)

/-- The certificate contracts discharge the ambient-action premises of the
existing orbit-membership theorem, using the literal label map and lifted group. -/
theorem labelMap_mem_suborbit_of_ambient_certificates
    (hgen : ∀ c x, Ambient.letterMap c x = (Ambient.letterValue c).val x)
    (ha : ∀ i, Ambient.candidateAMap (labelMap i) = labelMap (sourceA i))
    (hb : ∀ i, Ambient.candidateBMap (labelMap i) = labelMap (sourceB i)) :
    ∀ i, labelMap i ∈ suborbit :=
  labelMap_mem_suborbit_of_intertwinings
    (candidateA_apply_labelMap_of_certificates hgen ha)
    (candidateB_apply_labelMap_of_certificates hgen hb)

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate
