module

public import Stellmacher.Recognition.Parrott.LocalGenerators
public import Stellmacher.Recognition.Parrott.SecondCentralizer
public import Theory.GroupTheory.TwoInvolutionClassGeneration

/-!
# Ambient generation in Parrott's configuration

The original involution centralizer and the normalizer of the supplied second
elementary subgroup generate the ambient group. Their join contains the supplied
Sylow two-subgroup and both full involution centralizers. The retained conjugators
in the Sylow fusion theorem therefore allow the two-centralizer generation
theorem to apply. The presentation words of the same supplied local generator
pair consequently generate the ambient group, independently of the braid relation.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§6, p.684, generation and the Thompson order comparison.
-/

open Subgroup

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The actual centralizer and second elementary normalizer generate `G`,
with the supplied configuration unchanged. -/
public theorem ParrottNormalizerFusionData.centralizer_sup_normalizer_eq_top
    (n : ParrottNormalizerFusionData e)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G) :
    centralizer ({z} : Set G) ⊔ normalizer (e.F : Set G) = ⊤ := by
  apply Theory.GroupTheory.TwoInvolutionClassGeneration.eq_top_of_centralizers_le
    e.sylow _ (e.sylow_le_normalizer.trans le_sup_right) z n.v
    h.involution n.v_order n.not_isConj
    (e.le_sylow e.z_mem_inf.2) (e.le_sylow n.v_mem_inf.2) le_sup_left
    ((n.second_centralizer_data h hN).le_normalizer.trans le_sup_right)
  exact n.sylow_fusion

/-- The words attached to this exact compatible generator pair generate `G`.
No braid relation or ambient order assumption is needed. -/
public theorem ParrottNormalizerGeneratorData.closure_words_eq_top
    {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerGeneratorData f)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G) :
    closure (Set.range k.words) = ⊤ := by
  rw [k.closure_words, n.centralizer_sup_normalizer_eq_top h hN]

end Stellmacher.Recognition
