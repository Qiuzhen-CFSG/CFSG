module

public import Stellmacher.Recognition.Parrott.BraidFromCentralizerExponent
public import Theory.GroupTheory.TwoInvolutionClassGeneration
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.SpecificGroups.Tits.GeneratedImage

/-!
# Tits recognition from one actual Parrott configuration

The supplied centralizer and normalizer generate the ambient group, because
it has the two involution classes retained by their fusion data and contains
both full involution centralizers. Their compatible local words satisfy all
37 relators once the actual second-centralizer core has exponent four.

The resulting presentation map is surjective. Simplicity of the certified
Tits model and the nontrivial distinguished involution word make it injective.
This provides the final consumer for the local construction without imposing
a global N₂ condition. Construction of the same local witnesses and the core
exponent belongs to the original-source assembly.

Source: Parrott (1972), §§5–6, printed pp.683–684.
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Both full involution centralizers, with the supplied Sylow fusion, force
ambient generation by the first centralizer and second elementary normalizer. -/
public theorem ParrottNormalizerFusionData.centralizer_sup_normalizer_eq_top_of_containment
    (n : ParrottNormalizerFusionData e) (h : ParrottCentralizerHypotheses z)
    (hc : centralizer ({n.v} : Set G) ≤ normalizer (e.F : Set G)) :
    centralizer ({z} : Set G) ⊔ normalizer (e.F : Set G) = ⊤ := by
  apply Theory.GroupTheory.TwoInvolutionClassGeneration.eq_top_of_centralizers_le
    e.sylow _ (e.sylow_le_normalizer.trans le_sup_right) z n.v
    h.involution n.v_order n.not_isConj
    (e.le_sylow e.z_mem_inf.2) (e.le_sylow n.v_mem_inf.2) le_sup_left
    (hc.trans le_sup_right)
  exact n.sylow_fusion

/-- The actual compatible generator words generate the ambient group. -/
public theorem ParrottNormalizerGeneratorData.closure_words_eq_top_of_second_centralizer
    {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerGeneratorData f)
    (h : ParrottCentralizerHypotheses z) (c : ParrottSecondCentralizerData n) :
    closure (Set.range k.words) = ⊤ := by
  rw [k.closure_words,
    n.centralizer_sup_normalizer_eq_top_of_containment h c.le_normalizer]

/-- The exact compatible pair realizes the complete presentation and retains
both its prescribed involution and ambient generation. -/
public theorem ParrottNormalizerGeneratorData.generating_presentation_of_second_centralizer
    {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerGeneratorData f)
    (h : ParrottCentralizerHypotheses z) (c : ParrottSecondCentralizerData n)
    (hfour : ∀ a : pCore 2 (centralizer ({n.v} : Set G)), a ^ 4 = 1) :
    Tits.SatisfiesParrottRelations k.words ∧
      k.words .s1 * (k.words .s5) ^ 2 = z ∧ closure (Set.range k.words) = ⊤ := by
  exact ⟨k.satisfiesParrottRelations_of_second_centralizer_exponent h c hfour,
    k.anchor, k.closure_words_eq_top_of_second_centralizer h c⟩

/-- The full local configuration recognizes the actual presented Tits group.
No ambient simplicity or global N₂ premise is needed after construction of
these witnesses. -/
public theorem ParrottNormalizerGeneratorData.nonempty_equiv_tits_of_second_centralizer
    {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerGeneratorData f)
    (h : ParrottCentralizerHypotheses z) (c : ParrottSecondCentralizerData n)
    (hfour : ∀ a : pCore 2 (centralizer ({n.v} : Set G)), a ^ 4 = 1) :
    Nonempty (G ≃* Tits.ParrottGroup) := by
  obtain ⟨hrels, hanchor, hgen⟩ := k.generating_presentation_of_second_centralizer h c hfour
  let φ := Tits.parrottLift k.words hrels
  have hsurj : Function.Surjective φ := (Tits.parrottLift_surjective_iff _ _).mpr hgen
  have hinj : Function.Injective φ := by
    apply φ.ker_eq_bot_iff.mp
    rcases φ.normal_ker.eq_bot_or_eq_top with hker | hker
    · exact hker
    · have htrivial : φ = 1 := MonoidHom.ker_eq_top_iff.mp hker
      have hword : φ (Tits.parrottGenerator .s1 * Tits.parrottGenerator .s5 ^ 2) = z := by
        simpa only [φ, map_mul, map_pow, Tits.parrottLift_generator] using hanchor
      have hz : z = 1 := by simpa only [htrivial, MonoidHom.one_apply] using hword.symm
      have ho := h.involution
      rw [hz, orderOf_one] at ho
      norm_num at ho
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

end Stellmacher.Recognition
