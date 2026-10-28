module

public import Stellmacher.Recognition.Parrott.RecognitionFromLocalConfiguration
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreOmegaElementaryQuotient

/-!+# Completing a supplied Parrott configuration from the local inputs

The two-core of the actual second involution centralizer is the omega subgroup
of the second normalizer core. The local-input calculation puts every square
in the elementary subgroup F, so every fourth power is trivial. This discharges
the exponent premise in recognition for the same compatible generator pair
and second centralizer. No global N₂ hypothesis is used.

Construction of the generators and identification of the full second
centralizer remain separate obligations. These theorems do not assert that
the local inputs alone construct either witness.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
Lemma 8 and §6, printed pp.682–684.
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {d : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData d}

/-- The source-local hypotheses give exponent four in the actual second
centralizer core, retaining the supplied normalizer and fusion witnesses. -/
public theorem ParrottSecondCentralizerData.core_fourth_power_eq_one_of_local_inputs
    (c : ParrottSecondCentralizerData n)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (a : pCore 2 (centralizer ({n.v} : Set G))) : a ^ 4 = 1 := by
  have ha : ((a : centralizer ({n.v} : Set G)) : G) ∈
      (pCore 2 (centralizer ({n.v} : Set G))).map
        (centralizer ({n.v} : Set G)).subtype := mem_map_of_mem _ a.property
  rw [c.core_eq] at ha
  have ha2 := d.normalizer_omega_square_mem_elementary_of_local_inputs h hlocal
    n.sylow_lt_normalizer n.Q n.core_fixed_le_derived _ ha
  let : IsElementaryAbelian 2 d.F := d.elementary
  have ha4 := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ ha2
  apply Subtype.ext
  apply Subtype.ext
  change (((a : centralizer ({n.v} : Set G)) : G)) ^ 4 = 1
  simpa only [← pow_mul] using ha4

/-- A compatible pair and the same full second centralizer recognize the
ambient group. The local inputs discharge the core-exponent premise. -/
public theorem ParrottNormalizerGeneratorData.nonempty_equiv_tits_of_local_inputs
    {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerGeneratorData f)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (c : ParrottSecondCentralizerData n) : Nonempty (G ≃* Tits.ParrottGroup) := by
  exact k.nonempty_equiv_tits_of_second_centralizer h c
    (c.core_fourth_power_eq_one_of_local_inputs h hlocal)

end Stellmacher.Recognition
