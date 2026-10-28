module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Preliminaries
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.OddCoreGeneration
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.QuotientGeometry
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination.Setup
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination.Terminal
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination.Globalization
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination.Transport
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination.Localization

/-!
# Odd-core elimination for hyperplanes: E.6.20

The actual quotient odd-core values and their completion from quotient
balance are in `Setup`. `Globalization` proves the maximal-prime-core
generation equality (**) from the local corank-three localization (*), and
combines it with the forbidden T-invariant obstruction in `Terminal`.

`Transport` completes the actual local odd closure from E.6.19 balance and
vanishing of the full-actor odd core. Here that extra vanishing is proved
from C_G(V) ≤ M and E.6.6(2) at V. `Localization` then proves inversion,
abelianness, the odd-prime rank bound, and (*) for that completed closure.
The maximal-core argument and E.6.13 exclude a nontrivial hyperplane core.

The final theorem retains the genuine E.6.1 and E.6.15 hypotheses, the
earlier Chapter 1 inputs in `EarlierLocalFacts`, E.6.13 nonnormality, and
exact E.6.19 balance. The section and hyperplane assembly owners discharge
those earlier inputs; no completion or localization premise remains here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.20,
printed pp.252–253 (PDF pp.263–264).
-/

public section

open Subgroup

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes

open SignalizerElimination

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V : Subgroup G}

/-- E.6.20 from the exact earlier source inputs and E.6.19 balance.
The full-actor odd core, completed local closure, local prime localization,
and global maximal-core identity are all discharged in the proof. -/
theorem lemma_E_6_20 [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V)
    (earlier : EarlierLocalFacts T)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    (hbal : HyperplaneBalance V)
    {U : Subgroup G} (hU : IsHyperplane V U) : oddCentralizer U = ⊥ := by
  let _ := h.elementary
  have h6 : ∀ A : Subgroup G, A ≠ ⊥ → A ≤ M → IsPGroup 2 A →
      HasCharacteristicTwo ↥(M ⊓ centralizer (A : Set G)) :=
    fun _ _ hAM hAp => h.localCentralizer_characteristicTwo earlier hAM hAp
  have hVzero : oddCentralizer V = ⊥ :=
    oddCentralizer_eq_bot_of_le_M h h6 h.nontrivial le_rfl h.centralizer_le
  have hcpl : CompletedLocalOddClosure V :=
    completedLocalOddClosure_of_balance_of_fullActorCore_eq_bot hbal hVzero
  apply oddCentralizer_eq_bot_of_localization h h15 h6 h13 ?_ hU
  intro _ hdim p hp hpodd
  let _ : Fact p.Prime := ⟨hp⟩
  exact localPrimeLocalization_of_completed h earlier hcpl hdim p hpodd

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes
