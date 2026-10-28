module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Branches
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Full
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper

/-!
# Initial-adjacent displacement: support assembly

The existing central-root estimate handles its rank-one actors. The two
remaining support cases are {0,1} and {0,1,2}. For full support, the six-root
norm rules out either conjugate end-node radical inside a cubic actor.
This module combines the corresponding remaining actor estimates into the
original `InitialAdjacentDisplacement` contract, including outer actors.

The proper-support estimate uses the proved mixed-tensor comparison, while
the full-support estimate uses a regular orbit and seven generating conjugates.
Together they prove `initial_adjacent_displacement` from faithful
irreducibility, with no dimension or module-catalogue premise. This discharges
the initial-adjacent input of `multiple_support_displacement_of_root_estimates`
and the universal adjacent input of `FourDisplacement.Source`.

Source: Aschbacher–Smith K.3.2, printed pp.451,454–455; GM author manuscript
Propositions 4.7–4.8, especially step 3B.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement

open Representation Representation.BinaryOffender
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Assemble the two remaining support estimates, discharging the full-support
radical avoidance from the literal cubic action on the original module. -/
theorem initial_adjacent_displacement_of_support_estimates
    [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) Group V)
    (hproper : ProperAdjacentRemainingActors σ)
    (hfull : FullSupportRemainingActors σ) : InitialAdjacentDisplacement σ := by
  apply initial_adjacent_displacement_of_remaining_actors
  intro J v hv hJ h0 h1 A hA hc hr hremaining
  by_cases h2 : (2 : Fin 3) ∈ J
  · have hJuniv : J = Finset.univ := by
      ext i
      fin_cases i <;> simp [h0, h1, h2]
    subst J
    exact hfull v hv hJ A hA hc hr hremaining
      (full_support_radical_avoidance hJ hv A hc)
  · have hJpair : J = {0, 1} := by
      ext i
      fin_cases i <;> simp [h0, h1, h2]
    subst J
    exact hproper v hv hJ A hA hc hr hremaining

/-- Every initial-adjacent highest support, including full support, satisfies
the strict cubic displacement bound for actors in the full linear normalizer
of a faithful irreducible binary SL₄-module. -/
theorem initial_adjacent_displacement
    [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) Group V)
    (hf : Function.Injective σ) (hi : IsIrreducible σ) :
    InitialAdjacentDisplacement σ :=
  initial_adjacent_displacement_of_support_estimates σ
    (proper_adjacent_remaining_actors σ hf hi)
    (full_support_remaining_actors σ hf hi)


end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
