module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Branches
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.InnerEstimate
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.Normalizer
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.Pullback
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation

/-!
# Proper adjacent support: full-normalizer displacement

An outer normalizer operator exchanges the two proper adjacent highest-vector
supports. Once these supports are separated, binary Schur's lemma places every
elementary actor in the literal component image. Pulling back that actor
preserves cubicity, rank, common fixed codimension, and the central-root
avoidance condition. The inner estimate therefore applies to the original
normalizer action.

The proved mixed-tensor comparison supplies support separation and the
inner involution bounds. Thus `proper_adjacent_remaining_actors` discharges
both representation-theoretic premises from faithful irreducibility alone.
Its consumer is `Adjacent.initial_adjacent_displacement_of_support_estimates`.

Source: Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Propositions 4.7 and 4.8(3), pp.25–28; Aschbacher–Smith K.3.2, pp.454–455.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement

open Representation Representation.BinaryOffender
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Assemble the proper adjacent branch from the two independent facts,
retaining the literal full-normalizer actors in the conclusion. -/
theorem proper_adjacent_remaining_actors_of_separation_and_inner_estimate
    (σ : Representation (ZMod 2) Group V) (hf : Function.Injective σ)
    (hi : IsIrreducible σ) (hsep : ProperSupportSeparation σ)
    (hinner : ProperInnerEstimate σ) : ProperAdjacentRemainingActors σ := by
  intro v hv h A hA hc hr hremaining
  have hin := Proper.elementary_le_image_of_support_separation σ hf hi hsep hv h A hA
  obtain ⟨B, hB, hBc, hBr, hBcodim, hBremaining, _⟩ :=
    Proper.inner_actor_pullback σ hf A hA hin hc hremaining
  have hgap := hinner v hv h B hB hBc (by simpa only [hBr] using hr) hBremaining
  rwa [hBr, hBcodim] at hgap

/-- Faithful irreducible binary SL₄ modules with proper adjacent highest
support satisfy the strict common-fixed-space bound for every remaining
elementary cubic actor in the full linear normalizer. -/
theorem proper_adjacent_remaining_actors [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Group V) (hf : Function.Injective σ)
    (hi : IsIrreducible σ) : ProperAdjacentRemainingActors σ :=
  proper_adjacent_remaining_actors_of_separation_and_inner_estimate σ hf hi
    (proper_support_separation σ hi) (proper_inner_estimate σ hf hi)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
