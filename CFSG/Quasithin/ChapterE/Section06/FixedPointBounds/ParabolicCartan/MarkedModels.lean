module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Inputs
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Localization
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Cyclic
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Construction
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Transport

/-!
# Marked models for the Hall--Cartan branch of E.6.27

The exact E.1.13 and E.2.2 implications reduce n(X) > 1 to the three
characteristic-two alternatives. Their marked concrete Borels supply the
cyclic subgroup of order 2^n(X)-1, including unitary and derived symplectic
models and without discarding central extensions. Hall existence and
Hall--Sylow arithmetic provide containment and permutation once the
remaining model output `HallControl` is proved.

The intrinsic construction and its actual residual-parabolic application
are presently conditional on that explicitly named output. It is not part
of either earlier-source implication. The exchanged, single Bender and
diagram-active Hall calculations must discharge it before this module
establishes the full requested intrinsic theorem.

Source: Aschbacher--Smith, E.1.13, E.2.2, E.3.37, E.6.27 and 4.4.13,
printed pp.214--216, 239, 257 and 623--624 (combined manuscript, 1 March 2004).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

open Subgroup ChapterB
universe u
variable {X G : Type u} [Group X] [Finite X] [Group G] [Finite G]

/-- Source-to-construction assembly, with the remaining model output explicit.
This theorem does not claim to discharge `HallControl`. -/
theorem intrinsic_of_source_of_hallControl
    {Kc : GroupClass.{u}} (hX : IsSQTK Kc X)
    (h113 : SourceE113 X) (h22 : SourceE22 Kc X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hn : 1 < generationParameter X) (hHall : HallControl S hP) :
    Nonempty (IntrinsicHallCartanData S hP (generationParameter X)) := by
  obtain ⟨K, _, _, _, _, hc⟩ := reduced_of_source hX h113 h22 S hP hn
  exact intrinsic_of_cyclic_and_hallControl S hP (by omega) hHall hc.cyclic

/-- Application to the original E.6.27 residual parabolic. SQTK is inherited
from the actual two-local normalizer. Only the named model output and the
separately owned overlap/Sylow placements remain explicit. -/
theorem residual_hallCartan_of_source_of_hallControl
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    (S : Sylow 2 (centralizer (U : Set G)))
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (hH : IsMinimalParabolicOver (residualSylow S) H)
    (h113 : SourceE113 H) (h22 : SourceE22 Kc H)
    (hn : 1 < generationParameter H)
    (hHall : HallControl (parabolicSylow S H hH)
      (minimalParabolic_subtype (residualSylow S) H hH))
    (hM : minimalParabolicMax (parabolicSylow S H hH)
      (minimalParabolic_subtype (residualSylow S) H hH) = M.comap (residualEmbedding U H))
    (R : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (hR : (R : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
      (M ⊓ centralizer (U : Set G)).subtype =
      (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype) :
    Nonempty (HallCartanData (residualEmbedding U H) M U
      (parabolicSylow S H hH) (generationParameter H)) := by
  obtain ⟨d⟩ := intrinsic_of_source_of_hallControl (residual_sqtk h hU hUV H)
    h113 h22 (parabolicSylow S H hH)
    (minimalParabolic_subtype (residualSylow S) H hH) hn hHall
  exact ⟨transportResidual S H hH (generationParameter H) d M hM R hR⟩

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
