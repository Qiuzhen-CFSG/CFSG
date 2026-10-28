module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.ElementaryNine.Offender
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Selection

/-!
# The elementary-nine branch after local image recognition

On the literal U_H/V₁ action, an SL₂(3) conjugation image on the original
P* forces eight dimensions in its commutator support. The selected Uγ*
acts faithfully on P* by its conjugate parabolic-core placement. Uniform
character dimensions and the ternary dual-orbit estimate then make its fixed
codimension strictly larger than twice its rank, contradicting membership
in Q(H*,U_H/V₁).

This proves the action and support part of the noncontained E₉ branch by a
direct character argument, without applying D.2.17. The local recognition
premise `hSL` remains explicit: it must be derived from the standing natural
A₆ module, L₁ = sourceOne L T V₁, the noncontainment L₁* ≰ P*, and the
irreducible action in ReducedOdd. None of those data is replaced here by
an unrelated affine-group isomorphism. This module is not yet the complete
noncontained-branch exclusion from the standing hypotheses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.13, printed p.951 (PDF p.968).
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Noncontained.ElementaryNine

variable {G : Type*} [Group G] [Finite G]

/-- The lower dimension bound concerns the actual source support. Local
matrix-image recognition is the remaining input; no orbit or dimension sum
is assumed. -/
theorem source_support_bound_of_special_image
    {H L₁ T M Vα V₃ V₁ : Subgroup G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (r : ReducedOdd 3 H L₁ T M Vα)
    (coordinates : ConjugationCoordinates (Source.starImage H r.P))
    (hSL : Matrix.GeneralLinearGroup.threeSpecialLinear ≤ coordinates.action.range)
    (a : Five.StarAction H (Source.UH H V₃) V₁) (ha : Function.Injective a.action) :
    8 ≤ Module.finrank (ZMod 2) (subspaceCommutator
      (Supercritical.Offenders.linearAction a) ⊤ (Source.starImage H r.P)) :=
  support_finrank_ge_eight_of_special_image coordinates (Supercritical.Offenders.linearAction a)
    (Supercritical.Offenders.linearAction_injective a ha) hSL

/-- The actual selected actor contradicts its quadratic ratio bound once
the source conjugation image is recognized. Faithfulness on P* is derived
from the selected geometry rather than supplied as an additional premise. -/
theorem false_of_special_image
    {H L L₁ M V V₃ V₁ Vα : Subgroup G} {T : Sylow 2 G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    {c : CriticalGeometry.CriticalPair L T H V} (s : RankOne.Geometry c V₃ V₁ L₁)
    (r : ReducedOdd 3 H L₁ T M Vα)
    (coordinates : ConjugationCoordinates (Source.starImage H r.P))
    (hSL : Matrix.GeneralLinearGroup.threeSpecialLinear ≤ coordinates.action.range)
    (a : Five.StarAction H (Source.UH H V₃) V₁) (ha : Function.Injective a.action)
    (hQ : CriticalGeometry.Reorientation.QuadraticMember
      (Supercritical.Offenders.linearAction a) (Source.starImage H (c.Ugamma V₃))) : False := by
  have hstrict := strict_fixedCodim_of_special_image coordinates
    (Supercritical.Offenders.linearAction a) (Supercritical.Offenders.linearAction_injective a ha)
    hSL (Source.starImage H (c.Ugamma V₃)) hQ.1 (source_actor_centralizer s r)
  exact (Nat.not_le_of_lt hstrict) hQ.2.2

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Noncontained.ElementaryNine

end
