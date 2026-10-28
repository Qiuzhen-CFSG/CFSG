module
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.CoreRepresentatives
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions.Coordinates

/-!
# A pair vector moved by the sextet core

An eight-fixed-point involution moves the pair {0,6} by the pair {6,7}.
Transport along the actual native conjugator gives a pair displacement for
every sextet core. The original Todd embedding puts this pair vector in
E intersect Q, connecting its second orbit to the plane-core fusion.
The representative coordinate check, including import preparation, used
29.07 seconds and 1,984,364 KiB peak RSS.

Source: Aschbacher–Segev (1991), (6.4), printed p.602.
-/

public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open M24InvolutionCentralizers
namespace MathieuCode.J4Fusion

private lemma pair_displacement :
    cocodeRepresentation involution2A (pairVector ⟨{0,6},by decide⟩) -
      pairVector ⟨{0,6},by decide⟩ = pairVector ⟨{6,7},by decide⟩ := by
  apply CocodeOctad.Involutions.coordinateEquiv.injective
  change CocodeOctad.Involutions.coordinates _ = CocodeOctad.Involutions.coordinates _
  decide +kernel

/-- The same sextet core has a displacement which is an actual pair vector. -/
lemma sextet_core_pair_displacement (S : Sextet) :
    ∃ s ∈ (sextetStabilizer S).pCoreIn 2, ∃ v : Cocode, ∃ B : PointPair,
      cocodeRepresentation s v - v = pairVector B := by
  obtain ⟨s,hs,hc⟩ := sextet_core_class S true
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  refine ⟨s,hs,cocodeRepresentation g (pairVector ⟨{0,6},by decide⟩),
    mapPair g (⟨{6,7},by decide⟩ : PointPair),?_⟩
  have he (w : Cocode) : cocodeRepresentation s (cocodeRepresentation g w) =
      cocodeRepresentation g (cocodeRepresentation involution2A w) := by
    rw [←hg]
    simp only [↓reduceIte,map_mul,Module.End.mul_apply,cocodeRepresentation.inv_self_apply]
  rw [he,←map_sub,pair_displacement,pairVector_equivariant]

end MathieuCode.J4Fusion
