module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs.Geometry
public import Theory.Representation.BinaryOffender.ThreeConjugateNormalizer.CentralCover

/-!
# Transfer of pariah geometry to arbitrary central covers

The actual isomorphism from the central quotient supplies finiteness,
simplicity and perfectness of the specified sporadic carrier. Its model
geometry then gives the automorphism rank bound and three-conjugate generation;
the latter lifts to the literal full linear normalizer on the same space.

This supplies `Geometry` from `SimpleGeometry` for the degree contradiction
in Aschbacher–Smith B.1.13, printed pp.73–74. The individual simple-model facts
are still supplied by their producers, and the six unconditional exclusions
remain the responsibility of the pariah assembly.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
open Subgroup Theory.GroupTheory Representation.BinaryOffender
universe u v

/-- Simple-model geometry supplies normalizer geometry for every faithful
irreducible central cover, with carrier hypotheses inherited from that cover. -/
theorem geometry_of_simpleGeometry (name : KnownSimple.SporadicName) (r : ℕ)
    (h : SimpleGeometry name r) : Geometry.{u,v} name r := by
  intro L W _ _ _ _ _ _ σ hf hi he
  obtain ⟨e⟩ := he
  let : Finite name.Carrier := Finite.of_surjective e e.surjective
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup name.Carrier := e.symm.isSimpleGroup
  let : Group.IsPerfect name.Carrier :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨hgen, hrank⟩ := h
  exact ⟨normalizerThreeConjugates_of_centralCover σ hf hi e hgen, hrank⟩

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
