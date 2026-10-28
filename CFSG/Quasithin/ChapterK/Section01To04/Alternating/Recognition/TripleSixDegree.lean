module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSixDegree.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSixDegree.ActorGeometry
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSixDegree.NoTwelve

/-!
# Binary degree six for the triple-A₆ cubic branch

The proved elementary-actor geometry and the ambient cubic ratio bound leave
degrees six and twelve. The concrete central coset filtration excludes degree
twelve. Pulling the original restricted action back along the actual even-cover
equivalence applies this exclusion to the source component.

`tripleSixDegree` discharges both inputs to the retained conditional assembly,
without assuming a dimension or a representation equivalence.
Source: Aschbacher–Smith K.1 and K.1.3, printed pp.452–453, using
Guralnick–Malle (2002), Theorem 6.2 and Table 6.3.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Atlas.Codes
namespace CFSG.Quasithin.ChapterK.Alternating
open TripleSixReduction
universe u v

/-- The actual TripleSixDegree contract follows from actor geometry and
exclusion of the remaining degree twelve on the concrete even cover. -/
theorem tripleSixDegree_of_geometry_and_noTwelve
    (hgeom : CubicActorGeometry.{u,v}) (h12 : NoTwelve.{v}) :
    RecognitionInputs.TripleSixDegree.{u,v} := by
  intro G V _ _ _ _ _ ρ K L h e
  rcases finrank_six_or_twelve_of_actorGeometry ρ h e (hgeom ρ K L h e) with hd | hd
  · exact hd
  · let τ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
    have hf : Function.Injective τ :=
      (h.faithful.comp L.subtype_injective).comp e.symm.injective
    have hi : IsIrreducible τ :=
      (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h.irreducible
    exact (h12 τ hf hi hd).elim

/-- Under the source cubic-ratio bound, a component isomorphic to the actual
even hexacode cover acts on a binary space of dimension six. -/
theorem tripleSixDegree : RecognitionInputs.TripleSixDegree.{u,v} :=
  tripleSixDegree_of_geometry_and_noTwelve cubicActorGeometry noTwelve

end CFSG.Quasithin.ChapterK.Alternating
