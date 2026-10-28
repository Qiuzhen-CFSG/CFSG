module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.Basic
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.Source
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.NoFF

/-!
# FF exclusions transported through the actual Mathieu source markings

The checked code and cocode actions admit no FF offenders. Transport along the
source's injective actor maps and whole-action equivalences gives the same
conclusion on the original module. Consequently the M22 source FF branch can
only be the genuine triple-cover action, whose calculation is independent.
Source: Aschbacher--Smith B.4.2 and K.4, printed pp.86 and 457--459.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
open Representation Representation.BinaryOffender MathieuCode MathieuCode.QuadraticActors
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Subgroup
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem not_ff_of_m23Code (h : IsM23Code ρ) : ¬ IsFFModule ρ := by
  obtain ⟨e,E,hE⟩ := h
  intro hf
  exact m23Code_not_isFFModule (hf.map_equivariant ρ m23CodeRepresentation
    e.toMonoidHom e.injective E hE)

theorem not_ff_of_m23Cocode (h : IsM23Cocode ρ) : ¬ IsFFModule ρ := by
  obtain ⟨e,E,hE⟩ := h
  intro hf
  exact m23Cocode_not_isFFModule (hf.map_equivariant ρ m23CocodeRepresentation
    e.toMonoidHom e.injective E hE)

theorem not_ff_of_m24ToddOrDual (h : MathieuSmall.IsM24ToddOrDual ρ) : ¬ IsFFModule ρ := by
  rcases h with ⟨e,hc | hd⟩
  · obtain ⟨E⟩ := hc
    intro hf
    exact cocode_not_isFFModule (hf.map_equivariant ρ cocodeRepresentation
      e.toMonoidHom e.injective E.toLinearEquiv
      (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v))
  · obtain ⟨E⟩ := hd
    intro hf
    exact code_not_isFFModule (hf.map_equivariant ρ codeRepresentation
      e.toMonoidHom e.injective E.toLinearEquiv
      (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v))

theorem not_ff_of_marked_m22Code (D : M22Source.MarkedSimpleModel ρ L m22OuterCodeRepresentation) :
    ¬ IsFFModule ρ := by
  intro hf
  exact m22OuterCode_not_isFFModule (hf.map_equivariant ρ m22OuterCodeRepresentation
    D.embedding D.injective D.equivalence.toLinearEquiv
    (fun g v => LinearMap.congr_fun (D.equivalence.isIntertwining' g) v))

theorem not_ff_of_marked_m22Cocode (D : M22Source.MarkedSimpleModel ρ L m22OuterCocodeRepresentation) :
    ¬ IsFFModule ρ := by
  intro hf
  exact m22OuterCocode_not_isFFModule (hf.map_equivariant ρ m22OuterCocodeRepresentation
    D.embedding D.injective D.equivalence.toLinearEquiv
    (fun g v => LinearMap.congr_fun (D.equivalence.isIntertwining' g) v))

variable [Finite G] [FiniteDimensional (ZMod 2) V]

theorem m22_triple_of_ff (h : RankOne.SourceHypotheses ρ L) (hf : IsFFModule ρ)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m22.Carrier)) :
    Nonempty (M22Source.MarkedTripleModel ρ L) := by
  have hs : M22Source.SourceHypotheses ρ L := {
    sqtk := h.sqtk, component := h.fitting.symm, quasisimple := h.quasisimple,
    faithful := h.faithful, irreducible := h.irreducible, cubic := h.smallCubic,
    quotient := he }
  rcases M22Source.source_markedModels ρ L hs with hc | hd | D
  · obtain ⟨D⟩ := hc
    exact (not_ff_of_marked_m22Code D hf).elim
  · obtain ⟨D⟩ := hd
    exact (not_ff_of_marked_m22Cocode D hf).elim
  · exact D
end CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
