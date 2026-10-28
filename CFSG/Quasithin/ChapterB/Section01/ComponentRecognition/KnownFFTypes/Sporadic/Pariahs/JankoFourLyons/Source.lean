module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs.JankoFourLyons
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.DegreeWindows
public import Theory.Representation.CharacteristicTwoIrreducibleRank

/-!
# J₄ geometry and the Chapter K degree window

The actual ambient group acts by conjugation on its irreducible component
F*(G). The J₄ central quotient bounds the component's automorphism two-rank
by eleven and gives three-conjugate generation on the original vector space.
Consequently the ambient two-rank is at most eleven and cubic ratio at most
two forces binary degree at most sixty-six.

The applications use `SporadicCatalogue.SourceHypotheses`, which retains the
full known-simple SQTK hypothesis, faithfulness, the literal F*(G), its
irreducibility and the ambient cubic ratio. The central quotient equivalence
remains explicit. No restriction is imposed on the full linear normalizer.
The final application discharges exactly the geometry premise of the
catalogue's bounded-exclusion reduction; its representation exclusion stays
with the catalogue owner.

Source: Aschbacher–Smith, K.1–K.4, printed pp.451–460, especially K.4 on
p.457 citing Guralnick–Malle, Classification of 2F-modules I, Theorem 6.6
and Table 6.7. The model generation input is Revin–Zavarnitsine,
https://arxiv.org/abs/2505.05173v2, Theorem 1.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
universe u v

variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)

include ρ h

/-- The actual Chapter K actor has two-rank at most eleven in the J₄ case;
its component has three-conjugate geometry on the literal binary module. -/
theorem j4_source_geometry
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Janko4.Model) :
    primeRank 2 G ≤ 11 ∧
      NormalizerThreeConjugates (ρ.comp (generalizedFitting G).subtype) := by
  let := h.quasisimple
  let := h.irreducible
  obtain ⟨hgen, hrank⟩ := j4_centralCover_geometry
    (ρ.comp (generalizedFitting G).subtype)
    (h.faithful.comp (generalizedFitting G).subtype_injective) h.irreducible e
  exact ⟨(Representation.CharacteristicTwoIrreducible.primeRank_le_automorphisms
    ρ (generalizedFitting G) h.faithful).trans hrank, hgen⟩

/-- The cubic degree window for every J₄ source central cover and ambient action. -/
theorem j4_degree_le_sixtySix
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Janko4.Model) :
    Module.finrank (ZMod 2) V ≤ 66 :=
  degree_le_of_simpleGeometry ρ h .j4 11 simpleGeometry_j4 e

omit ρ h in
/-- Only the independent representation exclusion within degree sixty-six
remains; the source geometry premise is fully discharged. -/
theorem sourceExclusion_j4_of_bounded_geometry
    (hb : BoundedSourceExclusion.{u,v} .j4 66) : SourceExclusion.{u,v} .j4 :=
  sourceExclusion_j4_of_bounded simpleGeometry_j4 hb

end CFSG.Quasithin.ChapterK.SporadicCatalogue
