module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.Source
public import Theory.SpecificGroups.Held.BinaryDegree
public import Theory.Representation.BinaryOffender.CubicNormalizerDegree

/-!
# The Held degree gap at cubic ratio two

The source action has degree at most 36 from three-conjugate generation and
an automorphism two-rank bound of six. The actual Held carrier has faithful
binary degree at least 42, by the inverted center of its extraspecial seven
subgroup. The two bounds therefore exclude Held once the source cover has
trivial center.

The three model inputs in the final theorem remain explicit obligations:
trivial center for each quasisimple cover, three-conjugate generation for all
involutory automorphisms, and the full automorphism two-rank bound. This is
not yet an unconditional proof of `sourceExclusion_he`. It retains the actual
ambient cubic action and the literal central quotient; no property of the
full linear normalizer is presumed.

Source: Aschbacher–Smith, Chapter K introduction and K.4, printed pp.451 and
457 (PDF pp.462 and 468), citing GM02 Theorem 6.6 and Table 6.7. The local
representation argument reconstructs a sufficient bound for the Held case.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Theory.GroupTheory Subgroup Representation.BinaryOffender
universe u v

/-- Three-conjugate geometry and rank six give the source degree window,
including every central cover and ambient outer action. -/
theorem held_degree_le_thirtySix
    (hgen : ThreeConjugateAutomorphisms Held.He)
    (hrank : primeRank 2 (MulAut Held.He) ≤ 6)
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Held.He) :
    Module.finrank (ZMod 2) V ≤ 36 := by
  let := h.quasisimple
  exact finrank_le_six_mul_of_cubic_central_quotient ρ (generalizedFitting G)
    h.faithful h.irreducible e hgen hrank h.cubic_le_two

/-- Application of the proved Held degree bound to the exact K.4 exclusion
contract. The existing multiplier and automorphism producers must discharge
all three premises before the unconditional source exclusion is complete. -/
theorem sourceExclusion_he_of_model_inputs
    (hcenter : ∀ {L : Type u} [Group L] [Finite L] [IsQuasisimple L],
      (L ⧸ center L ≃* Held.He) → center L = ⊥)
    (hgen : ThreeConjugateAutomorphisms Held.He)
    (hrank : primeRank 2 (MulAut Held.He) ≤ 6) : SourceExclusion.{u,v} .he := by
  intro G V _ _ _ _ _ ρ h he
  obtain ⟨e⟩ := he
  let := h.quasisimple
  have hc := hcenter e
  let eL : generalizedFitting G ≃* Held.He :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans e
  have hlower := Held.BinaryDegree.finrank_ge_fortyTwo
    ((ρ.comp (generalizedFitting G).subtype).comp eL.symm.toMonoidHom)
    (h.faithful.comp ((generalizedFitting G).subtype_injective.comp eL.symm.injective))
  have hupper := held_degree_le_thirtySix hgen hrank ρ h e
  omega

end CFSG.Quasithin.ChapterK.SporadicCatalogue
