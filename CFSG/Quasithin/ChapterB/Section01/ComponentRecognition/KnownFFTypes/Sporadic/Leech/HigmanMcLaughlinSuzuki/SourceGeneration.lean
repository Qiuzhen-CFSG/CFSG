module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.Source
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceGeneration.Model
public import Theory.Representation.BinaryOffender.CubicConjugateDimension.CentralCover

/-!
# Five-conjugate generation for the actual HS source actor

Five conjugates of every nonidentity involution of the original G generate
a subgroup containing F*(G). The finite witnesses come from the four actual
HS inner and outer involution classes. Their conjugators lie in the carrier
and lift to F*(G), retaining every source central cover and outer action.
The source cubic-ratio consumer consequently has degree at most fifty.

This discharges the generation input, not the subsequent degree-twenty
recognition or fixed-space estimates in the HS exclusion.

Source: Guralnick--Malle, *Classification of 2F-modules, I*, (2.5)--(2.6),
Proposition 5.1, the HS paragraph; Aschbacher--Smith K.4, printed p.457.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
open Subgroup Theory.GroupTheory Representation.BinaryOffender

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- Five conjugates in the actual ambient actor generate a subgroup
containing its quasisimple generalized Fitting subgroup. -/
theorem SourceHypotheses.five_conjugates (h : SourceHypotheses ρ) :
    InvolutionConjugateGenerationBound (generalizedFitting G) 5 := by
  let := h.quasisimple
  obtain ⟨e⟩ := h.centralQuotient
  exact involutionConjugateGenerationBound_of_centralCover ρ (generalizedFitting G)
    h.faithful h.irreducible e SourceGeneration.five_conjugates_on_automorphisms

/-- The actual source representation has degree at most fifty at cubic
ratio at most two; the generation input is fully discharged. -/
theorem SourceHypotheses.finrank_le_fifty (h : SourceHypotheses ρ)
    (hq : cubicRatio ρ ≤ 2) : Module.finrank (ZMod 2) V ≤ 50 :=
  h.finrank_le_fifty_of_five_conjugates h.five_conjugates hq

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
