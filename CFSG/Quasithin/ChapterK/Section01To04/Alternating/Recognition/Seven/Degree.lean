module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.SmallSpectrum
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.Fourteen
public import Theory.Representation.Quotient

/-!
# Assembly of the A₇ binary degree bound

The original source input gives degree at most eighteen. Pulling the restricted
action back through the given A₇ isomorphism supplies the faithful irreducible
representation to the small-degree spectrum. The separate cubic exclusion then
removes degree fourteen.

The independently proved spectrum and cubic exclusion discharge both premises
in `sevenDegreeBound`, giving degree four or six under the original ambient
cubic bound two. The spectrum uses irreducibility over F₂ and already excludes
degree eight; no fixed-degree module recognition or B.4.2 is required.

Source: Aschbacher–Smith, K.1.2, printed p.452 (PDF p.463), invoking
Guralnick–Malle (2002), Theorem 6.2 and Table 6.3.
-/

public section

open Representation
namespace CFSG.Quasithin.ChapterK.Alternating

universe u v

/-- Conditional numerical assembly, with the two representation obligations
explicit and the ambient degree window proved from the original hypotheses. -/
theorem sevenDegreeBound_of_smallSpectrum_and_noFourteen
    (hs : RecognitionInputs.Seven.Degree.SmallSpectrum.{v})
    (h14 : RecognitionInputs.Seven.Degree.NoFourteen.{u,v}) :
    RecognitionInputs.Seven.DegreeBound.{u,v} := by
  intro G V _ _ _ _ _ ρ K L h e
  let τ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  have hf : Function.Injective τ :=
    (h.faithful.comp L.subtype_injective).comp e.symm.injective
  have hi : IsIrreducible τ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h.irreducible
  rcases hs τ hf hi (SevenDegreeReduction.finrank_le_eighteen ρ h e) with hd | hd | hd
  · exact Or.inl hd
  · exact Or.inr hd
  · exact (h14 ρ K L h e hd).elim

/-- The K.1.2 numerical assertion: a faithful binary action with quasisimple
F*(G) isomorphic to A₇, irreducible on that component, and ambient cubic ratio
at most two has degree four or six. All spectrum and exclusion premises are
discharged. -/
theorem sevenDegreeBound : RecognitionInputs.Seven.DegreeBound.{u,v} :=
  sevenDegreeBound_of_smallSpectrum_and_noFourteen
    sevenSmallDegreeSpectrum sevenNoFourteen

end CFSG.Quasithin.ChapterK.Alternating
