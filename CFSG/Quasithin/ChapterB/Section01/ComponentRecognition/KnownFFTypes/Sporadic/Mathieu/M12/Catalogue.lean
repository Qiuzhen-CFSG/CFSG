module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M12.SourceCompletion
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.Source

/-!
# The M₁₂ recognition input to the source sporadic catalogue

Apply the completed recognition theorem to the catalogue's literal Chapter K
hypotheses and its actual known-simple carrier. This discharges the M₁₂
recognition input: degree reduction, covers, the marked heart equivalence,
and the faithful compatible ambient extension all come from proved theorems.
The output's `moduleInput` and `ambient` fields are the inputs to the independent
H.11 and K.4 calculations on the same representation.

Source: Aschbacher--Smith, Chapter K introduction, printed p.451, and K.4,
printed pp.457--460 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Subgroup Theory.GroupTheory
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)
  (e : (generalizedFitting G ⧸ center (generalizedFitting G)) ≃*
    KnownSimple.SporadicName.m12.Carrier)

include h in
/-- The complete M₁₂ module and ambient-extension recognition from the
catalogue's full source hypotheses, retaining the exact quotient equivalence. -/
theorem m12_recognition : Nonempty (M12Source.Recognition ρ e) :=
  M12Source.source_recognition ρ
    ⟨h.sqtk, h.quasisimple, h.faithful, h.irreducible, h.cubic_le_two⟩ e

end CFSG.Quasithin.ChapterK.SporadicCatalogue
