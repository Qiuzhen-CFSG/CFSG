module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M12.SourceDegree.Reduction
public import Theory.Mathieu.M12.Properties.ThreeConjugates
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap

/-!
# The degree bound for the source M₁₂ branch

The reduction proves an ambient two-rank bound and a cubic actor of fixed
codimension at most eight. Three-conjugate generation gives degree at most
24; an ordinary binary M₁₂ degree-gap result then supplies degree at most
ten and the existing marked recognition output.

Both model calculations are proved on the concrete M₁₂. Applying them to
the literal component restriction discharges the degree premise of the
marked recognition theorem. The only inputs are the Chapter K hypotheses
on the actual actor G and the specified central-quotient equivalence;
no SQTK property of the full linear normalizer is assumed.

Source: Aschbacher--Smith, Chapter K introduction and K.4, printed pp.451
and 457 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M12Source
open Subgroup Theory.GroupTheory
open _root_.Sporadic.Mathieu

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : Hypotheses ρ)
  (e : (generalizedFitting G ⧸ center (generalizedFitting G)) ≃* M12)

include h e in
/-- The Chapter K M₁₂ degree bound under cubic ratio at most two for the
actual source actor. The generation and binary degree-gap inputs are discharged. -/
theorem source_degree_le_ten : Module.finrank (ZMod 2) V ≤ 10 := by
  apply source_degree_le_ten_of_threeConjugates_of_gap ρ h e
    m12_threeConjugateAutomorphisms
  intro σ hf hi hd
  let : σ.IsIrreducible := hi
  exact Representation.MathieuSmall.M12DegreeGap.finrank_le_ten σ hf hd

include h in
/-- The source hypotheses give the marked permutation heart and its faithful
ambient extension, retaining the original central-quotient marking. -/
theorem source_recognition : Nonempty (Recognition ρ e) :=
  source_recognition_of_finrank_le_ten ρ h e (source_degree_le_ten ρ h e)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M12Source
