module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.ConjugateGeneration
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.SourceReduction

/-!+# Discharging the conjugate-generation input to the PSU₃ parameter reduction

The proved source conjugate bound supplies the literal ambient tuples used
by the binary cubic-ratio argument in `SourceReduction`. The independent
degree minimum and PSU₃(5) outer-displacement estimate remain explicit;
their discharge belongs to the final parameter assembly.

Source: Aschbacher–Smith K.2, printed p.453; Guralnick–Malle,
*Classification of 2F-modules I*, Proposition 4.3, manuscript pp.10–11.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped ENNReal

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion

universe u v

/-- The K.2 parameter reduction with its conjugate-generation premise discharged.
Only the independent representation estimates remain for final assembly. -/
theorem source_parameter_eq_three_of_degree_and_outer
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L]
    (hdegree : PrimeDegreeBound.{u, v})
    (houter : SourceFiveOuterDisplacement.{u, v})
    {p : ℕ} (h : SourceHypotheses ρ L p) (hq : cubicRatio ρ ≤ 2) : p = 3 :=
  source_parameter_eq_three_of_inputs ρ L hdegree sourceConjugateBounds houter h hq

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
