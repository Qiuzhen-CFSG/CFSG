module
public import CFSG.Quasithin.ChapterF.Section09.ConjugatePair.Recognition
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.Pairs

/-!
# The genuine F.9.5(6) input to the Chapter13 component action

The universally quantified source interface is now instantiated by the proved
original conjugate-pair theorem, retaining the source's right conjugation and
literal starred quotient. No pair-recognition premise remains.
Source: Aschbacher–Smith F.9.5(6.i) and13.5.20, printed pp.319,923.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction
variable {G : Type*} [Group G] [Finite G]

/-- The full original F.9.5(6.i) specialization, with every source premise retained. -/
theorem source_F95Six : F95Six (G := G) := by
  intro D h hi _ hp hc hcard g hg hn
  exact h.pair_star_symmetricThree_right hi hcard hp hc g hg hn
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction
