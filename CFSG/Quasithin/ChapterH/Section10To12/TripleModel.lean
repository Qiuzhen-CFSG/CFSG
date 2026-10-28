module

public import CFSG.Quasithin.ChapterH.Section10To12.Defs
public import Theory.Representation.Mathieu.M22James

/-!
# A concrete inhabitant of the source triple-cover condition

The perfect binary matrix group constructed in `Theory.Mathieu.M22.TripleCover`
satisfies the exact `IsTripleM22` condition: its center has order three and
its actual central quotient is the native M₂₂. Its twelve-dimensional action
is faithful and irreducible. This supplies the concrete model for H.12.1;
the classification for every group satisfying the source condition still
requires triple-cover recognition and James's degree and uniqueness results.

Source: Aschbacher–Smith, H.12.1(1), printed pp.393–394.
-/

public section

namespace CFSG.Quasithin.ChapterH.Section10To12

open Sporadic.Mathieu

/-- The constructed nonsplit matrix cover satisfies the source hypotheses. -/
theorem isTripleM22_concrete : IsTripleM22 M22TripleCover where
  quasisimple := inferInstance
  center_card := M22TripleCover.center_card
  centralQuotient := ⟨M22TripleCover.centralQuotientEquiv⟩

end CFSG.Quasithin.ChapterH.Section10To12
