module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CountingData
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Localization
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.LocalCounts

/-!
# Bender's odd-prime centralizer argument

The structural semidirect-product theorem in (4.1), including the
exceptional order-27 exclusion, supplies the local numerical statements
in (4.2) with one common parameter. Localization then constructs all eight
fields of `BenderPrimeData`: both Sylow orders, both ambient centralizer
orders, and all three ambient involution counts. The final assembly uses
only the original local hypotheses and simplicity.

Source: H. Bender, *Finite groups with large subgroups* (1974), §4,
printed pp.225–226.
-/

namespace CFSG.Quasithin.Janko1CentralizerData

/-- Bender's odd-prime facts (4.1)–(4.2), with one common parameter and
quantifiers over all ambient prime-order elements and Sylow subgroups.
The centralizer decomposition and local counts are proved internally
from the original local hypotheses. -/
public theorem exists_benderPrimeData
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) : ∃ d : ℕ, BenderPrimeData G d := by
  obtain ⟨d, b⟩ := h.exists_localBenderPrimeData_of_structure h.oddPrimeCentralizerStructure
  exact ⟨d, h.benderPrimeData_of_local b⟩

end CFSG.Quasithin.Janko1CentralizerData
