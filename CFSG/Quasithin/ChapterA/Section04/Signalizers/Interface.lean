module

public import CFSG.Quasithin.ChapterA.Section04.Defs
import all CFSG.Quasithin.ChapterA.Section04.Basic

/-!
# Elimination rules for the signalizer predicates

This is an intentional definition/proof split with `Section04.Basic`.
Its private definition bodies are imported only to prove public specification
lemmas. Clients can use these lemmas without unfolding the predicates or
changing the existing Basic module's public boundary.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section04
variable {G : Type*} [Group G] {X M R : Subgroup G}

/-- A signalizer lies in its specified ambient subgroup. -/
theorem IsTwoSignalizer.le (h : IsTwoSignalizer X M R) : R ≤ M := h.1

/-- A signalizer is a two-group. -/
theorem IsTwoSignalizer.isPGroup (h : IsTwoSignalizer X M R) : IsPGroup 2 R := h.2.1

/-- The actor normalizes a signalizer. -/
theorem IsTwoSignalizer.normalizes (h : IsTwoSignalizer X M R) :
    X ≤ Subgroup.normalizer (R : Set G) := h.2.2

/-- Public construction and elimination rule for signalizers. -/
theorem isTwoSignalizer_iff (X M R : Subgroup G) :
    IsTwoSignalizer X M R ↔
      R ≤ M ∧ IsPGroup 2 R ∧ X ≤ Subgroup.normalizer (R : Set G) := Iff.rfl

/-- Maximality is with respect to inclusion among signalizers. -/
theorem isMaximalTwoSignalizer_iff (X M R : Subgroup G) :
    IsMaximalTwoSignalizer X M R ↔
      IsTwoSignalizer X M R ∧
        ∀ S : Subgroup G, IsTwoSignalizer X M S → R ≤ S → S ≤ R := Iff.rfl

end CFSG.Quasithin.ChapterA.Section04
end
