module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.LocalData
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.AlternativesData
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.FourCentralizers
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion

/-!
# Assembly of Bender's odd-prime centralizer structure

Burnside transfer unconditionally supplies an actual normal odd
complement to `⟨z⟩` in `C_G(x)`. Its intersection with `C_G(z)` is exactly
`⟨x⟩`. The four-group centralizers used in the exceptional-case argument
are also established from the source hypotheses.

The structural alternatives make this complement cyclic of order `p` or
15, or produce the exceptional elementary abelian order-27 normalizer.
Bender's exceptional-normalizer contradiction rules out the latter case.
The final theorem `oddPrimeCentralizerStructure` discharges both premises
of the conditional assembly from the original local data and simplicity.
Thus the full ambient centralizer is the internal semidirect product of
the actual cyclic odd complement with `⟨z⟩`.

Source: Bender, *Finite groups with large subgroups* (1974), §4, (4.1),
printed p.225; Janko, J. Algebra 3 (1966), proof of Lemma 3.1.
-/

namespace CFSG.Quasithin.Janko1CentralizerData

variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

/-- The exact source assembly, with both remaining source branches explicit.
The odd complement itself is constructed by the proved transfer theorem. -/
public theorem oddPrimeCentralizerStructure_of_alternatives
    (alternatives : ∀ (p : ℕ), p = 3 ∨ p = 5 → ∀ x : G,
      x ∈ Subgroup.centralizer ({h.z} : Set G) → orderOf x = p →
      ∀ A : Subgroup G, OddCentralizerComplement h x A →
        (IsCyclic A ∧ (Nat.card A = p ∨ Nat.card A = 15)) ∨
          ExceptionalOddNormalizer A)
    (exclude : ∀ x : G, x ∈ Subgroup.centralizer ({h.z} : Set G) →
      orderOf x = 3 → ∀ A : Subgroup G, OddCentralizerComplement h x A →
        ExceptionalOddNormalizer A → False) :
    OddPrimeCentralizerStructure h := by
  refine ⟨?_⟩
  intro p hp x hxC hx
  obtain ⟨A, a⟩ := h.exists_oddCentralizerComplement p hp x hxC hx
  rcases alternatives p hp x hxC hx A a with ⟨hcyc, hcard⟩ | e
  · have hzC : Subgroup.zpowers h.z ≤ Subgroup.centralizer ({x} : Set G) :=
      a.sup_eq ▸ le_sup_right
    exact ⟨A, hcyc, hcard, hzC.trans a.normalizes, a.disjoint, a.sup_eq⟩
  · exact (exclude x hxC (hx.trans (a.prime_eq_three_of_exceptional e p hp hx)) A a e).elim

/-- Bender's odd-prime centralizer decomposition (4.1): for an element of
order three or five in `C_G(z)`, its full ambient centralizer is the product
of a cyclic subgroup of order `p` or 15 with `⟨z⟩`. The odd subgroup is
normalized by `⟨z⟩` and disjoint from it; normality is relative to `C_G(x)`.
The complement, structural alternatives, and exceptional exclusion are all
proved from the original hypotheses. -/
public theorem oddPrimeCentralizerStructure [IsSimpleGroup G] :
    OddPrimeCentralizerStructure h :=
  h.oddPrimeCentralizerStructure_of_alternatives
    h.oddCentralizerAlternatives h.not_exceptionalOddNormalizer

end CFSG.Quasithin.Janko1CentralizerData
