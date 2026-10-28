module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.AlternativesData
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.ComplementAction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.ExceptionalNormalizer

/-!
# Janko's odd-centralizer alternatives

`ComplementAction` proves uniqueness and normalizer invariance of the actual
odd complement, constructs the distinguished involution action, and proves
that the complement has central commutator subgroup contained in `⟨x⟩`.

`Shape` classifies that complement as cyclic of order `p` or 15, or elementary
abelian of order 27. In the latter branch, `ExceptionalNormalizer` constructs
actual subgroups `V` and `X` with `V` elementary abelian of order four,
`|X| = 3`, `X ≤ N_G(V)`, and `N_G(A) = A ⊔ (V ⊔ X)`.

The final assembly discharges both premises of the conditional interface below.
Its complement hypothesis is supplied by `exists_oddCentralizerComplement`;
the independent exclusion of the exceptional branch belongs to the consumer
proving the full odd-prime centralizer structure.

Source: Bender, *Finite groups with large subgroups* (1974), (4.1), printed
p.225, citing the proof of Janko (1966), Lemma 3.1.
-/

namespace CFSG.Quasithin.Janko1CentralizerData

variable {G : Type*} [Group G]

/-- Assemble the structural alternatives once both the complement shape and
the exceptional ambient normalizer have been independently established. -/
public theorem oddCentralizerAlternatives_of_shape_and_normalizer
    (p : ℕ) (A : Subgroup G)
    (shape : (IsCyclic A ∧ (Nat.card A = p ∨ Nat.card A = 15)) ∨
      (IsElementaryAbelian 3 A ∧ Nat.card A = 27))
    (normalizer : IsElementaryAbelian 3 A → Nat.card A = 27 →
      ExceptionalOddNormalizer A) :
    (IsCyclic A ∧ (Nat.card A = p ∨ Nat.card A = 15)) ∨
      ExceptionalOddNormalizer A := by
  rcases shape with hcyc | ⟨he, hc⟩
  · exact Or.inl hcyc
  · exact Or.inr (normalizer he hc)

/-- The actual odd centralizer complement has the source cyclic alternatives
or the full exceptional ambient normalizer configuration. -/
public theorem oddCentralizerAlternatives [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x : G) (hxC : x ∈ Subgroup.centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (A : Subgroup G) (a : OddCentralizerComplement h x A) :
    (IsCyclic A ∧ (Nat.card A = p ∨ Nat.card A = 15)) ∨
      ExceptionalOddNormalizer A := by
  exact oddCentralizerAlternatives_of_shape_and_normalizer p A
    (h.oddCentralizerShape p hp x hxC hx A a)
    (h.exceptionalOddNormalizer_of_elementary p hp x hxC hx A a)

end CFSG.Quasithin.Janko1CentralizerData
