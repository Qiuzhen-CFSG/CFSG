module

public import Mathlib.GroupTheory.Index
public import Mathlib.Order.Atoms

/-!
# Computing a maximal subgroup quotient in an ambient normalizer

Let `S` be normal in a maximal proper subgroup `M` of `G`. Then `M`
normalizes the image of `S` in `G`. If that ambient normalizer is proper,
maximality identifies it with `M`. An element of the normalizer outside the
image of `S` rules out index one, so an upper bound of two gives index two.

The proof uses relative normality and transports the index along the subgroup
inclusion. It needs no simplicity assumption on `G` or `S`.

Source application: the `Sp₄(q):2` case of G. Malle, J. Algebra 139 (1991),
52–69, DOI 10.1016/0021-8693(91)90283-E. The model-specific normalizer bound
and properness witnesses are separate from this elementary argument.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- A maximal subgroup containing a relatively normal subgroup is its full
ambient normalizer whenever that normalizer is proper. -/
theorem normalizer_map_eq_of_isCoatom_of_ne_top
    (M : Subgroup G) (hM : IsCoatom M) (S : Subgroup M) [S.Normal]
    (hproper : normalizer (S.map M.subtype : Set G) ≠ ⊤) :
    normalizer (S.map M.subtype : Set G) = M := by
  apply (hM.le_iff_eq hproper).mp
  simpa only [S.normalizer_eq_top, ← MonoidHom.range_eq_map, M.range_subtype] using
    S.le_normalizer_map M.subtype

/-- A proper ambient normalizer, an element outside the supplied subgroup,
and an upper bound of two determine the original maximal quotient. -/
theorem quotient_card_eq_two_of_normalizer_bound [Finite G]
    (M : Subgroup G) (hM : IsCoatom M) (S : Subgroup M) [S.Normal]
    (hbound : (S.map M.subtype).relIndex (normalizer (S.map M.subtype : Set G)) ≤ 2)
    (t : G) (ht : t ∈ normalizer (S.map M.subtype : Set G))
    (htS : t ∉ S.map M.subtype)
    (hproper : normalizer (S.map M.subtype : Set G) ≠ ⊤) :
    Nat.card (M ⧸ S) = 2 := by
  have hN := normalizer_map_eq_of_isCoatom_of_ne_top M hM S hproper
  have hindex : (S.map M.subtype).relIndex M = S.index := by
    rw [relIndex, subgroupOf, comap_map_eq_self_of_injective M.subtype_injective]
  have hupper : S.index ≤ 2 := by rwa [hN, hindex] at hbound
  have hStop : S ≠ ⊤ := by
    intro heq
    apply htS
    rw [heq, ← MonoidHom.range_eq_map, M.range_subtype]
    rwa [hN] at ht
  have hlower := S.one_lt_index_of_ne_top hStop
  change S.index = 2
  exact Nat.le_antisymm hupper hlower

end Subgroup
