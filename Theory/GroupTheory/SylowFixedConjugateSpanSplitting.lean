module
public import Theory.GroupTheory.SylowCentralizerComplement
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Splitting a binary conjugate span at a Sylow-fixed seed

Odd-index averaging supplies a fixed representative modulo the moved subgroup
for every seed element. The moved subgroup and fixed elements are invariant,
so together they contain the whole conjugate span. This is the relative-actor
form of the splitting in Aschbacher--Smith B.2.13--14, printed p.78.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G] {Z H : Subgroup G} [Finite H]

/-- A seed element has a fixed representative in its coset modulo the moved span. -/
theorem conjugateSpan_fixed_coset_of_sylow
    [IsElementaryAbelian 2 (conjugateSpanBy Z H)] (P : Sylow 2 H)
    (hZP : Z ≤ centralizer ((P : Subgroup H).map H.subtype : Set G))
    {z : G} (hz : z ∈ Z) :
    ∃ u ∈ ⁅conjugateSpanBy Z H,H⁆,
      u * z ∈ conjugateSpanBy Z H ⊓ centralizer (H : Set G) := by
  let U := conjugateSpanBy Z H
  have hmove : ⁅U,H⁆ ≤ U :=
    le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy Z H)
  let : IsElementaryAbelian 2 (⁅U,H⁆ : Subgroup G) := IsElementaryAbelian.of_le hmove
  obtain ⟨u,hu,huc⟩ := fixed_coset_of_sylow H ⁅U,H⁆
    (normalizer_commutator_ge_right U H)
    (fun u hu => elemPow_eq_one_of_isElementaryAbelian u hu) P z
    (fun a ha => by
      rw [commutator_comm]
      exact commutator_mem_commutator ha (le_conjugateSpanBy Z H hz))
    (fun a ha => hZP hz a (mem_map_of_mem H.subtype ha))
  exact ⟨u,hu,⟨U.mul_mem (hmove hu) (le_conjugateSpanBy Z H hz),huc⟩⟩

/-- A binary conjugate span is the product of its moved subgroup and fixed subgroup. -/
theorem conjugateSpan_split_of_sylow_fixed
    [IsElementaryAbelian 2 (conjugateSpanBy Z H)] (P : Sylow 2 H)
    (hZP : Z ≤ centralizer ((P : Subgroup H).map H.subtype : Set G)) :
    conjugateSpanBy Z H = ⁅conjugateSpanBy Z H,H⁆ ⊔
      (conjugateSpanBy Z H ⊓ centralizer (H : Set G)) := by
  let U := conjugateSpanBy Z H
  have hn := le_normalizer_conjugateSpanBy Z H
  have hmove : ⁅U,H⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp hn
  apply le_antisymm ?_ (sup_le hmove inf_le_left)
  apply conjugateSpanBy_le
  · intro z hz
    obtain ⟨u,hu,huc⟩ := conjugateSpan_fixed_coset_of_sylow P hZP hz
    have hh := mul_mem_sup (⁅U,H⁆.inv_mem hu) huc
    simpa only [inv_mul_cancel_left] using hh
  · exact (le_inf (normalizer_commutator_ge_right U H)
      ((le_inf hn ((le_centralizer_iff.mp le_rfl).trans
        (Subgroup.centralizer_le_normalizer (centralizer (H : Set G) : Set G)))).trans
        inf_normalizer_le_normalizer_inf)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

end Theory.GroupTheory
