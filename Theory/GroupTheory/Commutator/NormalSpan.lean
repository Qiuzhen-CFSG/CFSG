module
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Commutators of a relatively normal actor on a conjugate span

If H normalizes K and A lies in H, then [⟨A^H⟩,K] = ⟨[A,K]^H⟩.
The subgroup centralizing K modulo the right-hand span contains A and is
H-invariant, which gives the forward inclusion. Conjugating commutators gives
the reverse inclusion. Nested spans along J ≤ H give the same H-span.

This transports the reduced natural seeds on U_(KT) to their full original
supports on U_H in Aschbacher--Smith14.6.22, printed p.1038.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- Relative normality transports the commutator of a seed through its
ambient conjugate span. -/
theorem commutator_conjugateSpanBy_of_normalized_right
    (A H K : Subgroup G) (hAH : A ≤ H)
    (hHK : H ≤ normalizer (K : Set G)) :
    ⁅conjugateSpanBy A H,K⁆ = conjugateSpanBy ⁅A,K⁆ H := by
  let W := conjugateSpanBy ⁅A,K⁆ H
  have hHW : H ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy _ _
  have hpre : A ≤ commutatorPreimage H K W :=
    le_commutatorPreimage hAH (le_conjugateSpanBy _ _)
  have hspan : conjugateSpanBy A H ≤ commutatorPreimage H K W :=
    conjugateSpanBy_le hpre
      (commutatorPreimage_normalized H K W H hHW H.le_normalizer hHK hHW)
  refine le_antisymm ((commutator_mono hspan le_rfl).trans
    (commutator_commutatorPreimage_le H K W hHW)) ?_
  apply conjugateSpanBy_le (commutator_mono (le_conjugateSpanBy _ _) le_rfl)
  intro h hh
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy A H hh),
    mem_normalizer_iff_map_conj_eq.mp (hHK hh)]

/-- Spanning inside an intermediate actor group and then the full group
is the same literal conjugate span. -/
theorem conjugateSpanBy_nested_of_le (A J H : Subgroup G) (hJH : J ≤ H) :
    conjugateSpanBy (conjugateSpanBy A J) H = conjugateSpanBy A H := by
  apply le_antisymm
  · exact conjugateSpanBy_le (conjugateSpanBy_mono le_rfl hJH)
      (le_normalizer_conjugateSpanBy _ _)
  · exact conjugateSpanBy_mono (le_conjugateSpanBy _ _) le_rfl
end Subgroup

