module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Extraction
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Diagram reversal on the actual binary SL₅ group

Compose inverse transpose with conjugation by the coordinate-reversing
permutation matrix. This is an automorphism of the actual special linear
group; it takes the root `(a,b)` to `(rev b,rev a)` and each simple generator
to the one at the reversed node. Consequently the same vector, for the
representation precomposed with this automorphism, has support `{0,1}`
whenever its original support is `{2,3}`.

`EndPairs` applies the left end-pair certificate to this transported vector.
Source application: Guralnick–Malle, Classification of 2F-modules II,
Lemma 4.2/Table 6 and Proposition 4.8(3B); Aschbacher–Smith K.3.2,
printed pp.454–455.
-/

public section
open Representation.SL5TenDimensional
open Representation.SL5TenDimensional.Classification
open Representation.SL5TenDimensional.Classification.Separated
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.AdjacentDimension.EndPairs

private def reverseMatrix : Group :=
  ⟨![![0,0,0,0,1], ![0,0,0,1,0], ![0,0,1,0,0], ![0,1,0,0,0], ![1,0,0,0,0]],
    by decide +kernel⟩

/-- Inverse transpose followed by reversal of the five coordinates. -/
def diagramReversal : MulAut Group :=
  MulAut.conj reverseMatrix * BinaryLinear.OuterCyclic.graphSL 5

private theorem graph_root (a b : Fin 5) :
    BinaryLinear.OuterCyclic.graphSL 5 (rootElement a b) = rootElement b a := by
  change (Matrix.SpecialLinearGroup.transpose (rootElement a b))⁻¹ = rootElement b a
  apply inv_eq_of_mul_eq_one_right
  revert a b
  decide +kernel

private theorem reverseMatrix_inv : reverseMatrix⁻¹ = reverseMatrix := by
  apply inv_eq_of_mul_eq_one_right
  decide +kernel

/-- Positive roots remain positive, with reversed endpoints. -/
theorem diagramReversal_root (a b : Fin 5) :
    diagramReversal (rootElement a b) = rootElement b.rev a.rev := by
  change reverseMatrix * BinaryLinear.OuterCyclic.graphSL 5 (rootElement a b) *
    reverseMatrix⁻¹ = _
  rw [graph_root, reverseMatrix_inv]
  revert a b
  decide +kernel

private theorem diagramReversal_swap (i : Fin 4) :
    diagramReversal (simpleSwap i) = simpleSwap i.rev := by
  change reverseMatrix * BinaryLinear.OuterCyclic.graphSL 5 (simpleSwap i) *
    reverseMatrix⁻¹ = _
  have hs : BinaryLinear.OuterCyclic.graphSL 5 (simpleSwap i) = simpleSwap i := by
    change (Matrix.SpecialLinearGroup.transpose (simpleSwap i))⁻¹ = simpleSwap i
    apply inv_eq_of_mul_eq_one_right
    revert i
    decide +kernel
  rw [hs, reverseMatrix_inv]
  revert i
  decide +kernel

private theorem diagramReversal_lower (i : Fin 4) :
    diagramReversal (simpleLower i) = simpleLower i.rev := by
  have he : simpleLower i = rootElement i.succ i.castSucc := by
    unfold rootElement
    rw [dif_pos (show i.succ ≠ i.castSucc by
      intro he
      have hh := congrArg Fin.val he
      simp at hh)]
    rfl
  rw [he, diagramReversal_root]
  revert i
  decide +kernel

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The literal automorphism transports the right end pair to the left end pair. -/
theorem reverse_local_highest {ρ : Representation (ZMod 2) Group V} {v : V}
    (h : LocalHighestVector ρ {2, 3} v) :
    LocalHighestVector (ρ.comp diagramReversal.toMonoidHom) {0, 1} v := by
  constructor
  · intro a b hab
    change ρ (diagramReversal (Matrix.SpecialLinearGroup.transvection (ne_of_lt hab)
      (1 : ZMod 2))) v = v
    have hr : rootElement a b = Matrix.SpecialLinearGroup.transvection (ne_of_lt hab)
        (1 : ZMod 2) := by simp [rootElement, ne_of_lt hab]
    rw [← hr, diagramReversal_root]
    have hba : b.rev < a.rev := Fin.rev_lt_rev.mpr hab
    simpa [rootElement, ne_of_lt hba] using h.upper_fixed b.rev a.rev hba
  · intro i hi
    change ρ (diagramReversal (simpleSwap i)) v = v
    rw [diagramReversal_swap]
    apply h.inactive_fixed
    fin_cases i <;> simp_all
  · intro i hi
    change v + ρ (diagramReversal (simpleSwap i)) v +
      ρ (diagramReversal (simpleLower i)) v = 0
    rw [diagramReversal_swap, diagramReversal_lower]
    apply h.active_relation
    fin_cases i <;> simp_all

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.AdjacentDimension.EndPairs
