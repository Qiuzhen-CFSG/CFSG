module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RowOrbit.FirstTargets
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RowOrbit.SecondTargets

/-!
# All coordinate rows lie in the zeroth-row orbit

Reading the selected A- and B-edges in parent order lists the children
1,...,1791 exactly once, each after its parent. The sequential certificate
and the two checked literal row tables therefore construct all coordinate
rows by right multiplication from e₀ᵀ. Their span is the whole row space.
No presentation, group action, or irreducibility premise is used.

Source data and the finite certificate construction: `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
open Matrix RowData

set_option maxRecDepth 8192 in
private theorem edges_checked :
    checkEdges 1792 1 (edgesFrom 0 firstTargets.toList secondTargets.toList) = true := by
  decide +kernel

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792

theorem coordinateRows_reachable
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 1792) (Fin 1792) (ZMod 2)))
    (hA : Data1792.first ∈ Q) (hB : Data1792.second ∈ Q) :
    ∀ i : Fin 1792, ∃ R ∈ Q, vecMul (Pi.single 0 1) R = Pi.single i 1 := by
  apply row_realizations_of_predecessor 1791 Q Data1792.first Data1792.second hA hB
  intro j hj
  have hj0 : j.val ≠ 0 := fun hz => hj (Fin.ext hz)
  obtain ⟨q,hq,he⟩ := checkEdges_sound 1792 1
    (edgesFrom 0 firstTargets.toList secondTargets.toList) edges_checked
    j.val (by omega) j.isLt
  obtain ⟨i,hi,_,hqi,ht⟩ := edgesFrom_sound 0 firstTargets.toList secondTargets.toList q j.val he
  have hsize : firstTargets.size = 1792 := by decide +kernel
  have hi' : i < 1792 := by simpa only [Array.length_toList, hsize] using hi
  refine ⟨⟨i,hi'⟩, ?_, ?_⟩
  · change i < j.val
    omega
  · have lookup (a : Array Nat) : a.toList[i]! = a[i]! := by
      simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    rcases ht with ht | ht
    · left
      exact row_of_target 1792 Data1792.firstRows firstTargets firstTargets_checked
        hsize ⟨i,hi'⟩ j (by simpa only [lookup] using ht) hj0
    · right
      exact row_of_target 1792 Data1792.secondRows secondTargets secondTargets_checked
        (by decide +kernel) ⟨i,hi'⟩ j (by simpa only [lookup] using ht) hj0

theorem rowOrbit_eq_top
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 1792) (Fin 1792) (ZMod 2)))
    (hA : Data1792.first ∈ Q) (hB : Data1792.second ∈ Q) :
    Submodule.span (ZMod 2) (Set.range (fun R : Q => vecMul (Pi.single 0 1) R.val)) = ⊤ :=
  row_span Q (Pi.single 0 1) (coordinateRows_reachable Q hA hB)
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
