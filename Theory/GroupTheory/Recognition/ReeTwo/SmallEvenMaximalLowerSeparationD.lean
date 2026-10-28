module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerWordsD
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperCoordinates

/-!+# Nonmembership certificates for lower even maximal subgroups, batch D

Each noncentric binary branch has a commuting witness from the word certificate.
The projected-orbit theorem bounds its subgroup by a finite orbit missing that
witness. All generator identities and orbit transitions are kernel checked.

Source: Shinoda (1975), (2.3), pp. 81–82. Projection soundness is proved in
`SmallEvenNodeWitnessesUpperCoordinates`; diagnostic inputs and original row
numbering are documented in `SmallEvenDescentEdgeData`.
-/

namespace ReeTwo.SylowModel.SmallEvenMaximalLower
open SmallEvenMaximalBranches UpperCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace Node81

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![31, 2, 29, 0, 27, 6, 25, 4, 23, 10, 21, 8, 19, 14, 17, 12, 15, 18, 13, 16, 11, 22, 9, 20, 7, 26, 5, 24, 3, 30, 1, 28], ![18, 11, 16, 9, 22, 15, 20, 13, 26, 3, 24, 1, 30, 7, 28, 5, 2, 27, 0, 25, 6, 31, 4, 29, 10, 19, 8, 17, 14, 23, 12, 21], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![31, 2, 29, 0, 27, 6, 25, 4, 23, 10, 21, 8, 19, 14, 17, 12, 15, 18, 13, 16, 11, 22, 9, 20, 7, 26, 5, 24, 3, 30, 1, 28], ![18, 11, 16, 9, 22, 15, 20, 13, 26, 3, 24, 1, 30, 7, 28, 5, 2, 27, 0, 25, 6, 31, 4, 29, 10, 19, 8, 17, 14, 23, 12, 21], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (8 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![31, 30, 1, 0, 27, 26, 5, 4, 11, 10, 21, 20, 15, 14, 17, 16, 19, 18, 13, 12, 23, 22, 9, 8, 7, 6, 25, 24, 3, 2, 29, 28], ![18, 19, 8, 9, 22, 23, 12, 13, 2, 3, 24, 25, 6, 7, 28, 29, 26, 27, 0, 1, 30, 31, 4, 5, 10, 11, 16, 17, 14, 15, 20, 21], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![3, 2, 29, 28, 7, 6, 25, 24, 23, 22, 9, 8, 19, 18, 13, 12, 15, 14, 17, 16, 11, 10, 21, 20, 27, 26, 5, 4, 31, 30, 1, 0], ![10, 11, 16, 17, 14, 15, 20, 21, 26, 27, 0, 1, 30, 31, 4, 5, 2, 3, 24, 25, 6, 7, 28, 29, 18, 19, 8, 9, 22, 23, 12, 13], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (9 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

namespace Mask10

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![16, 9, 18, 11, 20, 13, 22, 15, 24, 1, 26, 3, 28, 5, 30, 7, 0, 25, 2, 27, 4, 29, 6, 31, 8, 17, 10, 19, 12, 21, 14, 23], ![19, 14, 17, 12, 23, 10, 21, 8, 27, 6, 25, 4, 31, 2, 29, 0, 3, 30, 1, 28, 7, 26, 5, 24, 11, 22, 9, 20, 15, 18, 13, 16], ![29, 28, 31, 30, 25, 24, 27, 26, 21, 20, 23, 22, 17, 16, 19, 18, 13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 17, 10, 19, 12, 21, 14, 23, 0, 25, 2, 27, 4, 29, 6, 31, 24, 1, 26, 3, 28, 5, 30, 7, 16, 9, 18, 11, 20, 13, 22, 15], ![15, 18, 13, 16, 11, 22, 9, 20, 7, 26, 5, 24, 3, 30, 1, 28, 31, 2, 29, 0, 27, 6, 25, 4, 23, 10, 21, 8, 19, 14, 17, 12]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (10 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask10

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![3, 30, 29, 0, 7, 26, 25, 4, 23, 10, 9, 20, 19, 14, 13, 16, 15, 18, 17, 12, 11, 22, 21, 8, 27, 6, 5, 24, 31, 2, 1, 28], ![18, 11, 8, 17, 22, 15, 12, 21, 2, 27, 24, 1, 6, 31, 28, 5, 26, 3, 0, 25, 30, 7, 4, 29, 10, 19, 16, 9, 14, 23, 20, 13], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![31, 2, 1, 28, 27, 6, 5, 24, 11, 22, 21, 8, 15, 18, 17, 12, 19, 14, 13, 16, 23, 10, 9, 20, 7, 26, 25, 4, 3, 30, 29, 0], ![10, 19, 16, 9, 14, 23, 20, 13, 26, 3, 0, 25, 30, 7, 4, 29, 2, 27, 24, 1, 6, 31, 28, 5, 18, 11, 8, 17, 22, 15, 12, 21], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (11 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask11

namespace Mask12

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![31, 6, 29, 4, 27, 2, 25, 0, 23, 14, 21, 12, 19, 10, 17, 8, 15, 22, 13, 20, 11, 18, 9, 16, 7, 30, 5, 28, 3, 26, 1, 24], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![4, 21, 6, 23, 0, 17, 2, 19, 12, 29, 14, 31, 8, 25, 10, 27, 20, 5, 22, 7, 16, 1, 18, 3, 28, 13, 30, 15, 24, 9, 26, 11], ![17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![15, 22, 13, 20, 11, 18, 9, 16, 7, 30, 5, 28, 3, 26, 1, 24, 31, 6, 29, 4, 27, 2, 25, 0, 23, 14, 21, 12, 19, 10, 17, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![4, 21, 6, 23, 0, 17, 2, 19, 12, 29, 14, 31, 8, 25, 10, 27, 20, 5, 22, 7, 16, 1, 18, 3, 28, 13, 30, 15, 24, 9, 26, 11]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (12 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask12

namespace Mask13

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![31, 2, 29, 0, 27, 6, 25, 4, 11, 22, 9, 20, 15, 18, 13, 16, 19, 14, 17, 12, 23, 10, 21, 8, 7, 26, 5, 24, 3, 30, 1, 28], ![10, 19, 8, 17, 14, 23, 12, 21, 26, 3, 24, 1, 30, 7, 28, 5, 2, 27, 0, 25, 6, 31, 4, 29, 18, 11, 16, 9, 22, 15, 20, 13], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![3, 30, 1, 28, 7, 26, 5, 24, 23, 10, 21, 8, 19, 14, 17, 12, 15, 18, 13, 16, 11, 22, 9, 20, 27, 6, 25, 4, 31, 2, 29, 0], ![18, 11, 16, 9, 22, 15, 20, 13, 2, 27, 0, 25, 6, 31, 4, 29, 26, 3, 24, 1, 30, 7, 28, 5, 10, 19, 8, 17, 14, 23, 12, 21], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (13 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask13

namespace Mask14

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![9, 12, 11, 14, 13, 8, 15, 10, 1, 4, 3, 6, 5, 0, 7, 2, 25, 28, 27, 30, 29, 24, 31, 26, 17, 20, 19, 22, 21, 16, 23, 18], ![19, 14, 17, 12, 23, 10, 21, 8, 27, 6, 25, 4, 31, 2, 29, 0, 3, 30, 1, 28, 7, 26, 5, 24, 11, 22, 9, 20, 15, 18, 13, 16], ![29, 28, 31, 30, 25, 24, 27, 26, 21, 20, 23, 22, 17, 16, 19, 18, 13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![13, 8, 15, 10, 9, 12, 11, 14, 5, 0, 7, 2, 1, 4, 3, 6, 29, 24, 31, 26, 25, 28, 27, 30, 21, 16, 23, 18, 17, 20, 19, 22], ![15, 18, 13, 16, 11, 22, 9, 20, 7, 26, 5, 24, 3, 30, 1, 28, 31, 2, 29, 0, 27, 6, 25, 4, 23, 10, 21, 8, 19, 14, 17, 12]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (14 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask14

namespace Mask15

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![3, 2, 1, 0, 7, 6, 5, 4, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 27, 26, 25, 24, 31, 30, 29, 28], ![10, 11, 8, 9, 14, 15, 12, 13, 26, 27, 24, 25, 30, 31, 28, 29, 2, 3, 0, 1, 6, 7, 4, 5, 18, 19, 16, 17, 22, 23, 20, 21], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![31, 30, 29, 28, 27, 26, 25, 24, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 7, 6, 5, 4, 3, 2, 1, 0], ![18, 19, 16, 17, 22, 23, 20, 21, 2, 3, 0, 1, 6, 7, 4, 5, 26, 27, 24, 25, 30, 31, 28, 29, 10, 11, 8, 9, 14, 15, 12, 13], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (15 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask15

public theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ m : Fin 16,
      (branches (fun k => m.val.testBit k.val)).Separation gen
        (fun k => m.val.testBit k.val) (pivot (fun k => m.val.testBit k.val)) := by
    intro m
    fin_cases m
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact Mask8.not_mem
    · exact Mask9.not_mem
    · exact Mask10.not_mem
    · exact Mask11.not_mem
    · exact Mask12.not_mem
    · exact Mask13.not_mem
    · exact Mask14.not_mem
    · exact Mask15.not_mem
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 81) :
    Classified H := classify separation_checked H hH

end Node81

namespace Node83

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![29, 16, 31, 18, 25, 20, 27, 22, 21, 24, 23, 26, 17, 28, 19, 30, 13, 0, 15, 2, 9, 4, 11, 6, 5, 8, 7, 10, 1, 12, 3, 14], ![18, 11, 16, 9, 22, 15, 20, 13, 26, 3, 24, 1, 30, 7, 28, 5, 2, 27, 0, 25, 6, 31, 4, 29, 10, 19, 8, 17, 14, 23, 12, 21], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![29, 16, 31, 18, 25, 20, 27, 22, 21, 24, 23, 26, 17, 28, 19, 30, 13, 0, 15, 2, 9, 4, 11, 6, 5, 8, 7, 10, 1, 12, 3, 14], ![18, 11, 16, 9, 22, 15, 20, 13, 26, 3, 24, 1, 30, 7, 28, 5, 2, 27, 0, 25, 6, 31, 4, 29, 10, 19, 8, 17, 14, 23, 12, 21], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (8 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![29, 28, 19, 18, 21, 20, 27, 26, 25, 24, 23, 22, 17, 16, 31, 30, 1, 0, 15, 14, 9, 8, 7, 6, 5, 4, 11, 10, 13, 12, 3, 2], ![18, 19, 8, 9, 14, 15, 20, 21, 2, 3, 24, 25, 30, 31, 4, 5, 26, 27, 0, 1, 6, 7, 28, 29, 10, 11, 16, 17, 22, 23, 12, 13], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![17, 16, 31, 30, 25, 24, 23, 22, 21, 20, 27, 26, 29, 28, 19, 18, 13, 12, 3, 2, 5, 4, 11, 10, 9, 8, 7, 6, 1, 0, 15, 14], ![10, 11, 16, 17, 22, 23, 12, 13, 26, 27, 0, 1, 6, 7, 28, 29, 2, 3, 24, 25, 30, 31, 4, 5, 18, 19, 8, 9, 14, 15, 20, 21], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (9 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

namespace Mask10

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![16, 9, 18, 11, 20, 13, 22, 15, 24, 1, 26, 3, 28, 5, 30, 7, 0, 25, 2, 27, 4, 29, 6, 31, 8, 17, 10, 19, 12, 21, 14, 23], ![15, 2, 13, 0, 11, 6, 9, 4, 7, 10, 5, 8, 3, 14, 1, 12, 31, 18, 29, 16, 27, 22, 25, 20, 23, 26, 21, 24, 19, 30, 17, 28], ![13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2, 29, 28, 31, 30, 25, 24, 27, 26, 21, 20, 23, 22, 17, 16, 19, 18], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19], ![8, 17, 10, 19, 12, 21, 14, 23, 0, 25, 2, 27, 4, 29, 6, 31, 24, 1, 26, 3, 28, 5, 30, 7, 16, 9, 18, 11, 20, 13, 22, 15], ![3, 14, 1, 12, 7, 10, 5, 8, 11, 6, 9, 4, 15, 2, 13, 0, 19, 30, 17, 28, 23, 26, 21, 24, 27, 22, 25, 20, 31, 18, 29, 16]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (10 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask10

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![17, 28, 31, 18, 25, 20, 23, 26, 21, 24, 27, 22, 29, 16, 19, 30, 13, 0, 3, 14, 5, 8, 11, 6, 9, 4, 7, 10, 1, 12, 15, 2], ![18, 11, 8, 17, 14, 23, 20, 13, 2, 27, 24, 1, 30, 7, 4, 29, 26, 3, 0, 25, 6, 31, 28, 5, 10, 19, 16, 9, 22, 15, 12, 21], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![29, 16, 19, 30, 21, 24, 27, 22, 25, 20, 23, 26, 17, 28, 31, 18, 1, 12, 15, 2, 9, 4, 7, 10, 5, 8, 11, 6, 13, 0, 3, 14], ![10, 19, 16, 9, 22, 15, 12, 21, 26, 3, 0, 25, 6, 31, 28, 5, 2, 27, 24, 1, 30, 7, 4, 29, 18, 11, 8, 17, 14, 23, 20, 13], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (11 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask11

namespace Mask12

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![29, 16, 31, 18, 25, 20, 27, 22, 21, 24, 23, 26, 17, 28, 19, 30, 13, 0, 15, 2, 9, 4, 11, 6, 5, 8, 7, 10, 1, 12, 3, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![14, 23, 12, 21, 10, 19, 8, 17, 6, 31, 4, 29, 2, 27, 0, 25, 30, 7, 28, 5, 26, 3, 24, 1, 22, 15, 20, 13, 18, 11, 16, 9], ![25, 24, 27, 26, 29, 28, 31, 30, 17, 16, 19, 18, 21, 20, 23, 22, 9, 8, 11, 10, 13, 12, 15, 14, 1, 0, 3, 2, 5, 4, 7, 6], ![5, 8, 7, 10, 1, 12, 3, 14, 13, 0, 15, 2, 9, 4, 11, 6, 21, 24, 23, 26, 17, 28, 19, 30, 29, 16, 31, 18, 25, 20, 27, 22], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![14, 23, 12, 21, 10, 19, 8, 17, 6, 31, 4, 29, 2, 27, 0, 25, 30, 7, 28, 5, 26, 3, 24, 1, 22, 15, 20, 13, 18, 11, 16, 9]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (12 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask12

namespace Mask13

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![29, 28, 31, 30, 21, 20, 23, 22, 25, 24, 27, 26, 17, 16, 19, 18, 1, 0, 3, 2, 9, 8, 11, 10, 5, 4, 7, 6, 13, 12, 15, 14], ![10, 11, 8, 9, 22, 23, 20, 21, 26, 27, 24, 25, 6, 7, 4, 5, 2, 3, 0, 1, 30, 31, 28, 29, 18, 19, 16, 17, 14, 15, 12, 13], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![17, 16, 19, 18, 25, 24, 27, 26, 21, 20, 23, 22, 29, 28, 31, 30, 13, 12, 15, 14, 5, 4, 7, 6, 9, 8, 11, 10, 1, 0, 3, 2], ![18, 19, 16, 17, 14, 15, 12, 13, 2, 3, 0, 1, 30, 31, 28, 29, 26, 27, 24, 25, 6, 7, 4, 5, 10, 11, 8, 9, 22, 23, 20, 21], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (13 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask13

namespace Mask14

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![31, 14, 29, 12, 27, 10, 25, 8, 23, 6, 21, 4, 19, 2, 17, 0, 15, 30, 13, 28, 11, 26, 9, 24, 7, 22, 5, 20, 3, 18, 1, 16], ![11, 2, 9, 0, 15, 6, 13, 4, 3, 10, 1, 8, 7, 14, 5, 12, 27, 18, 25, 16, 31, 22, 29, 20, 19, 26, 17, 24, 23, 30, 21, 28], ![9, 8, 11, 10, 13, 12, 15, 14, 1, 0, 3, 2, 5, 4, 7, 6, 25, 24, 27, 26, 29, 28, 31, 30, 17, 16, 19, 18, 21, 20, 23, 22], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![15, 30, 13, 28, 11, 26, 9, 24, 7, 22, 5, 20, 3, 18, 1, 16, 31, 14, 29, 12, 27, 10, 25, 8, 23, 6, 21, 4, 19, 2, 17, 0], ![3, 10, 1, 8, 7, 14, 5, 12, 11, 2, 9, 0, 15, 6, 13, 4, 19, 26, 17, 24, 23, 30, 21, 28, 27, 18, 25, 16, 31, 22, 29, 20]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (14 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask14

namespace Mask15

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![17, 28, 19, 30, 25, 20, 27, 22, 21, 24, 23, 26, 29, 16, 31, 18, 13, 0, 15, 2, 5, 8, 7, 10, 9, 4, 11, 6, 1, 12, 3, 14], ![10, 19, 8, 17, 22, 15, 20, 13, 26, 3, 24, 1, 6, 31, 4, 29, 2, 27, 0, 25, 30, 7, 28, 5, 18, 11, 16, 9, 14, 23, 12, 21], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![29, 16, 31, 18, 21, 24, 23, 26, 25, 20, 27, 22, 17, 28, 19, 30, 1, 12, 3, 14, 9, 4, 11, 6, 5, 8, 7, 10, 13, 0, 15, 2], ![18, 11, 16, 9, 14, 23, 12, 21, 2, 27, 0, 25, 30, 7, 28, 5, 26, 3, 24, 1, 6, 31, 4, 29, 10, 19, 8, 17, 22, 15, 20, 13], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (15 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask15

public theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ m : Fin 16,
      (branches (fun k => m.val.testBit k.val)).Separation gen
        (fun k => m.val.testBit k.val) (pivot (fun k => m.val.testBit k.val)) := by
    intro m
    fin_cases m
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact Mask8.not_mem
    · exact Mask9.not_mem
    · exact Mask10.not_mem
    · exact Mask11.not_mem
    · exact Mask12.not_mem
    · exact Mask13.not_mem
    · exact Mask14.not_mem
    · exact Mask15.not_mem
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 83) :
    Classified H := classify separation_checked H hH

end Node83

namespace Node95

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (4 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 4 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 136 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (5 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 4 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 8 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

public theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ m : Fin 8,
      (branches (fun k => m.val.testBit k.val)).Separation gen
        (fun k => m.val.testBit k.val) (pivot (fun k => m.val.testBit k.val)) := by
    intro m
    fin_cases m
    · trivial
    · trivial
    · trivial
    · trivial
    · exact Mask4.not_mem
    · exact Mask5.not_mem
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 95) :
    Classified H := classify separation_checked H hH

end Node95

namespace Node96

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![41, 32, 39, 46, 27, 18, 17, 24, 33, 40, 47, 38, 19, 26, 25, 16, 57, 48, 55, 62, 11, 2, 1, 8, 49, 56, 63, 54, 3, 10, 9, 0, 51, 58, 15, 6, 5, 12, 61, 52, 59, 50, 7, 14, 13, 4, 53, 60, 35, 42, 31, 22, 21, 28, 45, 36, 43, 34, 23, 30, 29, 20, 37, 44], ![20, 5, 40, 57, 0, 17, 60, 45, 28, 13, 32, 49, 8, 25, 52, 37, 4, 21, 56, 41, 16, 1, 44, 61, 12, 29, 48, 33, 24, 9, 36, 53, 26, 11, 54, 39, 14, 31, 34, 51, 18, 3, 62, 47, 6, 23, 42, 59, 10, 27, 38, 55, 30, 15, 50, 35, 2, 19, 46, 63, 22, 7, 58, 43], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![41, 32, 39, 46, 27, 18, 17, 24, 33, 40, 47, 38, 19, 26, 25, 16, 57, 48, 55, 62, 11, 2, 1, 8, 49, 56, 63, 54, 3, 10, 9, 0, 51, 58, 15, 6, 5, 12, 61, 52, 59, 50, 7, 14, 13, 4, 53, 60, 35, 42, 31, 22, 21, 28, 45, 36, 43, 34, 23, 30, 29, 20, 37, 44], ![20, 5, 40, 57, 0, 17, 60, 45, 28, 13, 32, 49, 8, 25, 52, 37, 4, 21, 56, 41, 16, 1, 44, 61, 12, 29, 48, 33, 24, 9, 36, 53, 26, 11, 54, 39, 14, 31, 34, 51, 18, 3, 62, 47, 6, 23, 42, 59, 10, 27, 38, 55, 30, 15, 50, 35, 2, 19, 46, 63, 22, 7, 58, 43], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (8 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![41, 20, 47, 26, 37, 24, 35, 22, 33, 28, 39, 18, 45, 16, 43, 30, 57, 4, 63, 10, 53, 8, 51, 6, 49, 12, 55, 2, 61, 0, 59, 14, 1, 60, 7, 50, 13, 48, 11, 62, 9, 52, 15, 58, 5, 56, 3, 54, 17, 44, 23, 34, 29, 32, 27, 46, 25, 36, 31, 42, 21, 40, 19, 38], ![19, 58, 57, 0, 7, 46, 45, 20, 27, 50, 49, 8, 15, 38, 37, 28, 3, 42, 41, 16, 23, 62, 61, 4, 11, 34, 33, 24, 31, 54, 53, 12, 35, 10, 9, 48, 55, 30, 29, 36, 43, 2, 1, 56, 63, 22, 21, 44, 51, 26, 25, 32, 39, 14, 13, 52, 59, 18, 17, 40, 47, 6, 5, 60], ![32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![33, 28, 39, 18, 45, 16, 43, 30, 41, 20, 47, 26, 37, 24, 35, 22, 49, 12, 55, 2, 61, 0, 59, 14, 57, 4, 63, 10, 53, 8, 51, 6, 9, 52, 15, 58, 5, 56, 3, 54, 1, 60, 7, 50, 13, 48, 11, 62, 25, 36, 31, 42, 21, 40, 19, 38, 17, 44, 23, 34, 29, 32, 27, 46], ![3, 42, 41, 16, 23, 62, 61, 4, 11, 34, 33, 24, 31, 54, 53, 12, 19, 58, 57, 0, 7, 46, 45, 20, 27, 50, 49, 8, 15, 38, 37, 28, 51, 26, 25, 32, 39, 14, 13, 52, 59, 18, 17, 40, 47, 6, 5, 60, 35, 10, 9, 48, 55, 30, 29, 36, 43, 2, 1, 56, 63, 22, 21, 44], ![32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (9 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

namespace Mask10

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![20, 5, 56, 41, 0, 17, 44, 61, 28, 13, 48, 33, 8, 25, 36, 53, 4, 21, 40, 57, 16, 1, 60, 45, 12, 29, 32, 49, 24, 9, 52, 37, 10, 27, 54, 39, 30, 15, 34, 51, 2, 19, 62, 47, 22, 7, 42, 59, 26, 11, 38, 55, 14, 31, 50, 35, 18, 3, 46, 63, 6, 23, 58, 43], ![61, 52, 1, 8, 15, 6, 55, 62, 53, 60, 9, 0, 7, 14, 63, 54, 45, 36, 17, 24, 31, 22, 39, 46, 37, 44, 25, 16, 23, 30, 47, 38, 21, 28, 27, 18, 35, 42, 41, 32, 29, 20, 19, 26, 43, 34, 33, 40, 5, 12, 11, 2, 51, 58, 57, 48, 13, 4, 3, 10, 59, 50, 49, 56], ![9, 8, 11, 10, 13, 12, 15, 14, 1, 0, 3, 2, 5, 4, 7, 6, 25, 24, 27, 26, 29, 28, 31, 30, 17, 16, 19, 18, 21, 20, 23, 22, 41, 40, 43, 42, 45, 44, 47, 46, 33, 32, 35, 34, 37, 36, 39, 38, 57, 56, 59, 58, 61, 60, 63, 62, 49, 48, 51, 50, 53, 52, 55, 54], ![50, 51, 52, 53, 54, 55, 48, 49, 58, 59, 60, 61, 62, 63, 56, 57, 34, 35, 36, 37, 38, 39, 32, 33, 42, 43, 44, 45, 46, 47, 40, 41, 22, 23, 16, 17, 18, 19, 20, 21, 30, 31, 24, 25, 26, 27, 28, 29, 6, 7, 0, 1, 2, 3, 4, 5, 14, 15, 8, 9, 10, 11, 12, 13], ![28, 13, 48, 33, 8, 25, 36, 53, 20, 5, 56, 41, 0, 17, 44, 61, 12, 29, 32, 49, 24, 9, 52, 37, 4, 21, 40, 57, 16, 1, 60, 45, 2, 19, 62, 47, 22, 7, 42, 59, 10, 27, 54, 39, 30, 15, 34, 51, 18, 3, 46, 63, 6, 23, 58, 43, 26, 11, 38, 55, 14, 31, 50, 35], ![11, 2, 51, 58, 57, 48, 5, 12, 3, 10, 59, 50, 49, 56, 13, 4, 27, 18, 35, 42, 41, 32, 21, 28, 19, 26, 43, 34, 33, 40, 29, 20, 39, 46, 45, 36, 17, 24, 31, 22, 47, 38, 37, 44, 25, 16, 23, 30, 55, 62, 61, 52, 1, 8, 15, 6, 63, 54, 53, 60, 9, 0, 7, 14]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (10 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask10

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![33, 20, 47, 18, 45, 24, 35, 30, 41, 28, 39, 26, 37, 16, 43, 22, 49, 4, 63, 2, 61, 8, 51, 14, 57, 12, 55, 10, 53, 0, 59, 6, 9, 60, 7, 58, 5, 48, 11, 54, 1, 52, 15, 50, 13, 56, 3, 62, 25, 44, 23, 42, 21, 32, 27, 38, 17, 36, 31, 34, 29, 40, 19, 46], ![19, 42, 41, 0, 7, 62, 61, 20, 27, 34, 33, 8, 15, 54, 53, 28, 3, 58, 57, 16, 23, 46, 45, 4, 11, 50, 49, 24, 31, 38, 37, 12, 35, 26, 25, 48, 55, 14, 13, 36, 43, 18, 17, 56, 63, 6, 5, 44, 51, 10, 9, 32, 39, 30, 29, 52, 59, 2, 1, 40, 47, 22, 21, 60], ![32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![41, 28, 39, 26, 37, 16, 43, 22, 33, 20, 47, 18, 45, 24, 35, 30, 57, 12, 55, 10, 53, 0, 59, 6, 49, 4, 63, 2, 61, 8, 51, 14, 1, 52, 15, 50, 13, 56, 3, 62, 9, 60, 7, 58, 5, 48, 11, 54, 17, 36, 31, 34, 29, 40, 19, 46, 25, 44, 23, 42, 21, 32, 27, 38], ![3, 58, 57, 16, 23, 46, 45, 4, 11, 50, 49, 24, 31, 38, 37, 12, 19, 42, 41, 0, 7, 62, 61, 20, 27, 34, 33, 8, 15, 54, 53, 28, 51, 10, 9, 32, 39, 30, 29, 52, 59, 2, 1, 40, 47, 22, 21, 60, 35, 26, 25, 48, 55, 14, 13, 36, 43, 18, 17, 56, 63, 6, 5, 44], ![32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (11 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask11

namespace Mask12

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![41, 32, 17, 24, 37, 44, 29, 20, 33, 40, 25, 16, 45, 36, 21, 28, 57, 48, 1, 8, 53, 60, 13, 4, 49, 56, 9, 0, 61, 52, 5, 12, 55, 62, 7, 14, 59, 50, 11, 2, 63, 54, 15, 6, 51, 58, 3, 10, 39, 46, 23, 30, 43, 34, 27, 18, 47, 38, 31, 22, 35, 42, 19, 26], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![36, 53, 12, 29, 26, 11, 54, 39, 44, 61, 4, 21, 18, 3, 62, 47, 52, 37, 28, 13, 10, 27, 38, 55, 60, 45, 20, 5, 2, 19, 46, 63, 42, 59, 56, 41, 16, 1, 6, 23, 34, 51, 48, 33, 24, 9, 14, 31, 58, 43, 40, 57, 0, 17, 22, 7, 50, 35, 32, 49, 8, 25, 30, 15], ![17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46], ![33, 40, 25, 16, 45, 36, 21, 28, 41, 32, 17, 24, 37, 44, 29, 20, 49, 56, 9, 0, 61, 52, 5, 12, 57, 48, 1, 8, 53, 60, 13, 4, 63, 54, 15, 6, 51, 58, 3, 10, 55, 62, 7, 14, 59, 50, 11, 2, 47, 38, 31, 22, 35, 42, 19, 26, 39, 46, 23, 30, 43, 34, 27, 18], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47], ![52, 37, 28, 13, 10, 27, 38, 55, 60, 45, 20, 5, 2, 19, 46, 63, 36, 53, 12, 29, 26, 11, 54, 39, 44, 61, 4, 21, 18, 3, 62, 47, 58, 43, 40, 57, 0, 17, 22, 7, 50, 35, 32, 49, 8, 25, 30, 15, 42, 59, 56, 41, 16, 1, 6, 23, 34, 51, 48, 33, 24, 9, 14, 31]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (12 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask12

namespace Mask13

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![41, 20, 39, 18, 37, 24, 43, 30, 33, 28, 47, 26, 45, 16, 35, 22, 57, 4, 55, 2, 53, 8, 59, 14, 49, 12, 63, 10, 61, 0, 51, 6, 1, 60, 15, 58, 13, 48, 3, 54, 9, 52, 7, 50, 5, 56, 11, 62, 17, 44, 31, 42, 29, 32, 19, 38, 25, 36, 23, 34, 21, 40, 27, 46], ![3, 42, 57, 0, 23, 62, 45, 20, 11, 34, 49, 8, 31, 54, 37, 28, 19, 58, 41, 16, 7, 46, 61, 4, 27, 50, 33, 24, 15, 38, 53, 12, 51, 26, 9, 48, 39, 14, 29, 36, 59, 18, 1, 56, 47, 6, 21, 44, 35, 10, 25, 32, 55, 30, 13, 52, 43, 2, 17, 40, 63, 22, 5, 60], ![32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![33, 28, 47, 26, 45, 16, 35, 22, 41, 20, 39, 18, 37, 24, 43, 30, 49, 12, 63, 10, 61, 0, 51, 6, 57, 4, 55, 2, 53, 8, 59, 14, 9, 52, 7, 50, 5, 56, 11, 62, 1, 60, 15, 58, 13, 48, 3, 54, 25, 36, 23, 34, 21, 40, 27, 46, 17, 44, 31, 42, 29, 32, 19, 38], ![19, 58, 41, 16, 7, 46, 61, 4, 27, 50, 33, 24, 15, 38, 53, 12, 3, 42, 57, 0, 23, 62, 45, 20, 11, 34, 49, 8, 31, 54, 37, 28, 35, 10, 25, 32, 55, 30, 13, 52, 43, 2, 17, 40, 63, 22, 5, 60, 51, 26, 9, 48, 39, 14, 29, 36, 59, 18, 1, 56, 47, 6, 21, 44], ![32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (13 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask13

namespace Mask14

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![55, 46, 33, 56, 1, 24, 19, 10, 63, 38, 41, 48, 9, 16, 27, 2, 39, 62, 49, 40, 17, 8, 3, 26, 47, 54, 57, 32, 25, 0, 11, 18, 53, 44, 21, 12, 7, 30, 35, 58, 61, 36, 29, 4, 15, 22, 43, 50, 37, 60, 5, 28, 23, 14, 51, 42, 45, 52, 13, 20, 31, 6, 59, 34], ![61, 52, 1, 8, 49, 56, 13, 4, 53, 60, 9, 0, 57, 48, 5, 12, 45, 36, 17, 24, 33, 40, 29, 20, 37, 44, 25, 16, 41, 32, 21, 28, 47, 38, 27, 18, 35, 42, 23, 30, 39, 46, 19, 26, 43, 34, 31, 22, 63, 54, 11, 2, 51, 58, 7, 14, 55, 62, 3, 10, 59, 50, 15, 6], ![9, 8, 11, 10, 13, 12, 15, 14, 1, 0, 3, 2, 5, 4, 7, 6, 25, 24, 27, 26, 29, 28, 31, 30, 17, 16, 19, 18, 21, 20, 23, 22, 41, 40, 43, 42, 45, 44, 47, 46, 33, 32, 35, 34, 37, 36, 39, 38, 57, 56, 59, 58, 61, 60, 63, 62, 49, 48, 51, 50, 53, 52, 55, 54], ![50, 51, 52, 53, 54, 55, 48, 49, 58, 59, 60, 61, 62, 63, 56, 57, 34, 35, 36, 37, 38, 39, 32, 33, 42, 43, 44, 45, 46, 47, 40, 41, 22, 23, 16, 17, 18, 19, 20, 21, 30, 31, 24, 25, 26, 27, 28, 29, 6, 7, 0, 1, 2, 3, 4, 5, 14, 15, 8, 9, 10, 11, 12, 13], ![13, 20, 31, 6, 59, 34, 45, 52, 5, 28, 23, 14, 51, 42, 37, 60, 29, 4, 15, 22, 43, 50, 61, 36, 21, 12, 7, 30, 35, 58, 53, 44, 11, 18, 47, 54, 57, 32, 25, 0, 3, 26, 39, 62, 49, 40, 17, 8, 27, 2, 63, 38, 41, 48, 9, 16, 19, 10, 55, 46, 33, 56, 1, 24], ![11, 2, 51, 58, 7, 14, 63, 54, 3, 10, 59, 50, 15, 6, 55, 62, 27, 18, 35, 42, 23, 30, 47, 38, 19, 26, 43, 34, 31, 22, 39, 46, 29, 20, 45, 36, 17, 24, 33, 40, 21, 28, 37, 44, 25, 16, 41, 32, 13, 4, 61, 52, 1, 8, 49, 56, 5, 12, 53, 60, 9, 0, 57, 48]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (14 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask14

namespace Mask15

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![33, 20, 39, 26, 45, 24, 43, 22, 41, 28, 47, 18, 37, 16, 35, 30, 49, 4, 55, 10, 61, 8, 59, 6, 57, 12, 63, 2, 53, 0, 51, 14, 9, 60, 15, 50, 5, 48, 3, 62, 1, 52, 7, 58, 13, 56, 11, 54, 25, 44, 31, 34, 21, 32, 19, 46, 17, 36, 23, 42, 29, 40, 27, 38], ![3, 58, 41, 0, 23, 46, 61, 20, 11, 50, 33, 8, 31, 38, 53, 28, 19, 42, 57, 16, 7, 62, 45, 4, 27, 34, 49, 24, 15, 54, 37, 12, 51, 10, 25, 48, 39, 30, 13, 36, 59, 2, 17, 56, 47, 22, 5, 44, 35, 26, 9, 32, 55, 14, 29, 52, 43, 18, 1, 40, 63, 6, 21, 60], ![32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![41, 28, 47, 18, 37, 16, 35, 30, 33, 20, 39, 26, 45, 24, 43, 22, 57, 12, 63, 2, 53, 0, 51, 14, 49, 4, 55, 10, 61, 8, 59, 6, 1, 52, 7, 58, 13, 56, 11, 54, 9, 60, 15, 50, 5, 48, 3, 62, 17, 36, 23, 42, 29, 40, 27, 38, 25, 44, 31, 34, 21, 32, 19, 46], ![19, 42, 57, 16, 7, 62, 45, 4, 27, 34, 49, 24, 15, 54, 37, 12, 3, 58, 41, 0, 23, 46, 61, 20, 11, 50, 33, 8, 31, 38, 53, 28, 35, 26, 9, 32, 55, 14, 29, 52, 43, 18, 1, 40, 63, 6, 21, 60, 51, 10, 25, 48, 39, 30, 13, 36, 59, 2, 17, 56, 47, 22, 5, 44], ![32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (15 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask15

public theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ m : Fin 16,
      (branches (fun k => m.val.testBit k.val)).Separation gen
        (fun k => m.val.testBit k.val) (pivot (fun k => m.val.testBit k.val)) := by
    intro m
    fin_cases m
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact Mask8.not_mem
    · exact Mask9.not_mem
    · exact Mask10.not_mem
    · exact Mask11.not_mem
    · exact Mask12.not_mem
    · exact Mask13.not_mem
    · exact Mask14.not_mem
    · exact Mask15.not_mem
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 96) :
    Classified H := classify separation_checked H hH

end Node96

namespace Node99

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![11, 18, 9, 16, 15, 22, 13, 20, 55, 46, 53, 44, 51, 42, 49, 40, 47, 54, 45, 52, 43, 50, 41, 48, 19, 10, 17, 8, 23, 14, 21, 12, 31, 6, 29, 4, 27, 2, 25, 0, 35, 58, 33, 56, 39, 62, 37, 60, 59, 34, 57, 32, 63, 38, 61, 36, 7, 30, 5, 28, 3, 26, 1, 24], ![50, 43, 48, 41, 54, 47, 52, 45, 10, 19, 8, 17, 14, 23, 12, 21, 18, 11, 16, 9, 22, 15, 20, 13, 42, 51, 40, 49, 46, 55, 44, 53, 34, 59, 32, 57, 38, 63, 36, 61, 26, 3, 24, 1, 30, 7, 28, 5, 2, 27, 0, 25, 6, 31, 4, 29, 58, 35, 56, 33, 62, 39, 60, 37], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![11, 18, 9, 16, 15, 22, 13, 20, 55, 46, 53, 44, 51, 42, 49, 40, 47, 54, 45, 52, 43, 50, 41, 48, 19, 10, 17, 8, 23, 14, 21, 12, 31, 6, 29, 4, 27, 2, 25, 0, 35, 58, 33, 56, 39, 62, 37, 60, 59, 34, 57, 32, 63, 38, 61, 36, 7, 30, 5, 28, 3, 26, 1, 24], ![50, 43, 48, 41, 54, 47, 52, 45, 10, 19, 8, 17, 14, 23, 12, 21, 18, 11, 16, 9, 22, 15, 20, 13, 42, 51, 40, 49, 46, 55, 44, 53, 34, 59, 32, 57, 38, 63, 36, 61, 26, 3, 24, 1, 30, 7, 28, 5, 2, 27, 0, 25, 6, 31, 4, 29, 58, 35, 56, 33, 62, 39, 60, 37], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (8 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![11, 62, 9, 60, 15, 58, 13, 56, 27, 46, 25, 44, 31, 42, 29, 40, 3, 54, 1, 52, 7, 50, 5, 48, 19, 38, 17, 36, 23, 34, 21, 32, 51, 6, 49, 4, 55, 2, 53, 0, 35, 22, 33, 20, 39, 18, 37, 16, 59, 14, 57, 12, 63, 10, 61, 8, 43, 30, 41, 28, 47, 26, 45, 24], ![50, 3, 48, 1, 54, 7, 52, 5, 34, 19, 32, 17, 38, 23, 36, 21, 58, 11, 56, 9, 62, 15, 60, 13, 42, 27, 40, 25, 46, 31, 44, 29, 10, 59, 8, 57, 14, 63, 12, 61, 26, 43, 24, 41, 30, 47, 28, 45, 2, 51, 0, 49, 6, 55, 4, 53, 18, 35, 16, 33, 22, 39, 20, 37], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39, 56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![19, 38, 17, 36, 23, 34, 21, 32, 3, 54, 1, 52, 7, 50, 5, 48, 27, 46, 25, 44, 31, 42, 29, 40, 11, 62, 9, 60, 15, 58, 13, 56, 43, 30, 41, 28, 47, 26, 45, 24, 59, 14, 57, 12, 63, 10, 61, 8, 35, 22, 33, 20, 39, 18, 37, 16, 51, 6, 49, 4, 55, 2, 53, 0], ![42, 27, 40, 25, 46, 31, 44, 29, 58, 11, 56, 9, 62, 15, 60, 13, 34, 19, 32, 17, 38, 23, 36, 21, 50, 3, 48, 1, 54, 7, 52, 5, 18, 35, 16, 33, 22, 39, 20, 37, 2, 51, 0, 49, 6, 55, 4, 53, 26, 43, 24, 41, 30, 47, 28, 45, 10, 59, 8, 57, 14, 63, 12, 61], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39, 56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (9 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

namespace Mask10

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![52, 37, 6, 23, 48, 33, 2, 19, 60, 45, 14, 31, 56, 41, 10, 27, 36, 53, 22, 7, 32, 49, 18, 3, 44, 61, 30, 15, 40, 57, 26, 11, 20, 5, 38, 55, 16, 1, 34, 51, 28, 13, 46, 63, 24, 9, 42, 59, 4, 21, 54, 39, 0, 17, 50, 35, 12, 29, 62, 47, 8, 25, 58, 43], ![47, 62, 21, 4, 43, 58, 17, 0, 39, 54, 29, 12, 35, 50, 25, 8, 63, 46, 5, 20, 59, 42, 1, 16, 55, 38, 13, 28, 51, 34, 9, 24, 15, 30, 53, 36, 11, 26, 49, 32, 7, 22, 61, 44, 3, 18, 57, 40, 31, 14, 37, 52, 27, 10, 33, 48, 23, 6, 45, 60, 19, 2, 41, 56], ![17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46], ![40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39, 56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![20, 5, 38, 55, 16, 1, 34, 51, 28, 13, 46, 63, 24, 9, 42, 59, 4, 21, 54, 39, 0, 17, 50, 35, 12, 29, 62, 47, 8, 25, 58, 43, 52, 37, 6, 23, 48, 33, 2, 19, 60, 45, 14, 31, 56, 41, 10, 27, 36, 53, 22, 7, 32, 49, 18, 3, 44, 61, 30, 15, 40, 57, 26, 11], ![7, 22, 61, 44, 3, 18, 57, 40, 15, 30, 53, 36, 11, 26, 49, 32, 23, 6, 45, 60, 19, 2, 41, 56, 31, 14, 37, 52, 27, 10, 33, 48, 39, 54, 29, 12, 35, 50, 25, 8, 47, 62, 21, 4, 43, 58, 17, 0, 55, 38, 13, 28, 51, 34, 9, 24, 63, 46, 5, 20, 59, 42, 1, 16]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (10 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask10

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![19, 62, 17, 60, 23, 58, 21, 56, 3, 46, 1, 44, 7, 42, 5, 40, 27, 54, 25, 52, 31, 50, 29, 48, 11, 38, 9, 36, 15, 34, 13, 32, 43, 6, 41, 4, 47, 2, 45, 0, 59, 22, 57, 20, 63, 18, 61, 16, 35, 14, 33, 12, 39, 10, 37, 8, 51, 30, 49, 28, 55, 26, 53, 24], ![50, 27, 48, 25, 54, 31, 52, 29, 34, 11, 32, 9, 38, 15, 36, 13, 58, 19, 56, 17, 62, 23, 60, 21, 42, 3, 40, 1, 46, 7, 44, 5, 10, 35, 8, 33, 14, 39, 12, 37, 26, 51, 24, 49, 30, 55, 28, 53, 2, 43, 0, 41, 6, 47, 4, 45, 18, 59, 16, 57, 22, 63, 20, 61], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39, 56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![11, 38, 9, 36, 15, 34, 13, 32, 27, 54, 25, 52, 31, 50, 29, 48, 3, 46, 1, 44, 7, 42, 5, 40, 19, 62, 17, 60, 23, 58, 21, 56, 51, 30, 49, 28, 55, 26, 53, 24, 35, 14, 33, 12, 39, 10, 37, 8, 59, 22, 57, 20, 63, 18, 61, 16, 43, 6, 41, 4, 47, 2, 45, 0], ![42, 3, 40, 1, 46, 7, 44, 5, 58, 19, 56, 17, 62, 23, 60, 21, 34, 11, 32, 9, 38, 15, 36, 13, 50, 27, 48, 25, 54, 31, 52, 29, 18, 59, 16, 57, 22, 63, 20, 61, 2, 43, 0, 41, 6, 47, 4, 45, 26, 51, 24, 49, 30, 55, 28, 53, 10, 35, 8, 33, 14, 39, 12, 37], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39, 56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (11 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask11

namespace Mask12

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![11, 18, 61, 36, 15, 22, 57, 32, 3, 26, 53, 44, 7, 30, 49, 40, 27, 2, 45, 52, 31, 6, 41, 48, 19, 10, 37, 60, 23, 14, 33, 56, 43, 50, 29, 4, 47, 54, 25, 0, 35, 58, 21, 12, 39, 62, 17, 8, 59, 34, 13, 20, 63, 38, 9, 16, 51, 42, 5, 28, 55, 46, 1, 24], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![56, 33, 10, 19, 60, 37, 14, 23, 48, 41, 2, 27, 52, 45, 6, 31, 40, 49, 26, 3, 44, 53, 30, 7, 32, 57, 18, 11, 36, 61, 22, 15, 24, 1, 42, 51, 28, 5, 46, 55, 16, 9, 34, 59, 20, 13, 38, 63, 8, 17, 58, 35, 12, 21, 62, 39, 0, 25, 50, 43, 4, 29, 54, 47], ![25, 24, 27, 26, 29, 28, 31, 30, 17, 16, 19, 18, 21, 20, 23, 22, 9, 8, 11, 10, 13, 12, 15, 14, 1, 0, 3, 2, 5, 4, 7, 6, 57, 56, 59, 58, 61, 60, 63, 62, 49, 48, 51, 50, 53, 52, 55, 54, 41, 40, 43, 42, 45, 44, 47, 46, 33, 32, 35, 34, 37, 36, 39, 38], ![35, 58, 21, 12, 39, 62, 17, 8, 43, 50, 29, 4, 47, 54, 25, 0, 51, 42, 5, 28, 55, 46, 1, 24, 59, 34, 13, 20, 63, 38, 9, 16, 3, 26, 53, 44, 7, 30, 49, 40, 11, 18, 61, 36, 15, 22, 57, 32, 19, 10, 37, 60, 23, 14, 33, 56, 27, 2, 45, 52, 31, 6, 41, 48], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![56, 33, 10, 19, 60, 37, 14, 23, 48, 41, 2, 27, 52, 45, 6, 31, 40, 49, 26, 3, 44, 53, 30, 7, 32, 57, 18, 11, 36, 61, 22, 15, 24, 1, 42, 51, 28, 5, 46, 55, 16, 9, 34, 59, 20, 13, 38, 63, 8, 17, 58, 35, 12, 21, 62, 39, 0, 25, 50, 43, 4, 29, 54, 47]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (12 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask12

namespace Mask13

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![11, 38, 17, 60, 15, 34, 21, 56, 27, 54, 1, 44, 31, 50, 5, 40, 3, 46, 25, 52, 7, 42, 29, 48, 19, 62, 9, 36, 23, 58, 13, 32, 51, 30, 41, 4, 55, 26, 45, 0, 35, 14, 57, 20, 39, 10, 61, 16, 59, 22, 33, 12, 63, 18, 37, 8, 43, 6, 49, 28, 47, 2, 53, 24], ![42, 3, 48, 25, 46, 7, 52, 29, 58, 19, 32, 9, 62, 23, 36, 13, 34, 11, 56, 17, 38, 15, 60, 21, 50, 27, 40, 1, 54, 31, 44, 5, 18, 59, 8, 33, 22, 63, 12, 37, 2, 43, 24, 49, 6, 47, 28, 53, 26, 51, 0, 41, 30, 55, 4, 45, 10, 35, 16, 57, 14, 39, 20, 61], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39, 56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![19, 62, 9, 36, 23, 58, 13, 32, 3, 46, 25, 52, 7, 42, 29, 48, 27, 54, 1, 44, 31, 50, 5, 40, 11, 38, 17, 60, 15, 34, 21, 56, 43, 6, 49, 28, 47, 2, 53, 24, 59, 22, 33, 12, 63, 18, 37, 8, 35, 14, 57, 20, 39, 10, 61, 16, 51, 30, 41, 4, 55, 26, 45, 0], ![50, 27, 40, 1, 54, 31, 44, 5, 34, 11, 56, 17, 38, 15, 60, 21, 58, 19, 32, 9, 62, 23, 36, 13, 42, 3, 48, 25, 46, 7, 52, 29, 10, 35, 16, 57, 14, 39, 20, 61, 26, 51, 0, 41, 30, 55, 4, 45, 2, 43, 24, 49, 6, 47, 28, 53, 18, 59, 8, 33, 22, 63, 12, 37], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39, 56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (13 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask13

namespace Mask14

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![61, 60, 59, 58, 57, 56, 63, 62, 49, 48, 55, 54, 53, 52, 51, 50, 41, 40, 47, 46, 45, 44, 43, 42, 37, 36, 35, 34, 33, 32, 39, 38, 25, 24, 31, 30, 29, 28, 27, 26, 21, 20, 19, 18, 17, 16, 23, 22, 13, 12, 11, 10, 9, 8, 15, 14, 1, 0, 7, 6, 5, 4, 3, 2], ![47, 54, 25, 0, 43, 50, 29, 4, 19, 10, 37, 60, 23, 14, 33, 56, 11, 18, 61, 36, 15, 22, 57, 32, 55, 46, 1, 24, 51, 42, 5, 28, 59, 34, 13, 20, 63, 38, 9, 16, 7, 30, 49, 40, 3, 26, 53, 44, 31, 6, 41, 48, 27, 2, 45, 52, 35, 58, 21, 12, 39, 62, 17, 8], ![25, 24, 27, 26, 29, 28, 31, 30, 17, 16, 19, 18, 21, 20, 23, 22, 9, 8, 11, 10, 13, 12, 15, 14, 1, 0, 3, 2, 5, 4, 7, 6, 57, 56, 59, 58, 61, 60, 63, 62, 49, 48, 51, 50, 53, 52, 55, 54, 41, 40, 43, 42, 45, 44, 47, 46, 33, 32, 35, 34, 37, 36, 39, 38], ![44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35, 60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19], ![57, 56, 63, 62, 61, 60, 59, 58, 53, 52, 51, 50, 49, 48, 55, 54, 45, 44, 43, 42, 41, 40, 47, 46, 33, 32, 39, 38, 37, 36, 35, 34, 29, 28, 27, 26, 25, 24, 31, 30, 17, 16, 23, 22, 21, 20, 19, 18, 9, 8, 15, 14, 13, 12, 11, 10, 5, 4, 3, 2, 1, 0, 7, 6], ![3, 26, 53, 44, 7, 30, 49, 40, 63, 38, 9, 16, 59, 34, 13, 20, 39, 62, 17, 8, 35, 58, 21, 12, 27, 2, 45, 52, 31, 6, 41, 48, 23, 14, 33, 56, 19, 10, 37, 60, 43, 50, 29, 4, 47, 54, 25, 0, 51, 42, 5, 28, 55, 46, 1, 24, 15, 22, 57, 32, 11, 18, 61, 36]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (14 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask14

namespace Mask15

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![19, 38, 9, 60, 23, 34, 13, 56, 3, 54, 25, 44, 7, 50, 29, 40, 27, 46, 1, 52, 31, 42, 5, 48, 11, 62, 17, 36, 15, 58, 21, 32, 43, 30, 49, 4, 47, 26, 53, 0, 59, 14, 33, 20, 63, 10, 37, 16, 35, 22, 57, 12, 39, 18, 61, 8, 51, 6, 41, 28, 55, 2, 45, 24], ![42, 27, 48, 1, 46, 31, 52, 5, 58, 11, 32, 17, 62, 15, 36, 21, 34, 19, 56, 9, 38, 23, 60, 13, 50, 3, 40, 25, 54, 7, 44, 29, 18, 35, 8, 57, 22, 39, 12, 61, 2, 51, 24, 41, 6, 55, 28, 45, 26, 43, 0, 49, 30, 47, 4, 53, 10, 59, 16, 33, 14, 63, 20, 37], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39, 56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![11, 62, 17, 36, 15, 58, 21, 32, 27, 46, 1, 52, 31, 42, 5, 48, 3, 54, 25, 44, 7, 50, 29, 40, 19, 38, 9, 60, 23, 34, 13, 56, 51, 6, 41, 28, 55, 2, 45, 24, 35, 22, 57, 12, 39, 18, 61, 8, 59, 14, 33, 20, 63, 10, 37, 16, 43, 30, 49, 4, 47, 26, 53, 0], ![50, 3, 40, 25, 54, 7, 44, 29, 34, 19, 56, 9, 38, 23, 60, 13, 58, 11, 32, 17, 62, 15, 36, 21, 42, 27, 48, 1, 46, 31, 52, 5, 10, 59, 16, 33, 14, 63, 20, 37, 26, 43, 0, 49, 30, 47, 4, 53, 2, 51, 24, 41, 6, 55, 28, 45, 18, 35, 8, 57, 22, 39, 12, 61], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39, 56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (15 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask15

public theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ m : Fin 16,
      (branches (fun k => m.val.testBit k.val)).Separation gen
        (fun k => m.val.testBit k.val) (pivot (fun k => m.val.testBit k.val)) := by
    intro m
    fin_cases m
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact Mask8.not_mem
    · exact Mask9.not_mem
    · exact Mask10.not_mem
    · exact Mask11.not_mem
    · exact Mask12.not_mem
    · exact Mask13.not_mem
    · exact Mask14.not_mem
    · exact Mask15.not_mem
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 99) :
    Classified H := classify separation_checked H hH

end Node99

end ReeTwo.SylowModel.SmallEvenMaximalLower
