module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerWordsL
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperCoordinates

/-!+# Nonmembership certificates for lower even maximal subgroups, batch L

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

namespace Node275

namespace Mask3

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, 0)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 2 → Fin 2 :=
  ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![1, 0], ![0, 1]]
private def witness : E := (⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (3 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 168 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask3

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3], ![1, 0, 3, 2], ![3, 2, 1, 0]]
private def witness : E := (⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (5 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 5 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 168 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1]]
private def witness : E := (⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (7 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 5 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 168 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

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
    · exact Mask3.not_mem
    · trivial
    · exact Mask5.not_mem
    · trivial
    · exact Mask7.not_mem
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 275) :
    Classified H := classify separation_checked H hH

end Node275

namespace Node276

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![9, 8, 15, 14, 13, 12, 11, 10, 1, 0, 7, 6, 5, 4, 3, 2, 29, 28, 27, 26, 25, 24, 31, 30, 21, 20, 19, 18, 17, 16, 23, 22], ![14, 7, 30, 23, 10, 3, 26, 19, 6, 15, 22, 31, 2, 11, 18, 27, 12, 5, 28, 21, 8, 1, 24, 17, 4, 13, 20, 29, 0, 9, 16, 25], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![9, 8, 15, 14, 13, 12, 11, 10, 1, 0, 7, 6, 5, 4, 3, 2, 29, 28, 27, 26, 25, 24, 31, 30, 21, 20, 19, 18, 17, 16, 23, 22], ![14, 7, 30, 23, 10, 3, 26, 19, 6, 15, 22, 31, 2, 11, 18, 27, 12, 5, 28, 21, 8, 1, 24, 17, 4, 13, 20, 29, 0, 9, 16, 25], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (4 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask5

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![15, 20, 5, 30, 11, 16, 1, 26, 7, 28, 13, 22, 3, 24, 9, 18, 23, 12, 29, 6, 19, 8, 25, 2, 31, 4, 21, 14, 27, 0, 17, 10], ![28, 25, 30, 27, 24, 29, 26, 31, 20, 17, 22, 19, 16, 21, 18, 23, 12, 9, 14, 11, 8, 13, 10, 15, 4, 1, 6, 3, 0, 5, 2, 7], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![3, 24, 9, 18, 7, 28, 13, 22, 11, 16, 1, 26, 15, 20, 5, 30, 27, 0, 17, 10, 31, 4, 21, 14, 19, 8, 25, 2, 23, 12, 29, 6], ![28, 25, 30, 27, 24, 29, 26, 31, 20, 17, 22, 19, 16, 21, 18, 23, 12, 9, 14, 11, 8, 13, 10, 15, 4, 1, 6, 3, 0, 5, 2, 7], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (5 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask6

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![9, 8, 15, 14, 13, 12, 11, 10, 1, 0, 7, 6, 5, 4, 3, 2, 25, 24, 31, 30, 29, 28, 27, 26, 17, 16, 23, 22, 21, 20, 19, 18], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![10, 3, 24, 17, 14, 7, 28, 21, 2, 11, 16, 25, 6, 15, 20, 29, 26, 19, 8, 1, 30, 23, 12, 5, 18, 27, 0, 9, 22, 31, 4, 13], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![5, 4, 3, 2, 1, 0, 7, 6, 13, 12, 11, 10, 9, 8, 15, 14, 21, 20, 19, 18, 17, 16, 23, 22, 29, 28, 27, 26, 25, 24, 31, 30], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![26, 19, 8, 1, 30, 23, 12, 5, 18, 27, 0, 9, 22, 31, 4, 13, 10, 3, 24, 17, 14, 7, 28, 21, 2, 11, 16, 25, 6, 15, 20, 29], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (6 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

namespace Mask7

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![15, 24, 5, 18, 11, 28, 1, 22, 7, 16, 13, 26, 3, 20, 9, 30, 23, 0, 29, 10, 19, 4, 25, 14, 31, 8, 21, 2, 27, 12, 17, 6], ![28, 25, 30, 27, 24, 29, 26, 31, 20, 17, 22, 19, 16, 21, 18, 23, 12, 9, 14, 11, 8, 13, 10, 15, 4, 1, 6, 3, 0, 5, 2, 7], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![3, 20, 9, 30, 7, 16, 13, 26, 11, 28, 1, 22, 15, 24, 5, 18, 27, 12, 17, 6, 31, 8, 21, 2, 19, 4, 25, 14, 23, 0, 29, 10], ![28, 25, 30, 27, 24, 29, 26, 31, 20, 17, 22, 19, 16, 21, 18, 23, 12, 9, 14, 11, 8, 13, 10, 15, 4, 1, 6, 3, 0, 5, 2, 7], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (7 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![8, 11, 15, 14, 12, 10, 9, 13, 0, 6, 5, 1, 4, 7, 3, 2, 24, 30, 29, 25, 28, 31, 27, 26, 16, 19, 23, 22, 20, 18, 17, 21], ![14, 6, 31, 21, 3, 24, 16, 9, 15, 20, 28, 5, 2, 10, 19, 25, 23, 12, 4, 29, 26, 18, 11, 1, 22, 30, 7, 13, 27, 0, 8, 17], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![8, 11, 15, 14, 12, 10, 9, 13, 0, 6, 5, 1, 4, 7, 3, 2, 24, 30, 29, 25, 28, 31, 27, 26, 16, 19, 23, 22, 20, 18, 17, 21], ![14, 6, 31, 21, 3, 24, 16, 9, 15, 20, 28, 5, 2, 10, 19, 25, 23, 12, 4, 29, 26, 18, 11, 1, 22, 30, 7, 13, 27, 0, 8, 17], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![15, 7, 21, 29, 24, 8, 2, 18, 20, 4, 14, 30, 3, 11, 25, 17, 12, 28, 22, 6, 27, 19, 1, 9, 23, 31, 13, 5, 0, 16, 26, 10], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![1, 0, 4, 7, 2, 6, 5, 3, 14, 10, 9, 15, 13, 12, 8, 11, 22, 18, 17, 23, 21, 20, 16, 19, 25, 24, 28, 31, 26, 30, 29, 27], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![3, 11, 25, 17, 20, 4, 14, 30, 24, 8, 2, 18, 15, 7, 21, 29, 0, 16, 26, 10, 23, 31, 13, 5, 27, 19, 1, 9, 12, 28, 22, 6], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![1, 0, 4, 7, 2, 6, 5, 3, 14, 10, 9, 15, 13, 12, 8, 11, 22, 18, 17, 23, 21, 20, 16, 19, 25, 24, 28, 31, 26, 30, 29, 27]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

namespace Mask10

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![8, 14, 13, 9, 12, 15, 11, 10, 0, 3, 7, 6, 4, 2, 1, 5, 24, 27, 31, 30, 28, 26, 25, 29, 16, 22, 21, 17, 20, 23, 19, 18], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![21, 5, 15, 31, 26, 18, 0, 8, 22, 30, 12, 4, 25, 9, 3, 19, 14, 6, 20, 28, 1, 17, 27, 11, 13, 29, 23, 7, 2, 10, 24, 16], ![4, 2, 1, 5, 0, 3, 7, 6, 12, 15, 11, 10, 8, 14, 13, 9, 20, 23, 19, 18, 16, 22, 21, 17, 28, 26, 25, 29, 24, 27, 31, 30], ![17, 18, 19, 16, 23, 20, 21, 22, 27, 24, 25, 26, 29, 30, 31, 28, 3, 0, 1, 2, 5, 6, 7, 4, 9, 10, 11, 8, 15, 12, 13, 14], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![6, 20, 28, 14, 11, 1, 17, 27, 7, 13, 29, 23, 10, 24, 16, 2, 31, 21, 5, 15, 18, 0, 8, 26, 30, 12, 4, 22, 19, 25, 9, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask10

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![15, 7, 25, 17, 20, 8, 2, 30, 24, 4, 14, 18, 3, 11, 21, 29, 0, 28, 22, 10, 27, 19, 13, 5, 23, 31, 1, 9, 12, 16, 26, 6], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![1, 0, 4, 7, 2, 6, 5, 3, 14, 10, 9, 15, 13, 12, 8, 11, 22, 18, 17, 23, 21, 20, 16, 19, 25, 24, 28, 31, 26, 30, 29, 27], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![3, 11, 21, 29, 24, 4, 14, 18, 20, 8, 2, 30, 15, 7, 25, 17, 12, 16, 26, 6, 23, 31, 1, 9, 27, 19, 13, 5, 0, 28, 22, 10], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![1, 0, 4, 7, 2, 6, 5, 3, 14, 10, 9, 15, 13, 12, 8, 11, 22, 18, 17, 23, 21, 20, 16, 19, 25, 24, 28, 31, 26, 30, 29, 27]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask11

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
    · exact Mask4.not_mem
    · exact Mask5.not_mem
    · exact Mask6.not_mem
    · exact Mask7.not_mem
    · exact Mask8.not_mem
    · exact Mask9.not_mem
    · exact Mask10.not_mem
    · exact Mask11.not_mem
    · trivial
    · trivial
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 276) :
    Classified H := classify separation_checked H hH

end Node276

namespace Node278

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 :=
  ![![1, 0], ![0, 1], ![0, 1], ![1, 0], ![0, 1], ![0, 1]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 1)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 :=
  ![![0, 1], ![0, 1], ![1, 0], ![0, 1], ![0, 1], ![1, 0]]
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

namespace Mask6

private def generators : Fin 6 → E :=
  ![(⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 :=
  ![![1, 0], ![0, 1], ![0, 1], ![1, 0], ![0, 1], ![0, 1]]
private def witness : E := (⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (6 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 184 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 1), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 1), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 1)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 :=
  ![![0, 1], ![1, 0], ![1, 0], ![0, 1], ![1, 0], ![1, 0]]
private def witness : E := (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (7 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 56 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

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
    · exact Mask6.not_mem
    · exact Mask7.not_mem
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 278) :
    Classified H := classify separation_checked H hH

end Node278

namespace Node280

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (4 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 6 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 152 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 0, 0, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 0, 1, 2, 3], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 0, 1, 2, 3], ![3, 2, 1, 0, 7, 6, 5, 4]]
private def witness : E := (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (5 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 6 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 104 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask6

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 0, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 1, 1, 0⟩, 1)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 2, 3, 0, 1]]
private def witness : E := (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (6 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 6 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 24 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, 1), (⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 1, 0, 3, 2], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 1, 0, 3, 2], ![3, 2, 1, 0, 7, 6, 5, 4]]
private def witness : E := (⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (7 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 6 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 232 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

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
    · exact Mask6.not_mem
    · exact Mask7.not_mem
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 280) :
    Classified H := classify separation_checked H hH

end Node280

namespace Node282

namespace Mask3

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 :=
  ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![1, 0], ![0, 1]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (3 : Nat).testBit k.val

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

end Mask3

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (5 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 6 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 136 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (7 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 6 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 136 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

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
    · exact Mask3.not_mem
    · trivial
    · exact Mask5.not_mem
    · trivial
    · exact Mask7.not_mem
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 282) :
    Classified H := classify separation_checked H hH

end Node282

namespace Node283

namespace Mask3

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 :=
  ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![1, 0], ![0, 1]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (3 : Nat).testBit k.val

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

end Mask3

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 0, 1⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6]]
private def witness : E := (⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (5 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 6 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 184 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 1⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6]]
private def witness : E := (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (7 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 6 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 56 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

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
    · exact Mask3.not_mem
    · trivial
    · exact Mask5.not_mem
    · trivial
    · exact Mask7.not_mem
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 283) :
    Classified H := classify separation_checked H hH

end Node283

namespace Node284

namespace Mask2

private def generators : Fin 4 → E :=
  ![(⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 4 → Fin 8 → Fin 8 :=
  ![![6, 7, 4, 5, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 1, 0, 3, 2], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 2 → Bool := fun k => (2 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 7 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask2

namespace Mask3

private def generators : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 1)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 4 → Fin 2 → Fin 2 :=
  ![![0, 1], ![1, 0], ![0, 1], ![1, 0]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 2 → Bool := fun k => (3 : Nat).testBit k.val

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

end Mask3

public theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ m : Fin 4,
      (branches (fun k => m.val.testBit k.val)).Separation gen
        (fun k => m.val.testBit k.val) (pivot (fun k => m.val.testBit k.val)) := by
    intro m
    fin_cases m
    · trivial
    · trivial
    · exact Mask2.not_mem
    · exact Mask3.not_mem
  have hs : ∀ (σ : Fin 2 → Bool),
      σ = fun k => (signatureIndex σ % 4).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 284) :
    Classified H := classify separation_checked H hH

end Node284

namespace Node285

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![21, 16, 9, 12, 17, 20, 13, 8, 29, 24, 1, 4, 25, 28, 5, 0, 27, 30, 7, 2, 31, 26, 3, 6, 19, 22, 15, 10, 23, 18, 11, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![21, 16, 9, 12, 17, 20, 13, 8, 29, 24, 1, 4, 25, 28, 5, 0, 27, 30, 7, 2, 31, 26, 3, 6, 19, 22, 15, 10, 23, 18, 11, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (4 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask5

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![21, 10, 19, 12, 17, 14, 23, 8, 29, 2, 27, 4, 25, 6, 31, 0, 1, 30, 7, 24, 5, 26, 3, 28, 9, 22, 15, 16, 13, 18, 11, 20], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![17, 14, 23, 8, 21, 10, 19, 12, 25, 6, 31, 0, 29, 2, 27, 4, 5, 26, 3, 28, 1, 30, 7, 24, 13, 18, 11, 20, 9, 22, 15, 16], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (5 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask6

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![31, 26, 1, 4, 27, 30, 5, 0, 23, 18, 9, 12, 19, 22, 13, 8, 15, 10, 17, 20, 11, 14, 21, 16, 7, 2, 25, 28, 3, 6, 29, 24], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 29, 28, 31, 30, 25, 24, 27, 26], ![24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![7, 2, 25, 28, 3, 6, 29, 24, 15, 10, 17, 20, 11, 14, 21, 16, 23, 18, 9, 12, 19, 22, 13, 8, 31, 26, 1, 4, 27, 30, 5, 0], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (6 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

namespace Mask7

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![17, 10, 23, 12, 21, 14, 19, 8, 25, 2, 31, 4, 29, 6, 27, 0, 5, 30, 3, 24, 1, 26, 7, 28, 13, 22, 11, 16, 9, 18, 15, 20], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![21, 14, 19, 8, 17, 10, 23, 12, 29, 6, 27, 0, 25, 2, 31, 4, 1, 26, 7, 28, 5, 30, 3, 24, 9, 18, 15, 20, 13, 22, 11, 16], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (7 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![7, 2, 9, 12, 3, 6, 13, 8, 15, 10, 1, 4, 11, 14, 5, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![7, 2, 9, 12, 3, 6, 13, 8, 15, 10, 1, 4, 11, 14, 5, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![5, 14, 3, 8, 1, 10, 7, 12, 9, 2, 15, 4, 13, 6, 11, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 10, 7, 12, 5, 14, 3, 8, 13, 6, 11, 0, 9, 2, 15, 4], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

namespace Mask10

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![7, 2, 11, 14, 3, 6, 15, 10, 1, 4, 13, 8, 5, 0, 9, 12], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![13, 8, 1, 4, 9, 12, 5, 0, 11, 14, 7, 2, 15, 10, 3, 6]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask10

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 14, 7, 8, 5, 10, 3, 12, 13, 2, 11, 4, 9, 6, 15, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![5, 10, 3, 12, 1, 14, 7, 8, 9, 6, 15, 0, 13, 2, 11, 4], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask11

namespace Mask12

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![21, 16, 23, 18, 17, 20, 19, 22, 3, 6, 1, 4, 7, 2, 5, 0, 27, 30, 25, 28, 31, 26, 29, 24, 13, 8, 15, 10, 9, 12, 11, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![21, 16, 23, 18, 17, 20, 19, 22, 3, 6, 1, 4, 7, 2, 5, 0, 27, 30, 25, 28, 31, 26, 29, 24, 13, 8, 15, 10, 9, 12, 11, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![21, 10, 23, 8, 17, 14, 19, 12, 25, 6, 27, 4, 29, 2, 31, 0, 1, 30, 3, 28, 5, 26, 7, 24, 13, 18, 15, 16, 9, 22, 11, 20], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![17, 14, 19, 12, 21, 10, 23, 8, 29, 2, 31, 0, 25, 6, 27, 4, 5, 26, 7, 24, 1, 30, 3, 28, 9, 22, 11, 20, 13, 18, 15, 16], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 192 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask13

namespace Mask14

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![31, 22, 1, 8, 27, 18, 5, 12, 23, 30, 9, 0, 19, 26, 13, 4, 15, 6, 17, 24, 11, 2, 21, 28, 7, 14, 25, 16, 3, 10, 29, 20], ![15, 6, 17, 24, 11, 2, 21, 28, 7, 14, 25, 16, 3, 10, 29, 20, 31, 22, 1, 8, 27, 18, 5, 12, 23, 30, 9, 0, 19, 26, 13, 4], ![9, 8, 11, 10, 13, 12, 15, 14, 1, 0, 3, 2, 5, 4, 7, 6, 25, 24, 27, 26, 29, 28, 31, 30, 17, 16, 19, 18, 21, 20, 23, 22], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![11, 2, 21, 28, 15, 6, 17, 24, 3, 10, 29, 20, 7, 14, 25, 16, 27, 18, 5, 12, 31, 22, 1, 8, 19, 26, 13, 4, 23, 30, 9, 0], ![27, 18, 5, 12, 31, 22, 1, 8, 19, 26, 13, 4, 23, 30, 9, 0, 11, 2, 21, 28, 15, 6, 17, 24, 3, 10, 29, 20, 7, 14, 25, 16]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![17, 10, 19, 8, 21, 14, 23, 12, 29, 6, 31, 4, 25, 2, 27, 0, 5, 30, 7, 28, 1, 26, 3, 24, 9, 18, 11, 16, 13, 22, 15, 20], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![21, 14, 23, 12, 17, 10, 19, 8, 25, 2, 27, 0, 29, 6, 31, 4, 1, 26, 3, 24, 5, 30, 7, 28, 13, 22, 15, 20, 9, 18, 11, 16], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 192 ∉
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
    · exact Mask4.not_mem
    · exact Mask5.not_mem
    · exact Mask6.not_mem
    · exact Mask7.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 285) :
    Classified H := classify separation_checked H hH

end Node285

namespace Node286

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![7, 10, 29, 16, 3, 14, 25, 20, 15, 2, 21, 24, 11, 6, 17, 28, 23, 26, 13, 0, 19, 30, 9, 4, 31, 18, 5, 8, 27, 22, 1, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![7, 10, 29, 16, 3, 14, 25, 20, 15, 2, 21, 24, 11, 6, 17, 28, 23, 26, 13, 0, 19, 30, 9, 4, 31, 18, 5, 8, 27, 22, 1, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (4 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 160 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask5

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![5, 18, 11, 28, 1, 22, 15, 24, 13, 26, 3, 20, 9, 30, 7, 16, 25, 14, 23, 0, 29, 10, 19, 4, 17, 6, 31, 8, 21, 2, 27, 12], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![9, 30, 7, 16, 13, 26, 3, 20, 1, 22, 15, 24, 5, 18, 11, 28, 21, 2, 27, 12, 17, 6, 31, 8, 29, 10, 19, 4, 25, 14, 23, 0], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (5 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 160 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask6

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![3, 14, 27, 22, 7, 10, 31, 18, 11, 6, 19, 30, 15, 2, 23, 26, 9, 4, 17, 28, 13, 0, 21, 24, 1, 12, 25, 20, 5, 8, 29, 16], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2, 29, 28, 31, 30, 25, 24, 27, 26, 21, 20, 23, 22, 17, 16, 19, 18], ![22, 23, 20, 21, 18, 19, 16, 17, 30, 31, 28, 29, 26, 27, 24, 25, 6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![21, 24, 13, 0, 17, 28, 9, 4, 29, 16, 5, 8, 25, 20, 1, 12, 31, 18, 7, 10, 27, 22, 3, 14, 23, 26, 15, 2, 19, 30, 11, 6], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (6 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 160 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

namespace Mask7

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![9, 18, 7, 28, 13, 22, 3, 24, 1, 26, 15, 20, 5, 30, 11, 16, 21, 14, 27, 0, 17, 10, 31, 4, 29, 6, 19, 8, 25, 2, 23, 12], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![5, 30, 11, 16, 1, 26, 15, 20, 13, 22, 3, 24, 9, 18, 7, 28, 25, 2, 23, 12, 29, 6, 19, 8, 17, 10, 31, 4, 21, 14, 27, 0], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (7 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 160 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![5, 8, 13, 0, 11, 6, 3, 14, 7, 10, 15, 2, 9, 4, 1, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![5, 8, 13, 0, 11, 6, 3, 14, 7, 10, 15, 2, 9, 4, 1, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![5, 14, 11, 0, 13, 6, 3, 8, 1, 10, 15, 4, 9, 2, 7, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![9, 2, 7, 12, 1, 10, 15, 4, 13, 6, 3, 8, 5, 14, 11, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11]]
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
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![7, 10, 13, 0, 3, 14, 9, 4, 15, 2, 5, 8, 11, 6, 1, 12], ![13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![3, 14, 9, 4, 7, 10, 13, 0, 11, 6, 1, 12, 15, 2, 5, 8]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![9, 14, 7, 0, 1, 6, 15, 8, 13, 10, 3, 4, 5, 2, 11, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![5, 2, 11, 12, 13, 10, 3, 4, 1, 6, 15, 8, 9, 14, 7, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11]]
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
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![5, 8, 7, 10, 27, 22, 25, 20, 23, 26, 21, 24, 9, 4, 11, 6, 15, 2, 13, 0, 17, 28, 19, 30, 29, 16, 31, 18, 3, 14, 1, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![5, 8, 7, 10, 27, 22, 25, 20, 23, 26, 21, 24, 9, 4, 11, 6, 15, 2, 13, 0, 17, 28, 19, 30, 29, 16, 31, 18, 3, 14, 1, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![5, 30, 7, 28, 13, 22, 15, 20, 1, 26, 3, 24, 9, 18, 11, 16, 25, 2, 27, 0, 17, 10, 19, 8, 29, 6, 31, 4, 21, 14, 23, 12], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![9, 18, 11, 16, 1, 26, 3, 24, 13, 22, 15, 20, 5, 30, 7, 28, 21, 14, 23, 12, 29, 6, 31, 4, 17, 10, 19, 8, 25, 2, 27, 0], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27]]
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
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 1⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![7, 14, 25, 16, 3, 10, 29, 20, 15, 6, 17, 24, 11, 2, 21, 28, 23, 30, 9, 0, 19, 26, 13, 4, 31, 22, 1, 8, 27, 18, 5, 12], ![23, 30, 9, 0, 19, 26, 13, 4, 31, 22, 1, 8, 27, 18, 5, 12, 7, 14, 25, 16, 3, 10, 29, 20, 15, 6, 17, 24, 11, 2, 21, 28], ![9, 8, 11, 10, 13, 12, 15, 14, 1, 0, 3, 2, 5, 4, 7, 6, 25, 24, 27, 26, 29, 28, 31, 30, 17, 16, 19, 18, 21, 20, 23, 22], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![19, 26, 13, 4, 23, 30, 9, 0, 27, 18, 5, 12, 31, 22, 1, 8, 3, 10, 29, 20, 7, 14, 25, 16, 11, 2, 21, 28, 15, 6, 17, 24], ![3, 10, 29, 20, 7, 14, 25, 16, 11, 2, 21, 28, 15, 6, 17, 24, 19, 26, 13, 4, 23, 30, 9, 0, 27, 18, 5, 12, 31, 22, 1, 8]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![9, 30, 11, 28, 1, 22, 3, 20, 13, 26, 15, 24, 5, 18, 7, 16, 21, 2, 23, 0, 29, 10, 31, 8, 17, 6, 19, 4, 25, 14, 27, 12], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![5, 18, 7, 16, 13, 26, 15, 24, 1, 22, 3, 20, 9, 30, 11, 28, 25, 14, 27, 12, 17, 6, 19, 4, 29, 10, 31, 8, 21, 2, 23, 0], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27]]
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
    · exact Mask4.not_mem
    · exact Mask5.not_mem
    · exact Mask6.not_mem
    · exact Mask7.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 286) :
    Classified H := classify separation_checked H hH

end Node286

namespace Node287

namespace Mask4

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![10, 20, 8, 22, 14, 16, 12, 18, 2, 28, 0, 30, 6, 24, 4, 26, 5, 27, 7, 25, 1, 31, 3, 29, 13, 19, 15, 17, 9, 23, 11, 21], ![20, 19, 9, 12, 16, 23, 13, 8, 28, 27, 1, 4, 24, 31, 5, 0, 29, 7, 2, 26, 25, 3, 6, 30, 21, 15, 10, 18, 17, 11, 14, 22], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![10, 20, 8, 22, 14, 16, 12, 18, 2, 28, 0, 30, 6, 24, 4, 26, 5, 27, 7, 25, 1, 31, 3, 29, 13, 19, 15, 17, 9, 23, 11, 21], ![20, 19, 9, 12, 16, 23, 13, 8, 28, 27, 1, 4, 24, 31, 5, 0, 29, 7, 2, 26, 25, 3, 6, 30, 21, 15, 10, 18, 17, 11, 14, 22], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (4 : Nat).testBit k.val

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

end Mask4

namespace Mask5

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![20, 12, 18, 10, 16, 8, 22, 14, 28, 4, 26, 2, 24, 0, 30, 6, 31, 3, 25, 5, 27, 7, 29, 1, 23, 11, 17, 13, 19, 15, 21, 9], ![26, 6, 5, 27, 30, 2, 1, 31, 18, 14, 13, 19, 22, 10, 9, 23, 21, 20, 8, 11, 17, 16, 12, 15, 29, 28, 0, 3, 25, 24, 4, 7], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![20, 12, 18, 10, 16, 8, 22, 14, 28, 4, 26, 2, 24, 0, 30, 6, 31, 3, 25, 5, 27, 7, 29, 1, 23, 11, 17, 13, 19, 15, 21, 9], ![26, 6, 5, 27, 30, 2, 1, 31, 18, 14, 13, 19, 22, 10, 9, 23, 21, 20, 8, 11, 17, 16, 12, 15, 29, 28, 0, 3, 25, 24, 4, 7], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (5 : Nat).testBit k.val

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

end Mask5

namespace Mask6

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![10, 20, 8, 22, 14, 16, 12, 18, 2, 28, 0, 30, 6, 24, 4, 26, 5, 27, 7, 25, 1, 31, 3, 29, 13, 19, 15, 17, 9, 23, 11, 21], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![30, 4, 3, 27, 26, 0, 7, 31, 22, 12, 11, 19, 18, 8, 15, 23, 10, 13, 21, 16, 14, 9, 17, 20, 2, 5, 29, 24, 6, 1, 25, 28], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![10, 20, 8, 22, 14, 16, 12, 18, 2, 28, 0, 30, 6, 24, 4, 26, 5, 27, 7, 25, 1, 31, 3, 29, 13, 19, 15, 17, 9, 23, 11, 21], ![25, 26, 27, 24, 29, 30, 31, 28, 17, 18, 19, 16, 21, 22, 23, 20, 11, 8, 9, 10, 15, 12, 13, 14, 3, 0, 1, 2, 7, 4, 5, 6], ![5, 29, 24, 2, 1, 25, 28, 6, 13, 21, 16, 10, 9, 17, 20, 14, 19, 22, 12, 11, 23, 18, 8, 15, 27, 30, 4, 3, 31, 26, 0, 7], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (6 : Nat).testBit k.val

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

end Mask6

namespace Mask7

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![2, 7, 25, 30, 6, 3, 29, 26, 10, 15, 17, 22, 14, 11, 21, 18, 13, 19, 20, 8, 9, 23, 16, 12, 5, 27, 28, 0, 1, 31, 24, 4], ![24, 6, 5, 25, 28, 2, 1, 29, 16, 14, 13, 17, 20, 10, 9, 21, 8, 11, 23, 22, 12, 15, 19, 18, 0, 3, 31, 30, 4, 7, 27, 26], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![2, 7, 25, 30, 6, 3, 29, 26, 10, 15, 17, 22, 14, 11, 21, 18, 13, 19, 20, 8, 9, 23, 16, 12, 5, 27, 28, 0, 1, 31, 24, 4], ![24, 6, 5, 25, 28, 2, 1, 29, 16, 14, 13, 17, 20, 10, 9, 21, 8, 11, 23, 22, 12, 15, 19, 18, 0, 3, 31, 30, 4, 7, 27, 26], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (7 : Nat).testBit k.val

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

end Mask7

namespace Mask8

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 8 → Fin 8 :=
  ![![2, 6, 0, 5, 7, 3, 1, 4], ![6, 5, 1, 7, 2, 4, 3, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 6, 0, 5, 7, 3, 1, 4], ![6, 5, 1, 7, 2, 4, 3, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (8 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 7 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask9

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![2, 5, 1, 7, 3, 0, 4, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 7, 3, 2, 0, 6, 5, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 5, 1, 7, 3, 0, 4, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 7, 3, 2, 0, 6, 5, 1], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (9 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 7 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

namespace Mask10

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 8 → Fin 8 :=
  ![![2, 6, 0, 5, 7, 3, 1, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 0, 7, 1, 3, 6, 2, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 6, 0, 5, 7, 3, 1, 4], ![3, 4, 5, 0, 1, 2, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 3, 6, 4, 0, 7, 5, 2], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (10 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 7 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask10

namespace Mask11

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![2, 7, 3, 5, 6, 0, 1, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 2, 1, 7, 5, 4, 0, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 7, 3, 5, 6, 0, 1, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 2, 1, 7, 5, 4, 0, 3], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (11 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 7 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask11

namespace Mask20

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![9, 20, 11, 22, 13, 16, 15, 18, 29, 0, 31, 2, 25, 4, 27, 6, 5, 24, 7, 26, 1, 28, 3, 30, 17, 12, 19, 14, 21, 8, 23, 10], ![20, 19, 22, 17, 16, 23, 18, 21, 6, 1, 4, 3, 2, 5, 0, 7, 30, 25, 28, 27, 26, 29, 24, 31, 12, 11, 14, 9, 8, 15, 10, 13], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![9, 20, 11, 22, 13, 16, 15, 18, 29, 0, 31, 2, 25, 4, 27, 6, 5, 24, 7, 26, 1, 28, 3, 30, 17, 12, 19, 14, 21, 8, 23, 10], ![20, 19, 22, 17, 16, 23, 18, 21, 6, 1, 4, 3, 2, 5, 0, 7, 30, 25, 28, 27, 26, 29, 24, 31, 12, 11, 14, 9, 8, 15, 10, 13], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (20 : Nat).testBit k.val

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

end Mask20

namespace Mask21

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![20, 9, 22, 11, 16, 13, 18, 15, 6, 27, 4, 25, 2, 31, 0, 29, 30, 3, 28, 1, 26, 7, 24, 5, 12, 17, 14, 19, 8, 21, 10, 23], ![25, 24, 27, 26, 29, 28, 31, 30, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![1, 0, 3, 2, 5, 4, 7, 6, 21, 20, 23, 22, 17, 16, 19, 18, 13, 12, 15, 14, 9, 8, 11, 10, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![20, 9, 22, 11, 16, 13, 18, 15, 6, 27, 4, 25, 2, 31, 0, 29, 30, 3, 28, 1, 26, 7, 24, 5, 12, 17, 14, 19, 8, 21, 10, 23], ![25, 24, 27, 26, 29, 28, 31, 30, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![1, 0, 3, 2, 5, 4, 7, 6, 21, 20, 23, 22, 17, 16, 19, 18, 13, 12, 15, 14, 9, 8, 11, 10, 25, 24, 27, 26, 29, 28, 31, 30]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (21 : Nat).testBit k.val

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

end Mask21

namespace Mask22

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![9, 20, 11, 22, 13, 16, 15, 18, 29, 0, 31, 2, 25, 4, 27, 6, 5, 24, 7, 26, 1, 28, 3, 30, 17, 12, 19, 14, 21, 8, 23, 10], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![31, 4, 29, 6, 27, 0, 25, 2, 17, 10, 19, 8, 21, 14, 23, 12, 9, 18, 11, 16, 13, 22, 15, 20, 7, 28, 5, 30, 3, 24, 1, 26], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![7, 28, 5, 30, 3, 24, 1, 26, 9, 18, 11, 16, 13, 22, 15, 20, 17, 10, 19, 8, 21, 14, 23, 12, 31, 4, 29, 6, 27, 0, 25, 2], ![9, 20, 11, 22, 13, 16, 15, 18, 29, 0, 31, 2, 25, 4, 27, 6, 5, 24, 7, 26, 1, 28, 3, 30, 17, 12, 19, 14, 21, 8, 23, 10], ![26, 27, 24, 25, 30, 31, 28, 29, 18, 19, 16, 17, 22, 23, 20, 21, 10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5], ![5, 30, 7, 28, 1, 26, 3, 24, 11, 16, 9, 18, 15, 20, 13, 22, 19, 8, 17, 10, 23, 12, 21, 14, 29, 6, 31, 4, 25, 2, 27, 0], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![29, 6, 31, 4, 25, 2, 27, 0, 19, 8, 17, 10, 23, 12, 21, 14, 11, 16, 9, 18, 15, 20, 13, 22, 5, 30, 7, 28, 1, 26, 3, 24]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (22 : Nat).testBit k.val

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

end Mask22

namespace Mask23

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![2, 15, 20, 25, 6, 11, 16, 29, 10, 7, 28, 17, 14, 3, 24, 21, 18, 31, 4, 9, 22, 27, 0, 13, 26, 23, 12, 1, 30, 19, 8, 5], ![19, 10, 9, 16, 23, 14, 13, 20, 27, 2, 1, 24, 31, 6, 5, 28, 3, 26, 25, 0, 7, 30, 29, 4, 11, 18, 17, 8, 15, 22, 21, 12], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![3, 26, 25, 0, 7, 30, 29, 4, 11, 18, 17, 8, 15, 22, 21, 12, 19, 10, 9, 16, 23, 14, 13, 20, 27, 2, 1, 24, 31, 6, 5, 28], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![2, 15, 20, 25, 6, 11, 16, 29, 10, 7, 28, 17, 14, 3, 24, 21, 18, 31, 4, 9, 22, 27, 0, 13, 26, 23, 12, 1, 30, 19, 8, 5], ![19, 10, 9, 16, 23, 14, 13, 20, 27, 2, 1, 24, 31, 6, 5, 28, 3, 26, 25, 0, 7, 30, 29, 4, 11, 18, 17, 8, 15, 22, 21, 12], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![3, 26, 25, 0, 7, 30, 29, 4, 11, 18, 17, 8, 15, 22, 21, 12, 19, 10, 9, 16, 23, 14, 13, 20, 27, 2, 1, 24, 31, 6, 5, 28]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (23 : Nat).testBit k.val

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

end Mask23

namespace Mask24

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![9, 4, 7, 10, 1, 12, 15, 2, 13, 0, 3, 14, 5, 8, 11, 6], ![4, 3, 12, 11, 10, 13, 2, 5, 6, 1, 14, 9, 8, 15, 0, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![9, 4, 7, 10, 1, 12, 15, 2, 13, 0, 3, 14, 5, 8, 11, 6], ![4, 3, 12, 11, 10, 13, 2, 5, 6, 1, 14, 9, 8, 15, 0, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (24 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask24

namespace Mask25

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 9, 12, 1, 10, 7, 2, 15, 6, 11, 14, 3, 8, 5, 0, 13], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![13, 12, 3, 2, 5, 4, 11, 10, 9, 8, 7, 6, 1, 0, 15, 14], ![1, 0, 15, 14, 9, 8, 7, 6, 5, 4, 11, 10, 13, 12, 3, 2], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 9, 12, 1, 10, 7, 2, 15, 6, 11, 14, 3, 8, 5, 0, 13], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![13, 12, 3, 2, 5, 4, 11, 10, 9, 8, 7, 6, 1, 0, 15, 14], ![1, 0, 15, 14, 9, 8, 7, 6, 5, 4, 11, 10, 13, 12, 3, 2]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (25 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask25

namespace Mask26

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![9, 4, 7, 10, 1, 12, 15, 2, 13, 0, 3, 14, 5, 8, 11, 6], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![11, 0, 15, 4, 9, 2, 13, 6, 5, 14, 1, 10, 7, 12, 3, 8], ![7, 12, 3, 8, 5, 14, 1, 10, 9, 2, 13, 6, 11, 0, 15, 4], ![9, 4, 7, 10, 1, 12, 15, 2, 13, 0, 3, 14, 5, 8, 11, 6], ![10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 10, 5, 14, 3, 8, 7, 12, 15, 4, 11, 0, 13, 6, 9, 2], ![13, 6, 9, 2, 15, 4, 11, 0, 3, 8, 7, 12, 1, 10, 5, 14]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (26 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask26

namespace Mask27

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![2, 7, 8, 13, 6, 3, 12, 9, 10, 15, 0, 5, 14, 11, 4, 1], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![15, 2, 1, 12, 11, 6, 5, 8, 7, 10, 9, 4, 3, 14, 13, 0], ![3, 14, 13, 0, 7, 10, 9, 4, 11, 6, 5, 8, 15, 2, 1, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![2, 7, 8, 13, 6, 3, 12, 9, 10, 15, 0, 5, 14, 11, 4, 1], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![15, 2, 1, 12, 11, 6, 5, 8, 7, 10, 9, 4, 3, 14, 13, 0], ![3, 14, 13, 0, 7, 10, 9, 4, 11, 6, 5, 8, 15, 2, 1, 12]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (27 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 224 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask27

public theorem separation_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ m : Fin 32,
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
    · exact Mask6.not_mem
    · exact Mask7.not_mem
    · exact Mask8.not_mem
    · exact Mask9.not_mem
    · exact Mask10.not_mem
    · exact Mask11.not_mem
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact Mask20.not_mem
    · exact Mask21.not_mem
    · exact Mask22.not_mem
    · exact Mask23.not_mem
    · exact Mask24.not_mem
    · exact Mask25.not_mem
    · exact Mask26.not_mem
    · exact Mask27.not_mem
    · trivial
    · trivial
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 5 → Bool),
      σ = fun k => (signatureIndex σ % 32).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 287) :
    Classified H := classify separation_checked H hH

end Node287

namespace Node288

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![10, 28, 8, 30, 14, 24, 12, 26, 2, 20, 0, 22, 6, 16, 4, 18, 13, 27, 15, 25, 9, 31, 11, 29, 5, 19, 7, 17, 1, 23, 3, 21], ![5, 17, 24, 14, 1, 21, 28, 10, 13, 25, 16, 6, 9, 29, 20, 2, 31, 22, 0, 11, 27, 18, 4, 15, 23, 30, 8, 3, 19, 26, 12, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![25, 26, 27, 24, 29, 30, 31, 28, 17, 18, 19, 16, 21, 22, 23, 20, 11, 8, 9, 10, 15, 12, 13, 14, 3, 0, 1, 2, 7, 4, 5, 6], ![10, 28, 8, 30, 14, 24, 12, 26, 2, 20, 0, 22, 6, 16, 4, 18, 13, 27, 15, 25, 9, 31, 11, 29, 5, 19, 7, 17, 1, 23, 3, 21], ![5, 17, 24, 14, 1, 21, 28, 10, 13, 25, 16, 6, 9, 29, 20, 2, 31, 22, 0, 11, 27, 18, 4, 15, 23, 30, 8, 3, 19, 26, 12, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![25, 26, 27, 24, 29, 30, 31, 28, 17, 18, 19, 16, 21, 22, 23, 20, 11, 8, 9, 10, 15, 12, 13, 14, 3, 0, 1, 2, 7, 4, 5, 6]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (4 : Nat).testBit k.val

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

end Mask4

namespace Mask5

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![6, 15, 17, 26, 2, 11, 21, 30, 14, 7, 25, 18, 10, 3, 29, 22, 9, 23, 28, 0, 13, 19, 24, 4, 1, 31, 20, 8, 5, 27, 16, 12], ![24, 14, 13, 25, 28, 10, 9, 29, 16, 6, 5, 17, 20, 2, 1, 21, 8, 11, 31, 30, 12, 15, 27, 26, 0, 3, 23, 22, 4, 7, 19, 18], ![25, 26, 27, 24, 29, 30, 31, 28, 17, 18, 19, 16, 21, 22, 23, 20, 11, 8, 9, 10, 15, 12, 13, 14, 3, 0, 1, 2, 7, 4, 5, 6], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![14, 7, 25, 18, 10, 3, 29, 22, 6, 15, 17, 26, 2, 11, 21, 30, 1, 31, 20, 8, 5, 27, 16, 12, 9, 23, 28, 0, 13, 19, 24, 4], ![24, 14, 13, 25, 28, 10, 9, 29, 16, 6, 5, 17, 20, 2, 1, 21, 8, 11, 31, 30, 12, 15, 27, 26, 0, 3, 23, 22, 4, 7, 19, 18], ![25, 26, 27, 24, 29, 30, 31, 28, 17, 18, 19, 16, 21, 22, 23, 20, 11, 8, 9, 10, 15, 12, 13, 14, 3, 0, 1, 2, 7, 4, 5, 6]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (5 : Nat).testBit k.val

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

end Mask5

namespace Mask6

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![10, 28, 8, 30, 14, 24, 12, 26, 2, 20, 0, 22, 6, 16, 4, 18, 13, 27, 15, 25, 9, 31, 11, 29, 5, 19, 7, 17, 1, 23, 3, 21], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![3, 10, 30, 21, 7, 14, 26, 17, 11, 2, 22, 29, 15, 6, 18, 25, 4, 16, 27, 13, 0, 20, 31, 9, 12, 24, 19, 5, 8, 28, 23, 1], ![25, 26, 27, 24, 29, 30, 31, 28, 17, 18, 19, 16, 21, 22, 23, 20, 11, 8, 9, 10, 15, 12, 13, 14, 3, 0, 1, 2, 7, 4, 5, 6], ![2, 20, 0, 22, 6, 16, 4, 18, 10, 28, 8, 30, 14, 24, 12, 26, 5, 19, 7, 17, 1, 23, 3, 21, 13, 27, 15, 25, 9, 31, 11, 29], ![21, 22, 23, 20, 17, 18, 19, 16, 29, 30, 31, 28, 25, 26, 27, 24, 7, 4, 5, 6, 3, 0, 1, 2, 15, 12, 13, 14, 11, 8, 9, 10], ![20, 31, 9, 0, 16, 27, 13, 4, 28, 23, 1, 8, 24, 19, 5, 12, 17, 7, 14, 26, 21, 3, 10, 30, 25, 15, 6, 18, 29, 11, 2, 22], ![25, 26, 27, 24, 29, 30, 31, 28, 17, 18, 19, 16, 21, 22, 23, 20, 11, 8, 9, 10, 15, 12, 13, 14, 3, 0, 1, 2, 7, 4, 5, 6]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (6 : Nat).testBit k.val

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

end Mask6

namespace Mask7

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![16, 12, 18, 14, 20, 8, 22, 10, 24, 4, 26, 6, 28, 0, 30, 2, 31, 3, 29, 1, 27, 7, 25, 5, 23, 11, 21, 9, 19, 15, 17, 13], ![26, 14, 13, 27, 30, 10, 9, 31, 18, 6, 5, 19, 22, 2, 1, 23, 29, 28, 8, 11, 25, 24, 12, 15, 21, 20, 0, 3, 17, 16, 4, 7], ![27, 24, 25, 26, 31, 28, 29, 30, 19, 16, 17, 18, 23, 20, 21, 22, 9, 10, 11, 8, 13, 14, 15, 12, 1, 2, 3, 0, 5, 6, 7, 4], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![24, 4, 26, 6, 28, 0, 30, 2, 16, 12, 18, 14, 20, 8, 22, 10, 23, 11, 21, 9, 19, 15, 17, 13, 31, 3, 29, 1, 27, 7, 25, 5], ![26, 14, 13, 27, 30, 10, 9, 31, 18, 6, 5, 19, 22, 2, 1, 23, 29, 28, 8, 11, 25, 24, 12, 15, 21, 20, 0, 3, 17, 16, 4, 7], ![27, 24, 25, 26, 31, 28, 29, 30, 19, 16, 17, 18, 23, 20, 21, 22, 9, 10, 11, 8, 13, 14, 15, 12, 1, 2, 3, 0, 5, 6, 7, 4]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (7 : Nat).testBit k.val

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

end Mask7

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 4, 0, 6, 1, 7, 3, 5], ![4, 7, 1, 0, 5, 3, 2, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 4, 0, 6, 1, 7, 3, 5], ![4, 7, 1, 0, 5, 3, 2, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (8 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 7 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 288 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![5, 6, 0, 1, 3, 7, 4, 2], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 5, 4, 0, 2, 1, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![5, 6, 0, 1, 3, 7, 4, 2], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 5, 4, 0, 2, 1, 7, 6]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (9 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 7 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 288 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

namespace Mask10

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 4, 0, 6, 1, 7, 3, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 5, 4, 2, 7, 6, 0, 3], ![2, 4, 0, 6, 1, 7, 3, 5], ![5, 6, 7, 4, 3, 0, 1, 2], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 0, 3, 7, 2, 1, 5, 4]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (10 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 7 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 288 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask10

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 5, 3, 7, 2, 6, 0, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 7, 6, 0, 5, 4, 2, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 5, 3, 7, 2, 6, 0, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 7, 6, 0, 5, 4, 2, 1]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (11 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 7 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 288 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask11

namespace Mask12

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![9, 8, 11, 10, 25, 24, 27, 26, 1, 0, 3, 2, 17, 16, 19, 18, 13, 12, 15, 14, 29, 28, 31, 30, 5, 4, 7, 6, 21, 20, 23, 22], ![5, 24, 7, 26, 11, 22, 9, 20, 13, 16, 15, 18, 3, 30, 1, 28, 31, 2, 29, 0, 17, 12, 19, 14, 23, 10, 21, 8, 25, 4, 27, 6], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5, 26, 27, 24, 25, 30, 31, 28, 29, 18, 19, 16, 17, 22, 23, 20, 21], ![9, 8, 11, 10, 25, 24, 27, 26, 1, 0, 3, 2, 17, 16, 19, 18, 13, 12, 15, 14, 29, 28, 31, 30, 5, 4, 7, 6, 21, 20, 23, 22], ![5, 24, 7, 26, 11, 22, 9, 20, 13, 16, 15, 18, 3, 30, 1, 28, 31, 2, 29, 0, 17, 12, 19, 14, 23, 10, 21, 8, 25, 4, 27, 6], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5, 26, 27, 24, 25, 30, 31, 28, 29, 18, 19, 16, 17, 22, 23, 20, 21]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![4, 15, 6, 13, 22, 29, 20, 31, 12, 7, 14, 5, 30, 21, 28, 23, 2, 9, 0, 11, 16, 27, 18, 25, 10, 1, 8, 3, 24, 19, 26, 17], ![25, 12, 27, 14, 9, 28, 11, 30, 17, 4, 19, 6, 1, 20, 3, 22, 29, 8, 31, 10, 13, 24, 15, 26, 21, 0, 23, 2, 5, 16, 7, 18], ![19, 6, 17, 4, 3, 22, 1, 20, 27, 14, 25, 12, 11, 30, 9, 28, 23, 2, 21, 0, 7, 18, 5, 16, 31, 10, 29, 8, 15, 26, 13, 24], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![12, 7, 14, 5, 30, 21, 28, 23, 4, 15, 6, 13, 22, 29, 20, 31, 10, 1, 8, 3, 24, 19, 26, 17, 2, 9, 0, 11, 16, 27, 18, 25], ![25, 12, 27, 14, 9, 28, 11, 30, 17, 4, 19, 6, 1, 20, 3, 22, 29, 8, 31, 10, 13, 24, 15, 26, 21, 0, 23, 2, 5, 16, 7, 18], ![19, 6, 17, 4, 3, 22, 1, 20, 27, 14, 25, 12, 11, 30, 9, 28, 23, 2, 21, 0, 7, 18, 5, 16, 31, 10, 29, 8, 15, 26, 13, 24]]
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
  ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 1⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![11, 26, 25, 8, 15, 30, 29, 12, 3, 18, 17, 0, 7, 22, 21, 4, 27, 10, 9, 24, 31, 14, 13, 28, 19, 2, 1, 16, 23, 6, 5, 20], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![6, 11, 16, 29, 2, 15, 20, 25, 14, 3, 24, 21, 10, 7, 28, 17, 22, 27, 0, 13, 18, 31, 4, 9, 30, 19, 8, 5, 26, 23, 12, 1], ![10, 7, 28, 17, 14, 3, 24, 21, 2, 15, 20, 25, 6, 11, 16, 29, 26, 23, 12, 1, 30, 19, 8, 5, 18, 31, 4, 9, 22, 27, 0, 13], ![3, 18, 17, 0, 7, 22, 21, 4, 11, 26, 25, 8, 15, 30, 29, 12, 19, 2, 1, 16, 23, 6, 5, 20, 27, 10, 9, 24, 31, 14, 13, 28], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![18, 31, 4, 9, 22, 27, 0, 13, 26, 23, 12, 1, 30, 19, 8, 5, 2, 15, 20, 25, 6, 11, 16, 29, 10, 7, 28, 17, 14, 3, 24, 21], ![30, 19, 8, 5, 26, 23, 12, 1, 22, 27, 0, 13, 18, 31, 4, 9, 14, 3, 24, 21, 10, 7, 28, 17, 6, 11, 16, 29, 2, 15, 20, 25]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 1⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![16, 19, 18, 17, 10, 9, 8, 11, 24, 27, 26, 25, 2, 1, 0, 3, 30, 29, 28, 31, 4, 7, 6, 5, 22, 21, 20, 23, 12, 15, 14, 13], ![25, 12, 27, 14, 9, 28, 11, 30, 17, 4, 19, 6, 1, 20, 3, 22, 29, 8, 31, 10, 13, 24, 15, 26, 21, 0, 23, 2, 5, 16, 7, 18], ![19, 6, 17, 4, 3, 22, 1, 20, 27, 14, 25, 12, 11, 30, 9, 28, 23, 2, 21, 0, 7, 18, 5, 16, 31, 10, 29, 8, 15, 26, 13, 24], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![24, 27, 26, 25, 2, 1, 0, 3, 16, 19, 18, 17, 10, 9, 8, 11, 22, 21, 20, 23, 12, 15, 14, 13, 30, 29, 28, 31, 4, 7, 6, 5], ![25, 12, 27, 14, 9, 28, 11, 30, 17, 4, 19, 6, 1, 20, 3, 22, 29, 8, 31, 10, 13, 24, 15, 26, 21, 0, 23, 2, 5, 16, 7, 18], ![19, 6, 17, 4, 3, 22, 1, 20, 27, 14, 25, 12, 11, 30, 9, 28, 23, 2, 21, 0, 7, 18, 5, 16, 31, 10, 29, 8, 15, 26, 13, 24]]
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
    · exact Mask4.not_mem
    · exact Mask5.not_mem
    · exact Mask6.not_mem
    · exact Mask7.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 288) :
    Classified H := classify separation_checked H hH

end Node288

namespace Node289

namespace Mask1

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![20, 15, 12, 23, 16, 11, 8, 19, 28, 7, 4, 31, 24, 3, 0, 27, 30, 5, 6, 29, 26, 1, 2, 25, 22, 13, 14, 21, 18, 9, 10, 17], ![25, 28, 31, 26, 29, 24, 27, 30, 17, 20, 23, 18, 21, 16, 19, 22, 13, 8, 11, 14, 9, 12, 15, 10, 5, 0, 3, 6, 1, 4, 7, 2], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![16, 11, 8, 19, 20, 15, 12, 23, 24, 3, 0, 27, 28, 7, 4, 31, 26, 1, 2, 25, 30, 5, 6, 29, 18, 9, 10, 17, 22, 13, 14, 21], ![21, 16, 19, 22, 17, 20, 23, 18, 29, 24, 27, 30, 25, 28, 31, 26, 1, 4, 7, 2, 5, 0, 3, 6, 9, 12, 15, 10, 13, 8, 11, 14]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (1 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 320 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask1

namespace Mask3

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![16, 15, 12, 19, 20, 11, 8, 23, 24, 7, 4, 27, 28, 3, 0, 31, 30, 1, 2, 29, 26, 5, 6, 25, 22, 9, 10, 21, 18, 13, 14, 17], ![25, 16, 19, 26, 29, 20, 23, 30, 17, 24, 27, 18, 21, 28, 31, 22, 1, 8, 11, 2, 5, 12, 15, 6, 9, 0, 3, 10, 13, 4, 7, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![20, 11, 8, 23, 16, 15, 12, 19, 28, 3, 0, 31, 24, 7, 4, 27, 26, 5, 6, 25, 30, 1, 2, 29, 18, 13, 14, 17, 22, 9, 10, 21], ![21, 28, 31, 22, 17, 24, 27, 18, 29, 20, 23, 30, 25, 16, 19, 26, 13, 4, 7, 14, 9, 0, 3, 10, 5, 12, 15, 6, 1, 8, 11, 2]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (3 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 256 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask3

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![21, 16, 9, 12, 17, 20, 13, 8, 29, 24, 1, 4, 25, 28, 5, 0, 27, 30, 7, 2, 31, 26, 3, 6, 19, 22, 15, 10, 23, 18, 11, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2, 29, 28, 31, 30, 25, 24, 27, 26, 21, 20, 23, 22, 17, 16, 19, 18], ![17, 20, 13, 8, 21, 16, 9, 12, 25, 28, 5, 0, 29, 24, 1, 4, 31, 26, 3, 6, 27, 30, 7, 2, 23, 18, 11, 14, 19, 22, 15, 10], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (4 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask6

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![19, 26, 5, 12, 23, 30, 1, 8, 27, 18, 13, 4, 31, 22, 9, 0, 3, 10, 21, 28, 7, 14, 17, 24, 11, 2, 29, 20, 15, 6, 25, 16], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 29, 28, 31, 30, 25, 24, 27, 26], ![24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![15, 6, 25, 16, 11, 2, 29, 20, 7, 14, 17, 24, 3, 10, 21, 28, 31, 22, 9, 0, 27, 18, 13, 4, 23, 30, 1, 8, 19, 26, 5, 12]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (6 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

public theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ m : Fin 8,
      (branches (fun k => m.val.testBit k.val)).Separation gen
        (fun k => m.val.testBit k.val) (pivot (fun k => m.val.testBit k.val)) := by
    intro m
    fin_cases m
    · trivial
    · exact Mask1.not_mem
    · trivial
    · exact Mask3.not_mem
    · exact Mask4.not_mem
    · trivial
    · exact Mask6.not_mem
    · trivial
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 289) :
    Classified H := classify separation_checked H hH

end Node289

namespace Node290

namespace Mask1

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![5, 30, 7, 28, 1, 26, 3, 24, 13, 22, 15, 20, 9, 18, 11, 16, 21, 14, 23, 12, 17, 10, 19, 8, 29, 6, 31, 4, 25, 2, 27, 0], ![24, 29, 26, 31, 28, 25, 30, 27, 16, 21, 18, 23, 20, 17, 22, 19, 8, 13, 10, 15, 12, 9, 14, 11, 0, 5, 2, 7, 4, 1, 6, 3], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![1, 26, 3, 24, 5, 30, 7, 28, 9, 18, 11, 16, 13, 22, 15, 20, 17, 10, 19, 8, 21, 14, 23, 12, 25, 2, 27, 0, 29, 6, 31, 4], ![20, 17, 22, 19, 16, 21, 18, 23, 28, 25, 30, 27, 24, 29, 26, 31, 4, 1, 6, 3, 0, 5, 2, 7, 12, 9, 14, 11, 8, 13, 10, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (1 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 320 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask1

namespace Mask3

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![1, 30, 3, 28, 5, 26, 7, 24, 9, 22, 11, 20, 13, 18, 15, 16, 17, 14, 19, 12, 21, 10, 23, 8, 25, 6, 27, 4, 29, 2, 31, 0], ![24, 17, 26, 19, 28, 21, 30, 23, 16, 25, 18, 27, 20, 29, 22, 31, 8, 1, 10, 3, 12, 5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![5, 26, 7, 24, 1, 30, 3, 28, 13, 18, 15, 16, 9, 22, 11, 20, 21, 10, 23, 8, 17, 14, 19, 12, 29, 2, 31, 0, 25, 6, 27, 4], ![20, 29, 22, 31, 16, 25, 18, 27, 28, 21, 30, 23, 24, 17, 26, 19, 4, 13, 6, 15, 0, 9, 2, 11, 12, 5, 14, 7, 8, 1, 10, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (3 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 256 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask3

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![7, 2, 25, 28, 3, 6, 29, 24, 15, 10, 17, 20, 11, 14, 21, 16, 23, 18, 9, 12, 19, 22, 13, 8, 31, 26, 1, 4, 27, 30, 5, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2, 29, 28, 31, 30, 25, 24, 27, 26, 21, 20, 23, 22, 17, 16, 19, 18], ![3, 6, 29, 24, 7, 2, 25, 28, 11, 14, 21, 16, 15, 10, 17, 20, 19, 22, 13, 8, 23, 18, 9, 12, 27, 30, 5, 0, 31, 26, 1, 4], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (4 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 32 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask6

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![3, 10, 23, 30, 7, 14, 19, 26, 11, 2, 31, 22, 15, 6, 27, 18, 5, 12, 17, 24, 1, 8, 21, 28, 13, 4, 25, 16, 9, 0, 29, 20], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 29, 28, 31, 30, 25, 24, 27, 26], ![26, 27, 24, 25, 30, 31, 28, 29, 18, 19, 16, 17, 22, 23, 20, 21, 10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5], ![29, 20, 9, 0, 25, 16, 13, 4, 21, 28, 1, 8, 17, 24, 5, 12, 27, 18, 15, 6, 31, 22, 11, 2, 19, 26, 7, 14, 23, 30, 3, 10]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (6 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

public theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ m : Fin 8,
      (branches (fun k => m.val.testBit k.val)).Separation gen
        (fun k => m.val.testBit k.val) (pivot (fun k => m.val.testBit k.val)) := by
    intro m
    fin_cases m
    · trivial
    · exact Mask1.not_mem
    · trivial
    · exact Mask3.not_mem
    · exact Mask4.not_mem
    · trivial
    · exact Mask6.not_mem
    · trivial
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 290) :
    Classified H := classify separation_checked H hH

end Node290

namespace Node293

namespace Mask3

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0)]
private def representatives : Fin 1 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 1 → Fin 1 :=
  ![![0], ![0], ![0], ![0], ![0], ![0]]
private def witness : E := (⟨1, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (3 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 1 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 67 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 1 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask3

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3], ![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3]]
private def witness : E := (⟨1, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (4 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 3 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 67 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 3 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![3, 2, 1, 0], ![2, 3, 0, 1], ![0, 1, 2, 3], ![3, 2, 1, 0], ![2, 3, 0, 1]]
private def witness : E := (⟨1, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (5 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 3 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 67 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 3 representatives 0
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
    · exact Mask3.not_mem
    · exact Mask4.not_mem
    · exact Mask5.not_mem
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 293) :
    Classified H := classify separation_checked H hH

end Node293

namespace Node294

namespace Mask3

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 1 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 1 → Fin 1 :=
  ![![0], ![0], ![0], ![0], ![0], ![0]]
private def witness : E := (⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (3 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 1 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 131 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 1 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask3

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3], ![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3]]
private def witness : E := (⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)
private def signature : Fin 3 → Bool := fun k => (4 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 3 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 643 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 3 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![3, 2, 1, 0], ![2, 3, 0, 1], ![0, 1, 2, 3], ![3, 2, 1, 0], ![2, 3, 0, 1]]
private def witness : E := (⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (5 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 3 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 131 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 3 representatives 0
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
    · exact Mask3.not_mem
    · exact Mask4.not_mem
    · exact Mask5.not_mem
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 294) :
    Classified H := classify separation_checked H hH

end Node294

namespace Node295

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 0, 0, 1, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![16, 21, 18, 23, 20, 17, 22, 19, 4, 1, 6, 3, 0, 5, 2, 7, 28, 25, 30, 27, 24, 29, 26, 31, 8, 13, 10, 15, 12, 9, 14, 11], ![21, 18, 23, 16, 17, 22, 19, 20, 1, 6, 3, 4, 5, 2, 7, 0, 25, 30, 27, 28, 29, 26, 31, 24, 13, 10, 15, 8, 9, 14, 11, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![16, 21, 18, 23, 20, 17, 22, 19, 4, 1, 6, 3, 0, 5, 2, 7, 28, 25, 30, 27, 24, 29, 26, 31, 8, 13, 10, 15, 12, 9, 14, 11], ![21, 18, 23, 16, 17, 22, 19, 20, 1, 6, 3, 4, 5, 2, 7, 0, 25, 30, 27, 28, 29, 26, 31, 24, 13, 10, 15, 8, 9, 14, 11, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, 0)
private def signature : Fin 3 → Bool := fun k => (4 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 864 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![21, 8, 23, 10, 17, 12, 19, 14, 27, 6, 25, 4, 31, 2, 29, 0, 3, 30, 1, 28, 7, 26, 5, 24, 13, 16, 15, 18, 9, 20, 11, 22], ![29, 0, 31, 2, 25, 4, 27, 6, 17, 12, 19, 14, 21, 8, 23, 10, 9, 20, 11, 22, 13, 16, 15, 18, 5, 24, 7, 26, 1, 28, 3, 30], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![17, 12, 19, 14, 21, 8, 23, 10, 31, 2, 29, 0, 27, 6, 25, 4, 7, 26, 5, 24, 3, 30, 1, 28, 9, 20, 11, 22, 13, 16, 15, 18], ![1, 28, 3, 30, 5, 24, 7, 26, 13, 16, 15, 18, 9, 20, 11, 22, 21, 8, 23, 10, 17, 12, 19, 14, 25, 4, 27, 6, 29, 0, 31, 2]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, 0)
private def signature : Fin 3 → Bool := fun k => (5 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 864 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask6

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![17, 8, 19, 10, 21, 12, 23, 14, 29, 4, 31, 6, 25, 0, 27, 2, 5, 28, 7, 30, 1, 24, 3, 26, 9, 16, 11, 18, 13, 20, 15, 22], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![31, 4, 29, 6, 27, 0, 25, 2, 17, 10, 19, 8, 21, 14, 23, 12, 9, 18, 11, 16, 13, 22, 15, 20, 7, 28, 5, 30, 3, 24, 1, 26], ![21, 12, 23, 14, 17, 8, 19, 10, 25, 0, 27, 2, 29, 4, 31, 6, 1, 24, 3, 26, 5, 28, 7, 30, 13, 20, 15, 22, 9, 16, 11, 18], ![26, 27, 24, 25, 30, 31, 28, 29, 18, 19, 16, 17, 22, 23, 20, 21, 10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5], ![5, 30, 7, 28, 1, 26, 3, 24, 11, 16, 9, 18, 15, 20, 13, 22, 19, 8, 17, 10, 23, 12, 21, 14, 29, 6, 31, 4, 25, 2, 27, 0]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, 0)
private def signature : Fin 3 → Bool := fun k => (6 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 864 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨1, 0, 1, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![9, 12, 11, 14, 13, 8, 15, 10, 1, 4, 3, 6, 5, 0, 7, 2, 25, 28, 27, 30, 29, 24, 31, 26, 17, 20, 19, 22, 21, 16, 23, 18], ![26, 19, 0, 9, 30, 23, 4, 13, 18, 27, 8, 1, 22, 31, 12, 5, 10, 3, 16, 25, 14, 7, 20, 29, 2, 11, 24, 17, 6, 15, 28, 21], ![24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![25, 28, 27, 30, 29, 24, 31, 26, 17, 20, 19, 22, 21, 16, 23, 18, 9, 12, 11, 14, 13, 8, 15, 10, 1, 4, 3, 6, 5, 0, 7, 2], ![2, 11, 24, 17, 6, 15, 28, 21, 10, 3, 16, 25, 14, 7, 20, 29, 18, 27, 8, 1, 22, 31, 12, 5, 26, 19, 0, 9, 30, 23, 4, 13]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, 0)
private def signature : Fin 3 → Bool := fun k => (7 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 864 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

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
    · exact Mask6.not_mem
    · exact Mask7.not_mem
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 295) :
    Classified H := classify separation_checked H hH

end Node295

namespace Node296

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![25, 20, 27, 22, 5, 8, 7, 10, 9, 4, 11, 6, 21, 24, 23, 26, 17, 28, 19, 30, 13, 0, 15, 2, 1, 12, 3, 14, 29, 16, 31, 18], ![5, 8, 7, 10, 27, 22, 25, 20, 23, 26, 21, 24, 9, 4, 11, 6, 15, 2, 13, 0, 17, 28, 19, 30, 29, 16, 31, 18, 3, 14, 1, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![25, 20, 27, 22, 5, 8, 7, 10, 9, 4, 11, 6, 21, 24, 23, 26, 17, 28, 19, 30, 13, 0, 15, 2, 1, 12, 3, 14, 29, 16, 31, 18], ![5, 8, 7, 10, 27, 22, 25, 20, 23, 26, 21, 24, 9, 4, 11, 6, 15, 2, 13, 0, 17, 28, 19, 30, 29, 16, 31, 18, 3, 14, 1, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (4 : Nat).testBit k.val

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

end Mask4

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![5, 30, 7, 28, 13, 22, 15, 20, 1, 26, 3, 24, 9, 18, 11, 16, 25, 2, 27, 0, 17, 10, 19, 8, 29, 6, 31, 4, 21, 14, 23, 12], ![4, 29, 6, 31, 12, 21, 14, 23, 0, 25, 2, 27, 8, 17, 10, 19, 24, 1, 26, 3, 16, 9, 18, 11, 28, 5, 30, 7, 20, 13, 22, 15], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19], ![29, 6, 31, 4, 21, 14, 23, 12, 25, 2, 27, 0, 17, 10, 19, 8, 1, 26, 3, 24, 9, 18, 11, 16, 5, 30, 7, 28, 13, 22, 15, 20], ![8, 17, 10, 19, 0, 25, 2, 27, 12, 21, 14, 23, 4, 29, 6, 31, 20, 13, 22, 15, 28, 5, 30, 7, 16, 9, 18, 11, 24, 1, 26, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (5 : Nat).testBit k.val

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

end Mask5

namespace Mask6

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![26, 3, 16, 9, 30, 7, 20, 13, 18, 11, 24, 1, 22, 15, 28, 5, 10, 19, 0, 25, 14, 23, 4, 29, 2, 27, 8, 17, 6, 31, 12, 21], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![7, 26, 13, 16, 3, 30, 9, 20, 15, 18, 5, 24, 11, 22, 1, 28, 23, 10, 29, 0, 19, 14, 25, 4, 31, 2, 21, 8, 27, 6, 17, 12], ![2, 27, 8, 17, 6, 31, 12, 21, 10, 19, 0, 25, 14, 23, 4, 29, 18, 11, 24, 1, 22, 15, 28, 5, 26, 3, 16, 9, 30, 7, 20, 13], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![19, 14, 25, 4, 23, 10, 29, 0, 27, 6, 17, 12, 31, 2, 21, 8, 3, 30, 9, 20, 7, 26, 13, 16, 11, 22, 1, 28, 15, 18, 5, 24]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (6 : Nat).testBit k.val

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

end Mask6

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![28, 31, 30, 29, 26, 25, 24, 27, 22, 21, 20, 23, 16, 19, 18, 17, 14, 13, 12, 15, 8, 11, 10, 9, 4, 7, 6, 5, 2, 1, 0, 3], ![5, 16, 7, 18, 25, 12, 27, 14, 21, 0, 23, 2, 9, 28, 11, 30, 13, 24, 15, 26, 17, 4, 19, 6, 29, 8, 31, 10, 1, 20, 3, 22], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19], ![8, 11, 10, 9, 14, 13, 12, 15, 2, 1, 0, 3, 4, 7, 6, 5, 26, 25, 24, 27, 28, 31, 30, 29, 16, 19, 18, 17, 22, 21, 20, 23], ![9, 28, 11, 30, 21, 0, 23, 2, 25, 12, 27, 14, 5, 16, 7, 18, 1, 20, 3, 22, 29, 8, 31, 10, 17, 4, 19, 6, 13, 24, 15, 26]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (7 : Nat).testBit k.val

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

end Mask7

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
    · exact Mask6.not_mem
    · exact Mask7.not_mem
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 296) :
    Classified H := classify separation_checked H hH

end Node296

namespace Node298

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![14, 11, 0, 5, 10, 15, 4, 1, 6, 3, 8, 13, 2, 7, 12, 9], ![15, 14, 1, 0, 11, 10, 5, 4, 7, 6, 9, 8, 3, 2, 13, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![14, 11, 0, 5, 10, 15, 4, 1, 6, 3, 8, 13, 2, 7, 12, 9], ![15, 14, 1, 0, 11, 10, 5, 4, 7, 6, 9, 8, 3, 2, 13, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0)
private def signature : Fin 3 → Bool := fun k => (4 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 928 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![15, 0, 13, 2, 11, 4, 9, 6, 7, 8, 5, 10, 3, 12, 1, 14], ![9, 4, 11, 6, 15, 2, 13, 0, 3, 14, 1, 12, 5, 8, 7, 10], ![14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1], ![13, 2, 15, 0, 9, 6, 11, 4, 5, 10, 7, 8, 1, 14, 3, 12], ![7, 10, 5, 8, 1, 12, 3, 14, 13, 0, 15, 2, 11, 6, 9, 4]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (5 : Nat).testBit k.val

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

end Mask5

namespace Mask6

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![15, 0, 13, 2, 9, 6, 11, 4, 5, 10, 7, 8, 3, 12, 1, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![9, 6, 11, 4, 13, 2, 15, 0, 1, 14, 3, 12, 5, 10, 7, 8], ![13, 2, 15, 0, 11, 4, 9, 6, 7, 8, 5, 10, 1, 14, 3, 12], ![14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1], ![7, 8, 5, 10, 3, 12, 1, 14, 15, 0, 13, 2, 11, 4, 9, 6]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (6 : Nat).testBit k.val

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

end Mask6

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 2, 3, 0, 5, 6, 7, 4, 9, 10, 11, 8, 13, 14, 15, 12], ![8, 11, 10, 9, 2, 1, 0, 3, 14, 13, 12, 15, 4, 7, 6, 5], ![14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1], ![13, 14, 15, 12, 9, 10, 11, 8, 5, 6, 7, 4, 1, 2, 3, 0], ![6, 5, 4, 7, 12, 15, 14, 13, 0, 3, 2, 1, 10, 9, 8, 11]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0)
private def signature : Fin 3 → Bool := fun k => (7 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 928 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

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
    · exact Mask6.not_mem
    · exact Mask7.not_mem
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 298) :
    Classified H := classify separation_checked H hH

end Node298

namespace Node299

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![5, 0, 7, 2, 1, 4, 3, 6], ![6, 3, 0, 5, 2, 7, 4, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![5, 0, 7, 2, 1, 4, 3, 6], ![6, 3, 0, 5, 2, 7, 4, 1], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (4 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 7 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 160 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![7, 0, 3, 4, 5, 2, 1, 6], ![4, 5, 0, 1, 6, 7, 2, 3], ![6, 7, 4, 5, 2, 3, 0, 1], ![1, 6, 5, 2, 3, 4, 7, 0], ![2, 3, 6, 7, 0, 1, 4, 5]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (5 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 7 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 160 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask6

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![7, 0, 5, 2, 3, 4, 1, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 3, 0, 7, 6, 1, 2, 5], ![1, 6, 3, 4, 5, 2, 7, 0], ![6, 7, 4, 5, 2, 3, 0, 1], ![2, 5, 6, 1, 0, 7, 4, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (6 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 7 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 160 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 6, 3, 4, 5, 2, 7, 0], ![4, 3, 0, 7, 6, 1, 2, 5], ![6, 7, 4, 5, 2, 3, 0, 1], ![1, 6, 3, 4, 5, 2, 7, 0], ![2, 5, 6, 1, 0, 7, 4, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (7 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 7 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 160 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

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
    · exact Mask6.not_mem
    · exact Mask7.not_mem
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 299) :
    Classified H := classify separation_checked H hH

end Node299

end ReeTwo.SylowModel.SmallEvenMaximalLower
