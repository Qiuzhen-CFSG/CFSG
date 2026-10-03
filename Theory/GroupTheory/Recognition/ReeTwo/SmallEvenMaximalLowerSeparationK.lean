module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerWordsK
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperCoordinates

/-!+# Nonmembership certificates for lower even maximal subgroups, batch K

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

namespace Node250

namespace Mask3

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 2 → Fin 2 :=
  ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![1, 0], ![0, 1], ![0, 1]]
private def witness : E := (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (3 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 24 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask3

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (11 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 8 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
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
    · exact Mask3.not_mem
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact Mask11.not_mem
    · trivial
    · trivial
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 250) :
    Classified H := classify separation_checked H hH

end Node250

namespace Node261

namespace Mask5

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![3, 2, 1, 0], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![3, 2, 1, 0], ![1, 0, 3, 2], ![0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (5 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 36 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask7

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (7 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 100 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

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
    · exact Mask5.not_mem
    · trivial
    · exact Mask7.not_mem
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 261) :
    Classified H := classify separation_checked H hH

end Node261

namespace Node264

namespace Mask2

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![5, 4, 7, 6, 1, 0, 3, 2], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![5, 4, 7, 6, 1, 0, 3, 2], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (2 : Nat).testBit k.val

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

namespace Mask7

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 1⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (7 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 68 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

public theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ m : Fin 16,
      (branches (fun k => m.val.testBit k.val)).Separation gen
        (fun k => m.val.testBit k.val) (pivot (fun k => m.val.testBit k.val)) := by
    intro m
    fin_cases m
    · trivial
    · trivial
    · exact Mask2.not_mem
    · trivial
    · trivial
    · trivial
    · trivial
    · exact Mask7.not_mem
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 264) :
    Classified H := classify separation_checked H hH

end Node264

namespace Node267

namespace Mask2

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2], ![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (2 : Nat).testBit k.val

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

namespace Mask5

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6]]
private def witness : E := (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (5 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 36 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

public theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ m : Fin 16,
      (branches (fun k => m.val.testBit k.val)).Separation gen
        (fun k => m.val.testBit k.val) (pivot (fun k => m.val.testBit k.val)) := by
    intro m
    fin_cases m
    · trivial
    · trivial
    · exact Mask2.not_mem
    · trivial
    · trivial
    · exact Mask5.not_mem
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 267) :
    Classified H := classify separation_checked H hH

end Node267

namespace Node269

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![29, 24, 31, 26, 25, 28, 27, 30, 21, 16, 23, 18, 17, 20, 19, 22, 13, 8, 15, 10, 9, 12, 11, 14, 5, 0, 7, 2, 1, 4, 3, 6], ![10, 19, 0, 25, 14, 23, 4, 29, 2, 27, 8, 17, 6, 31, 12, 21, 26, 3, 16, 9, 30, 7, 20, 13, 18, 11, 24, 1, 22, 15, 28, 5], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![29, 24, 31, 26, 25, 28, 27, 30, 21, 16, 23, 18, 17, 20, 19, 22, 13, 8, 15, 10, 9, 12, 11, 14, 5, 0, 7, 2, 1, 4, 3, 6], ![10, 19, 0, 25, 14, 23, 4, 29, 2, 27, 8, 17, 6, 31, 12, 21, 26, 3, 16, 9, 30, 7, 20, 13, 18, 11, 24, 1, 22, 15, 28, 5], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)
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

theorem not_mem : Collected.decode 256 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![9, 0, 11, 2, 17, 24, 19, 26, 1, 8, 3, 10, 25, 16, 27, 18, 5, 12, 7, 14, 29, 20, 31, 22, 13, 4, 15, 6, 21, 28, 23, 30], ![12, 13, 14, 15, 10, 11, 8, 9, 4, 5, 6, 7, 2, 3, 0, 1, 30, 31, 28, 29, 24, 25, 26, 27, 22, 23, 20, 21, 16, 17, 18, 19], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![21, 28, 23, 30, 13, 4, 15, 6, 29, 20, 31, 22, 5, 12, 7, 14, 25, 16, 27, 18, 1, 8, 3, 10, 17, 24, 19, 26, 9, 0, 11, 2], ![14, 15, 12, 13, 8, 9, 10, 11, 6, 7, 4, 5, 0, 1, 2, 3, 28, 29, 30, 31, 26, 27, 24, 25, 20, 21, 22, 23, 18, 19, 16, 17]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask6

private def generators : Fin 6 → E :=
  ![(⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![31, 28, 29, 30, 27, 24, 25, 26, 23, 20, 21, 22, 19, 16, 17, 18, 15, 12, 13, 14, 11, 8, 9, 10, 7, 4, 5, 6, 3, 0, 1, 2], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![16, 13, 18, 15, 28, 1, 30, 3, 24, 5, 26, 7, 20, 9, 22, 11, 8, 21, 10, 23, 4, 25, 6, 27, 0, 29, 2, 31, 12, 17, 14, 19], ![3, 0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 15, 12, 13, 14, 19, 16, 17, 18, 23, 20, 21, 22, 27, 24, 25, 26, 31, 28, 29, 30], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![24, 5, 26, 7, 20, 9, 22, 11, 16, 13, 18, 15, 28, 1, 30, 3, 0, 29, 2, 31, 12, 17, 14, 19, 8, 21, 10, 23, 4, 25, 6, 27]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)
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

theorem not_mem : Collected.decode 256 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 0, 1⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![9, 30, 11, 28, 19, 4, 17, 6, 1, 22, 3, 20, 27, 12, 25, 14, 7, 16, 5, 18, 29, 10, 31, 8, 15, 24, 13, 26, 21, 2, 23, 0], ![12, 15, 14, 13, 10, 9, 8, 11, 4, 7, 6, 5, 2, 1, 0, 3, 30, 29, 28, 31, 24, 27, 26, 25, 22, 21, 20, 23, 16, 19, 18, 17], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![23, 0, 21, 2, 13, 26, 15, 24, 31, 8, 29, 10, 5, 18, 7, 16, 25, 14, 27, 12, 3, 20, 1, 22, 17, 6, 19, 4, 11, 28, 9, 30], ![14, 13, 12, 15, 8, 11, 10, 9, 6, 5, 4, 7, 0, 3, 2, 1, 28, 31, 30, 29, 26, 25, 24, 27, 20, 23, 22, 21, 18, 17, 16, 19]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 269) :
    Classified H := classify separation_checked H hH

end Node269

namespace Node270

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![6, 7, 4, 5, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (4 : Nat).testBit k.val

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

end Mask4

namespace Mask5

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5], ![1, 4, 3, 6, 5, 0, 7, 2], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![5, 0, 7, 2, 1, 4, 3, 6], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (5 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 320 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask6

private def generators : Fin 8 → E :=
  ![(⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![6, 5, 4, 7, 0, 3, 2, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 5, 4, 7, 0, 3, 2, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (6 : Nat).testBit k.val

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

end Mask6

namespace Mask7

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![5, 6, 7, 4, 1, 2, 3, 0], ![1, 2, 3, 0, 5, 6, 7, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5], ![7, 4, 5, 6, 3, 0, 1, 2], ![3, 0, 1, 2, 7, 4, 5, 6], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (7 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 320 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![29, 24, 31, 26, 25, 28, 27, 30, 21, 16, 23, 18, 17, 20, 19, 22, 13, 8, 15, 10, 9, 12, 11, 14, 5, 0, 7, 2, 1, 4, 3, 6], ![18, 3, 16, 1, 22, 7, 20, 5, 26, 11, 24, 9, 30, 15, 28, 13, 2, 19, 0, 17, 6, 23, 4, 21, 10, 27, 8, 25, 14, 31, 12, 29], ![24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![29, 24, 31, 26, 25, 28, 27, 30, 21, 16, 23, 18, 17, 20, 19, 22, 13, 8, 15, 10, 9, 12, 11, 14, 5, 0, 7, 2, 1, 4, 3, 6], ![18, 3, 16, 1, 22, 7, 20, 5, 26, 11, 24, 9, 30, 15, 28, 13, 2, 19, 0, 17, 6, 23, 4, 21, 10, 27, 8, 25, 14, 31, 12, 29], ![24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)
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

theorem not_mem : Collected.decode 256 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![25, 24, 27, 26, 29, 28, 31, 30, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 1, 0, 3, 2, 5, 4, 7, 6], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![20, 21, 22, 23, 16, 17, 18, 19, 30, 31, 28, 29, 26, 27, 24, 25, 6, 7, 4, 5, 2, 3, 0, 1, 12, 13, 14, 15, 8, 9, 10, 11], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 17, 16, 19, 18, 21, 20, 23, 22, 9, 8, 11, 10, 13, 12, 15, 14, 25, 24, 27, 26, 29, 28, 31, 30], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![22, 23, 20, 21, 18, 19, 16, 17, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 14, 15, 12, 13, 10, 11, 8, 9]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)
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

theorem not_mem : Collected.decode 256 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

namespace Mask10

private def generators : Fin 8 → E :=
  ![(⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![31, 28, 29, 30, 27, 24, 25, 26, 23, 20, 21, 22, 19, 16, 17, 18, 15, 12, 13, 14, 11, 8, 9, 10, 7, 4, 5, 6, 3, 0, 1, 2], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![16, 9, 18, 11, 20, 13, 22, 15, 24, 1, 26, 3, 28, 5, 30, 7, 0, 25, 2, 27, 4, 29, 6, 31, 8, 17, 10, 19, 12, 21, 14, 23], ![7, 4, 5, 6, 3, 0, 1, 2, 15, 12, 13, 14, 11, 8, 9, 10, 23, 20, 21, 22, 19, 16, 17, 18, 31, 28, 29, 30, 27, 24, 25, 26], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![16, 9, 18, 11, 20, 13, 22, 15, 24, 1, 26, 3, 28, 5, 30, 7, 0, 25, 2, 27, 4, 29, 6, 31, 8, 17, 10, 19, 12, 21, 14, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)
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

theorem not_mem : Collected.decode 256 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask10

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![29, 6, 31, 4, 25, 2, 27, 0, 15, 20, 13, 22, 11, 16, 9, 18, 23, 12, 21, 14, 19, 8, 17, 10, 5, 30, 7, 28, 1, 26, 3, 24], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![20, 23, 22, 21, 16, 19, 18, 17, 30, 29, 28, 31, 26, 25, 24, 27, 6, 5, 4, 7, 2, 1, 0, 3, 12, 15, 14, 13, 8, 11, 10, 9], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![7, 28, 5, 30, 3, 24, 1, 26, 21, 14, 23, 12, 17, 10, 19, 8, 13, 22, 15, 20, 9, 18, 11, 16, 31, 4, 29, 6, 27, 0, 25, 2], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![22, 21, 20, 23, 18, 17, 16, 19, 28, 31, 30, 29, 24, 27, 26, 25, 4, 7, 6, 5, 0, 3, 2, 1, 14, 13, 12, 15, 10, 9, 8, 11]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)
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

theorem not_mem : Collected.decode 256 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask11

namespace Mask12

private def generators : Fin 8 → E :=
  ![(⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![30, 31, 28, 29, 24, 25, 26, 27, 20, 21, 22, 23, 18, 19, 16, 17, 12, 13, 14, 15, 10, 11, 8, 9, 6, 7, 4, 5, 0, 1, 2, 3], ![25, 24, 27, 26, 5, 4, 7, 6, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 13, 12, 15, 14, 1, 0, 3, 2, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![30, 31, 28, 29, 24, 25, 26, 27, 20, 21, 22, 23, 18, 19, 16, 17, 12, 13, 14, 15, 10, 11, 8, 9, 6, 7, 4, 5, 0, 1, 2, 3], ![25, 24, 27, 26, 5, 4, 7, 6, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 13, 12, 15, 14, 1, 0, 3, 2, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![26, 3, 24, 1, 30, 7, 28, 5, 18, 11, 16, 9, 22, 15, 20, 13, 10, 19, 8, 17, 14, 23, 12, 21, 2, 27, 0, 25, 6, 31, 4, 29], ![1, 4, 3, 6, 5, 0, 7, 2, 9, 12, 11, 14, 13, 8, 15, 10, 17, 20, 19, 22, 21, 16, 23, 18, 25, 28, 27, 30, 29, 24, 31, 26], ![17, 20, 19, 22, 21, 16, 23, 18, 25, 28, 27, 30, 29, 24, 31, 26, 1, 4, 3, 6, 5, 0, 7, 2, 9, 12, 11, 14, 13, 8, 15, 10], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![2, 27, 0, 25, 6, 31, 4, 29, 10, 19, 8, 17, 14, 23, 12, 21, 18, 11, 16, 9, 22, 15, 20, 13, 26, 3, 24, 1, 30, 7, 28, 5], ![5, 0, 7, 2, 1, 4, 3, 6, 13, 8, 15, 10, 9, 12, 11, 14, 21, 16, 23, 18, 17, 20, 19, 22, 29, 24, 31, 26, 25, 28, 27, 30], ![21, 16, 23, 18, 17, 20, 19, 22, 29, 24, 31, 26, 25, 28, 27, 30, 5, 0, 7, 2, 1, 4, 3, 6, 13, 8, 15, 10, 9, 12, 11, 14]]
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
  ![(⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![30, 29, 28, 31, 24, 27, 26, 25, 20, 23, 22, 21, 18, 17, 16, 19, 12, 15, 14, 13, 10, 9, 8, 11, 6, 5, 4, 7, 0, 3, 2, 1], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![5, 28, 7, 30, 25, 0, 27, 2, 21, 12, 23, 14, 9, 16, 11, 18, 13, 20, 15, 22, 17, 8, 19, 10, 29, 4, 31, 6, 1, 24, 3, 26], ![17, 8, 19, 10, 13, 20, 15, 22, 1, 24, 3, 26, 29, 4, 31, 6, 25, 0, 27, 2, 5, 28, 7, 30, 9, 16, 11, 18, 21, 12, 23, 14], ![6, 5, 4, 7, 0, 3, 2, 1, 12, 15, 14, 13, 10, 9, 8, 11, 20, 23, 22, 21, 18, 17, 16, 19, 30, 29, 28, 31, 24, 27, 26, 25], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![5, 28, 7, 30, 25, 0, 27, 2, 21, 12, 23, 14, 9, 16, 11, 18, 13, 20, 15, 22, 17, 8, 19, 10, 29, 4, 31, 6, 1, 24, 3, 26], ![17, 8, 19, 10, 13, 20, 15, 22, 1, 24, 3, 26, 29, 4, 31, 6, 25, 0, 27, 2, 5, 28, 7, 30, 9, 16, 11, 18, 21, 12, 23, 14]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![29, 6, 31, 4, 25, 2, 27, 0, 21, 14, 23, 12, 17, 10, 19, 8, 13, 22, 15, 20, 9, 18, 11, 16, 5, 30, 7, 28, 1, 26, 3, 24], ![1, 2, 3, 0, 5, 6, 7, 4, 9, 10, 11, 8, 13, 14, 15, 12, 17, 18, 19, 16, 21, 22, 23, 20, 25, 26, 27, 24, 29, 30, 31, 28], ![21, 22, 23, 20, 17, 18, 19, 16, 29, 30, 31, 28, 25, 26, 27, 24, 5, 6, 7, 4, 1, 2, 3, 0, 13, 14, 15, 12, 9, 10, 11, 8], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![7, 28, 5, 30, 3, 24, 1, 26, 15, 20, 13, 22, 11, 16, 9, 18, 23, 12, 21, 14, 19, 8, 17, 10, 31, 4, 29, 6, 27, 0, 25, 2], ![3, 0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 15, 12, 13, 14, 19, 16, 17, 18, 23, 20, 21, 22, 27, 24, 25, 26, 31, 28, 29, 30], ![23, 20, 21, 22, 19, 16, 17, 18, 31, 28, 29, 30, 27, 24, 25, 26, 7, 4, 5, 6, 3, 0, 1, 2, 15, 12, 13, 14, 11, 8, 9, 10]]
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 270) :
    Classified H := classify separation_checked H hH

end Node270

namespace Node272

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![7, 0, 5, 2, 3, 4, 1, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 0, 5, 2, 3, 4, 1, 6], ![2, 3, 0, 1, 6, 7, 4, 5]]
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
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 6, 7, 0, 1, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 2, 3, 0, 1], ![4, 5, 0, 1, 6, 7, 2, 3]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![7, 0, 5, 2, 3, 4, 1, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 0, 5, 2, 3, 4, 1, 6], ![2, 3, 0, 1, 6, 7, 4, 5]]
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 272) :
    Classified H := classify separation_checked H hH

end Node272

namespace Node273

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![1, 0, 14, 4, 3, 15, 7, 6, 12, 10, 9, 13, 8, 11, 2, 5], ![15, 11, 7, 14, 8, 10, 13, 5, 1, 12, 2, 4, 6, 9, 0, 3], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 0, 14, 4, 3, 15, 7, 6, 12, 10, 9, 13, 8, 11, 2, 5], ![15, 11, 7, 14, 8, 10, 13, 5, 1, 12, 2, 4, 6, 9, 0, 3], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 192 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![13, 10, 7, 4, 2, 15, 11, 3, 12, 14, 0, 9, 5, 1, 6, 8], ![5, 8, 11, 14, 12, 0, 10, 15, 1, 13, 6, 2, 4, 9, 3, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![7, 4, 13, 10, 0, 9, 5, 1, 6, 8, 2, 15, 11, 3, 12, 14], ![5, 8, 11, 14, 12, 0, 10, 15, 1, 13, 6, 2, 4, 9, 3, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 192 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask6

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![2, 14, 0, 5, 15, 3, 8, 12, 6, 11, 13, 9, 7, 10, 1, 4], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![7, 9, 14, 10, 6, 15, 1, 3, 12, 4, 0, 13, 11, 8, 5, 2], ![8, 12, 6, 11, 13, 9, 2, 14, 0, 5, 15, 3, 1, 4, 7, 10], ![3, 4, 5, 0, 1, 2, 9, 10, 11, 6, 7, 8, 13, 12, 15, 14], ![10, 6, 15, 7, 9, 14, 4, 0, 13, 1, 3, 12, 8, 11, 2, 5]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 192 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![11, 12, 0, 8, 13, 3, 5, 14, 6, 2, 15, 9, 10, 7, 4, 1], ![12, 8, 7, 13, 11, 10, 14, 2, 1, 15, 5, 4, 0, 3, 6, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![5, 14, 6, 2, 15, 9, 11, 12, 0, 8, 13, 3, 4, 1, 10, 7], ![12, 8, 7, 13, 11, 10, 14, 2, 1, 15, 5, 4, 0, 3, 6, 9]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 192 ∉
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 273) :
    Classified H := classify separation_checked H hH

end Node273

namespace Node274

namespace Mask3

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 2 → Fin 2 :=
  ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![1, 0], ![0, 1]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 1⟩, 0)
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

theorem not_mem : Collected.decode 904 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask3

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3], ![1, 0, 3, 2], ![3, 2, 1, 0]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 1⟩, 0)
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

theorem not_mem : Collected.decode 904 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 1⟩, 0)
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

theorem not_mem : Collected.decode 904 ∉
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 274) :
    Classified H := classify separation_checked H hH

end Node274

end ReeTwo.SylowModel.SmallEvenMaximalLower
