module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerWordsJ
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperCoordinates

/-!+# Nonmembership certificates for lower even maximal subgroups, batch J

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

namespace Node225

namespace Mask5

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![3, 2, 1, 0, 7, 6, 5, 4]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (5 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2056 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 1, 1, 0, 1, 0, 1, 1, 1⟩, 1)
private def signature : Fin 4 → Bool := fun k => (11 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2988 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
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
    · trivial
    · exact Mask5.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 225) :
    Classified H := classify separation_checked H hH

end Node225

namespace Node226

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (8 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2056 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 226) :
    Classified H := classify separation_checked H hH

end Node226

namespace Node227

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (8 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2048 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 24 ∉
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
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact Mask8.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 227) :
    Classified H := classify separation_checked H hH

end Node227

namespace Node228

namespace Mask3

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![3, 2, 1, 0], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3], ![3, 2, 1, 0], ![0, 1, 2, 3], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
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

theorem not_mem : Collected.decode 2048 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask3

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 80 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 24 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask11

namespace Mask13

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 1, 1, 0, 1, 0, 1, 1, 1⟩, 1)
private def signature : Fin 4 → Bool := fun k => (13 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2988 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask13

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
    · exact Mask9.not_mem
    · trivial
    · exact Mask11.not_mem
    · trivial
    · exact Mask13.not_mem
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 228) :
    Classified H := classify separation_checked H hH

end Node228

namespace Node229

namespace Mask2

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3]]
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

namespace Mask3

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)]
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

namespace Mask5

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5]]
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

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (8 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2048 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

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
    · exact Mask3.not_mem
    · trivial
    · exact Mask5.not_mem
    · trivial
    · trivial
    · exact Mask8.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 229) :
    Classified H := classify separation_checked H hH

end Node229

namespace Node230

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (8 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2048 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 230) :
    Classified H := classify separation_checked H hH

end Node230

namespace Node231

namespace Mask4

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (4 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask5

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (5 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask6

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (6 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

namespace Mask7

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (7 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

namespace Mask12

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (12 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask12

namespace Mask13

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (13 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask13

namespace Mask14

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (14 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask14

namespace Mask15

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (15 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask15

namespace Mask16

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (16 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask16

namespace Mask17

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (17 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask17

namespace Mask18

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 1)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (18 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask18

namespace Mask19

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (19 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask19

namespace Mask20

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (20 : Nat).testBit k.val

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

end Mask20

namespace Mask21

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (21 : Nat).testBit k.val

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

end Mask21

namespace Mask22

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 1)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (22 : Nat).testBit k.val

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

end Mask22

namespace Mask23

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (23 : Nat).testBit k.val

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

end Mask23

namespace Mask24

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask24

namespace Mask25

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask25

namespace Mask26

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 1)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask26

namespace Mask27

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask27

namespace Mask28

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (28 : Nat).testBit k.val

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

end Mask28

namespace Mask29

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (29 : Nat).testBit k.val

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

end Mask29

namespace Mask30

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 1)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (30 : Nat).testBit k.val

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

end Mask30

namespace Mask31

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (31 : Nat).testBit k.val

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

end Mask31

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
    · trivial
    · trivial
    · trivial
    · trivial
    · exact Mask12.not_mem
    · exact Mask13.not_mem
    · exact Mask14.not_mem
    · exact Mask15.not_mem
    · exact Mask16.not_mem
    · exact Mask17.not_mem
    · exact Mask18.not_mem
    · exact Mask19.not_mem
    · exact Mask20.not_mem
    · exact Mask21.not_mem
    · exact Mask22.not_mem
    · exact Mask23.not_mem
    · exact Mask24.not_mem
    · exact Mask25.not_mem
    · exact Mask26.not_mem
    · exact Mask27.not_mem
    · exact Mask28.not_mem
    · exact Mask29.not_mem
    · exact Mask30.not_mem
    · exact Mask31.not_mem
  have hs : ∀ (σ : Fin 5 → Bool),
      σ = fun k => (signatureIndex σ % 32).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 231) :
    Classified H := classify separation_checked H hH

end Node231

namespace Node232

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4], ![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4]]
private def witness : E := (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (4 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2072 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

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
    · trivial
    · trivial
    · trivial
    · exact Mask8.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 232) :
    Classified H := classify separation_checked H hH

end Node232

namespace Node233

namespace Mask2

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 1 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 1 → Fin 1 :=
  ![![0], ![0], ![0], ![0], ![0], ![0], ![0], ![0]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (2 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 0 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 2056 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 0 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask2

namespace Mask10

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 2 → Fin 2 :=
  ![![0, 1], ![0, 1], ![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![1, 0]]
private def witness : E := (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (10 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2072 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 3 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask10

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
    · trivial
    · trivial
    · trivial
    · exact Mask10.not_mem
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 233) :
    Classified H := classify separation_checked H hH

end Node233

namespace Node234

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 2 → Fin 2 :=
  ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![1, 0], ![0, 1], ![0, 1]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (8 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2056 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 3 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask10

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, 1)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 2 → Fin 2 :=
  ![![0, 1], ![0, 1], ![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![1, 0]]
private def witness : E := (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (10 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2072 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 3 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask10

namespace Mask12

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (12 : Nat).testBit k.val

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

end Mask12

namespace Mask13

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![3, 2, 1, 0, 7, 6, 5, 4], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![3, 2, 1, 0, 7, 6, 5, 4], ![1, 0, 3, 2, 5, 4, 7, 6]]
private def witness : E := (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (13 : Nat).testBit k.val

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

end Mask13

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
    · trivial
    · exact Mask10.not_mem
    · trivial
    · exact Mask12.not_mem
    · exact Mask13.not_mem
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 234) :
    Classified H := classify separation_checked H hH

end Node234

namespace Node235

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (9 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2072 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

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
    · trivial
    · exact Mask9.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 235) :
    Classified H := classify separation_checked H hH

end Node235

namespace Node236

namespace Mask5

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 4 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask7

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![3, 2, 1, 0], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![3, 2, 1, 0], ![1, 0, 3, 2], ![0, 1, 2, 3]]
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
    trunc 6 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 68 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask7

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (8 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2056 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (9 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2072 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

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
    · exact Mask8.not_mem
    · exact Mask9.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 236) :
    Classified H := classify separation_checked H hH

end Node236

namespace Node238

namespace Mask16

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (16 : Nat).testBit k.val

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

end Mask16

namespace Mask17

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (17 : Nat).testBit k.val

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

end Mask17

namespace Mask18

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 1), (⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 1)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (18 : Nat).testBit k.val

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

end Mask18

namespace Mask19

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (19 : Nat).testBit k.val

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

end Mask19

namespace Mask20

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (20 : Nat).testBit k.val

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

end Mask20

namespace Mask21

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (21 : Nat).testBit k.val

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

end Mask21

namespace Mask22

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 1), (⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 1)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (22 : Nat).testBit k.val

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

end Mask22

namespace Mask23

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (23 : Nat).testBit k.val

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

end Mask23

namespace Mask24

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask24

namespace Mask25

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask25

namespace Mask26

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 1), (⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 1)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2], ![15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2], ![15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask26

namespace Mask27

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask27

namespace Mask28

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8], ![15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8], ![15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (28 : Nat).testBit k.val

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

end Mask28

namespace Mask29

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (29 : Nat).testBit k.val

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

end Mask29

namespace Mask30

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 1), (⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 1⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 1)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1], ![11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4], ![15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (30 : Nat).testBit k.val

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

end Mask30

namespace Mask31

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 1)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (31 : Nat).testBit k.val

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

end Mask31

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
    · trivial
    · trivial
    · exact Mask16.not_mem
    · exact Mask17.not_mem
    · exact Mask18.not_mem
    · exact Mask19.not_mem
    · exact Mask20.not_mem
    · exact Mask21.not_mem
    · exact Mask22.not_mem
    · exact Mask23.not_mem
    · exact Mask24.not_mem
    · exact Mask25.not_mem
    · exact Mask26.not_mem
    · exact Mask27.not_mem
    · exact Mask28.not_mem
    · exact Mask29.not_mem
    · exact Mask30.not_mem
    · exact Mask31.not_mem
  have hs : ∀ (σ : Fin 5 → Bool),
      σ = fun k => (signatureIndex σ % 32).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 238) :
    Classified H := classify separation_checked H hH

end Node238

namespace Node239

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4], ![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (4 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2064 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

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
    · trivial
    · trivial
    · trivial
    · exact Mask8.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 239) :
    Classified H := classify separation_checked H hH

end Node239

namespace Node240

namespace Mask2

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 1 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 1 → Fin 1 :=
  ![![0], ![0], ![0], ![0], ![0], ![0], ![0], ![0]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (2 : Nat).testBit k.val

private theorem code_checked : ∀ k,
    Collected.code (encode (generators k)) = packedSchreier gen signature (pivot signature) k := by
  decide +kernel

private theorem generators_eq : encode ∘ generators = schreier gen signature (pivot signature) := by
  funext k
  apply Collected.code_injective
  simpa only [Function.comp_apply, packedSchreier_eq] using code_checked k

private theorem transitions_checked : ∀ i j,
    trunc 0 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 2048 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 0 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask2

namespace Mask10

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, 1)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 2 → Fin 2 :=
  ![![0, 1], ![0, 1], ![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![1, 0]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (10 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2064 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 3 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask10

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
    · trivial
    · trivial
    · trivial
    · exact Mask10.not_mem
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 240) :
    Classified H := classify separation_checked H hH

end Node240

namespace Node241

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 2 → Fin 2 :=
  ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![1, 0], ![0, 1], ![0, 1]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (8 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2048 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 3 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask10

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 1)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 2 → Fin 2 :=
  ![![0, 1], ![0, 1], ![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![1, 0]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (10 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2064 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 3 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask10

namespace Mask12

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (12 : Nat).testBit k.val

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

end Mask12

namespace Mask15

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1], ![3, 2, 1, 0, 7, 6, 5, 4], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1], ![3, 2, 1, 0, 7, 6, 5, 4], ![1, 0, 3, 2, 5, 4, 7, 6]]
private def witness : E := (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (15 : Nat).testBit k.val

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
    · trivial
    · exact Mask10.not_mem
    · trivial
    · exact Mask12.not_mem
    · trivial
    · trivial
    · exact Mask15.not_mem
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 241) :
    Classified H := classify separation_checked H hH

end Node241

namespace Node243

namespace Mask3

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![3, 2, 1, 0], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3], ![3, 2, 1, 0], ![0, 1, 2, 3], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
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

theorem not_mem : Collected.decode 2048 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask3

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (11 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2064 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 243) :
    Classified H := classify separation_checked H hH

end Node243

namespace Node244

namespace Mask5

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0)]
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

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (8 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2048 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (11 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2064 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
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
    · trivial
    · exact Mask5.not_mem
    · trivial
    · exact Mask7.not_mem
    · exact Mask8.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 244) :
    Classified H := classify separation_checked H hH

end Node244

namespace Node245

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (4 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (8 : Nat).testBit k.val

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

end Mask8

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
    · trivial
    · trivial
    · trivial
    · exact Mask8.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 245) :
    Classified H := classify separation_checked H hH

end Node245

namespace Node246

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask12

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (12 : Nat).testBit k.val

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

end Mask12

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
    · trivial
    · trivial
    · trivial
    · exact Mask12.not_mem
    · trivial
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 246) :
    Classified H := classify separation_checked H hH

end Node246

namespace Node249

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (9 : Nat).testBit k.val

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

end Mask9

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
    · trivial
    · exact Mask9.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 249) :
    Classified H := classify separation_checked H hH

end Node249

end ReeTwo.SylowModel.SmallEvenMaximalLower
