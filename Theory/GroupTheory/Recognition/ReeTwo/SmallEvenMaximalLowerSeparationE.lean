module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerWordsE
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperCoordinates

/-!+# Nonmembership certificates for lower even maximal subgroups, batch E

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

namespace Node105

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 1⟩, 1), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![3, 2, 1, 0], ![1, 0, 3, 2], ![0, 1, 2, 3], ![3, 2, 1, 0], ![1, 0, 3, 2], ![0, 1, 2, 3]]
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

namespace Mask6

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 1, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![3, 2, 1, 0], ![0, 1, 2, 3], ![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 8 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
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
    · trivial
    · trivial
    · trivial
    · exact Mask4.not_mem
    · trivial
    · exact Mask6.not_mem
    · trivial
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 105) :
    Classified H := classify separation_checked H hH

end Node105

namespace Node106

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3], ![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3]]
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

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 8 ∉
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
    · trivial
    · trivial
    · exact Mask7.not_mem
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 106) :
    Classified H := classify separation_checked H hH

end Node106

namespace Node107

namespace Mask3

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![3, 2, 1, 0], ![1, 0, 3, 2], ![0, 1, 2, 3], ![3, 2, 1, 0], ![1, 0, 3, 2]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2]]
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
    trunc 4 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 136 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 4 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2]]
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
    trunc 4 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 136 ∉
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
    · exact Mask3.not_mem
    · trivial
    · exact Mask5.not_mem
    · trivial
    · exact Mask7.not_mem
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 107) :
    Classified H := classify separation_checked H hH

end Node107

namespace Node109

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)]
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
    · trivial
    · exact Mask5.not_mem
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 109) :
    Classified H := classify separation_checked H hH

end Node109

namespace Node110

namespace Mask3

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![3, 2, 1, 0], ![1, 0, 3, 2], ![0, 1, 2, 3], ![3, 2, 1, 0], ![1, 0, 3, 2]]
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

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 1, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 8 ∉
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
    · exact Mask3.not_mem
    · trivial
    · trivial
    · trivial
    · exact Mask7.not_mem
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 110) :
    Classified H := classify separation_checked H hH

end Node110

namespace Node112

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![29, 4, 15, 22, 25, 0, 11, 18, 21, 12, 7, 30, 17, 8, 3, 26, 13, 20, 31, 6, 9, 16, 27, 2, 5, 28, 23, 14, 1, 24, 19, 10], ![30, 7, 4, 29, 26, 3, 0, 25, 22, 15, 12, 21, 18, 11, 8, 17, 14, 23, 20, 13, 10, 19, 16, 9, 6, 31, 28, 5, 2, 27, 24, 1], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![29, 4, 15, 22, 25, 0, 11, 18, 21, 12, 7, 30, 17, 8, 3, 26, 13, 20, 31, 6, 9, 16, 27, 2, 5, 28, 23, 14, 1, 24, 19, 10], ![30, 7, 4, 29, 26, 3, 0, 25, 22, 15, 12, 21, 18, 11, 8, 17, 14, 23, 20, 13, 10, 19, 16, 9, 6, 31, 28, 5, 2, 27, 24, 1], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![30, 27, 0, 5, 26, 31, 4, 1, 10, 15, 20, 17, 14, 11, 16, 21, 18, 23, 12, 9, 22, 19, 8, 13, 6, 3, 24, 29, 2, 7, 28, 25], ![31, 30, 1, 0, 27, 26, 5, 4, 11, 10, 21, 20, 15, 14, 17, 16, 19, 18, 13, 12, 23, 22, 9, 8, 7, 6, 25, 24, 3, 2, 29, 28], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![2, 7, 28, 25, 6, 3, 24, 29, 22, 19, 8, 13, 18, 23, 12, 9, 14, 11, 16, 21, 10, 15, 20, 17, 26, 31, 4, 1, 30, 27, 0, 5], ![3, 2, 29, 28, 7, 6, 25, 24, 23, 22, 9, 8, 19, 18, 13, 12, 15, 14, 17, 16, 11, 10, 21, 20, 27, 26, 5, 4, 31, 30, 1, 0], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
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
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![30, 3, 0, 29, 26, 7, 4, 25, 10, 23, 20, 9, 14, 19, 16, 13, 18, 15, 12, 17, 22, 11, 8, 21, 6, 27, 24, 5, 2, 31, 28, 1], ![19, 14, 9, 20, 23, 10, 13, 16, 3, 30, 25, 4, 7, 26, 29, 0, 27, 6, 1, 28, 31, 2, 5, 24, 11, 22, 17, 12, 15, 18, 21, 8], ![29, 28, 31, 30, 25, 24, 27, 26, 21, 20, 23, 22, 17, 16, 19, 18, 13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![26, 7, 4, 25, 30, 3, 0, 29, 14, 19, 16, 13, 10, 23, 20, 9, 22, 11, 8, 21, 18, 15, 12, 17, 2, 31, 28, 1, 6, 27, 24, 5], ![15, 18, 21, 8, 11, 22, 17, 12, 31, 2, 5, 24, 27, 6, 1, 28, 7, 26, 29, 0, 3, 30, 25, 4, 23, 10, 13, 16, 19, 14, 9, 20]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![2, 27, 0, 25, 6, 31, 4, 29, 22, 15, 20, 13, 18, 11, 16, 9, 14, 23, 12, 21, 10, 19, 8, 17, 26, 3, 24, 1, 30, 7, 28, 5], ![31, 2, 29, 0, 27, 6, 25, 4, 11, 22, 9, 20, 15, 18, 13, 16, 19, 14, 17, 12, 23, 10, 21, 8, 7, 26, 5, 24, 3, 30, 1, 28], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![30, 7, 28, 5, 26, 3, 24, 1, 10, 19, 8, 17, 14, 23, 12, 21, 18, 11, 16, 9, 22, 15, 20, 13, 6, 31, 4, 29, 2, 27, 0, 25], ![3, 30, 1, 28, 7, 26, 5, 24, 23, 10, 21, 8, 19, 14, 17, 12, 15, 18, 13, 16, 11, 22, 9, 20, 27, 6, 25, 4, 31, 2, 29, 0], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
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
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![31, 2, 29, 0, 27, 6, 25, 4, 15, 18, 13, 16, 11, 22, 9, 20, 23, 10, 21, 8, 19, 14, 17, 12, 7, 26, 5, 24, 3, 30, 1, 28], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![18, 15, 16, 13, 22, 11, 20, 9, 6, 27, 4, 25, 2, 31, 0, 29, 30, 3, 28, 1, 26, 7, 24, 5, 10, 23, 8, 21, 14, 19, 12, 17], ![29, 28, 31, 30, 25, 24, 27, 26, 21, 20, 23, 22, 17, 16, 19, 18, 13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2], ![27, 6, 25, 4, 31, 2, 29, 0, 11, 22, 9, 20, 15, 18, 13, 16, 19, 14, 17, 12, 23, 10, 21, 8, 3, 30, 1, 28, 7, 26, 5, 24], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![14, 19, 12, 17, 10, 23, 8, 21, 26, 7, 24, 5, 30, 3, 28, 1, 2, 31, 0, 29, 6, 27, 4, 25, 22, 11, 20, 9, 18, 15, 16, 13]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![30, 7, 0, 25, 26, 3, 4, 29, 10, 19, 20, 13, 14, 23, 16, 9, 18, 11, 12, 21, 22, 15, 8, 17, 6, 31, 24, 1, 2, 27, 28, 5], ![3, 30, 29, 0, 7, 26, 25, 4, 23, 10, 9, 20, 19, 14, 13, 16, 15, 18, 17, 12, 11, 22, 21, 8, 27, 6, 5, 24, 31, 2, 1, 28], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![2, 27, 28, 5, 6, 31, 24, 1, 22, 15, 8, 17, 18, 11, 12, 21, 14, 23, 16, 9, 10, 19, 20, 13, 26, 3, 4, 29, 30, 7, 0, 25], ![31, 2, 1, 28, 27, 6, 5, 24, 11, 22, 21, 8, 15, 18, 17, 12, 19, 14, 13, 16, 23, 10, 9, 20, 7, 26, 25, 4, 3, 30, 29, 0], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
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
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![3, 2, 5, 4, 7, 6, 1, 0, 11, 10, 13, 12, 15, 14, 9, 8, 19, 18, 21, 20, 23, 22, 17, 16, 27, 26, 29, 28, 31, 30, 25, 24], ![17, 12, 11, 22, 21, 8, 15, 18, 25, 4, 3, 30, 29, 0, 7, 26, 1, 28, 27, 6, 5, 24, 31, 2, 9, 20, 19, 14, 13, 16, 23, 10], ![29, 28, 31, 30, 25, 24, 27, 26, 21, 20, 23, 22, 17, 16, 19, 18, 13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![27, 26, 29, 28, 31, 30, 25, 24, 19, 18, 21, 20, 23, 22, 17, 16, 11, 10, 13, 12, 15, 14, 9, 8, 3, 2, 5, 4, 7, 6, 1, 0], ![13, 16, 23, 10, 9, 20, 19, 14, 5, 24, 31, 2, 1, 28, 27, 6, 29, 0, 7, 26, 25, 4, 3, 30, 21, 8, 15, 18, 17, 12, 11, 22]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![2, 7, 0, 5, 6, 3, 4, 1, 22, 19, 20, 17, 18, 23, 16, 21, 14, 11, 12, 9, 10, 15, 8, 13, 26, 31, 24, 29, 30, 27, 28, 25], ![3, 2, 1, 0, 7, 6, 5, 4, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 27, 26, 25, 24, 31, 30, 29, 28], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![30, 27, 28, 25, 26, 31, 24, 29, 10, 15, 8, 13, 14, 11, 12, 9, 18, 23, 16, 21, 22, 19, 20, 17, 6, 3, 4, 1, 2, 7, 0, 5], ![31, 30, 29, 28, 27, 26, 25, 24, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 7, 6, 5, 4, 3, 2, 1, 0], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 112) :
    Classified H := classify separation_checked H hH

end Node112

namespace Node114

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![11, 2, 9, 0, 15, 6, 13, 4, 3, 10, 1, 8, 7, 14, 5, 12], ![12, 5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![11, 2, 9, 0, 15, 6, 13, 4, 3, 10, 1, 8, 7, 14, 5, 12], ![12, 5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 160 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![13, 0, 15, 2, 5, 8, 7, 10, 9, 4, 11, 6, 1, 12, 3, 14], ![14, 3, 0, 13, 6, 11, 8, 5, 10, 7, 4, 9, 2, 15, 12, 1], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 12, 3, 14, 9, 4, 11, 6, 5, 8, 7, 10, 13, 0, 15, 2], ![2, 15, 12, 1, 10, 7, 4, 9, 6, 11, 8, 5, 14, 3, 0, 13], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 160 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

namespace Mask10

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![14, 3, 0, 13, 10, 7, 4, 9, 6, 11, 8, 5, 2, 15, 12, 1], ![9, 4, 11, 6, 13, 0, 15, 2, 1, 12, 3, 14, 5, 8, 7, 10], ![13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![2, 15, 12, 1, 6, 11, 8, 5, 10, 7, 4, 9, 14, 3, 0, 13], ![5, 8, 7, 10, 1, 12, 3, 14, 13, 0, 15, 2, 9, 4, 11, 6]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 160 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask10

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 0, 3, 2, 9, 8, 11, 10, 5, 4, 7, 6, 13, 12, 15, 14], ![14, 15, 0, 1, 6, 7, 8, 9, 10, 11, 4, 5, 2, 3, 12, 13], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![13, 12, 15, 14, 5, 4, 7, 6, 9, 8, 11, 10, 1, 0, 3, 2], ![2, 3, 12, 13, 10, 11, 4, 5, 6, 7, 8, 9, 14, 15, 0, 1], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 160 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask11

namespace Mask12

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![15, 2, 13, 0, 11, 6, 9, 4, 7, 10, 5, 8, 3, 14, 1, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 5, 10, 7, 0, 13, 2, 15, 12, 1, 14, 3, 4, 9, 6, 11], ![13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2], ![3, 14, 1, 12, 7, 10, 5, 8, 11, 6, 9, 4, 15, 2, 13, 0], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![4, 9, 6, 11, 12, 1, 14, 3, 0, 13, 2, 15, 8, 5, 10, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (12 : Nat).testBit k.val

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

end Mask12

namespace Mask13

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![13, 0, 3, 14, 5, 8, 11, 6, 9, 4, 7, 10, 1, 12, 15, 2], ![2, 15, 0, 13, 10, 7, 8, 5, 6, 11, 4, 9, 14, 3, 12, 1], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 12, 15, 2, 9, 4, 7, 10, 5, 8, 11, 6, 13, 0, 3, 14], ![14, 3, 12, 1, 6, 11, 4, 9, 10, 7, 8, 5, 2, 15, 0, 13], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (13 : Nat).testBit k.val

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

end Mask13

namespace Mask14

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![3, 2, 13, 12, 7, 6, 9, 8, 11, 10, 5, 4, 15, 14, 1, 0], ![9, 4, 11, 6, 13, 0, 15, 2, 1, 12, 3, 14, 5, 8, 7, 10], ![13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![3, 2, 13, 12, 7, 6, 9, 8, 11, 10, 5, 4, 15, 14, 1, 0], ![5, 8, 7, 10, 1, 12, 3, 14, 13, 0, 15, 2, 9, 4, 11, 6]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (14 : Nat).testBit k.val

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

end Mask14

namespace Mask15

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 0, 15, 14, 9, 8, 7, 6, 5, 4, 11, 10, 13, 12, 3, 2], ![2, 3, 0, 1, 10, 11, 8, 9, 6, 7, 4, 5, 14, 15, 12, 13], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![13, 12, 3, 2, 5, 4, 11, 10, 9, 8, 7, 6, 1, 0, 15, 14], ![14, 15, 12, 13, 6, 7, 4, 5, 10, 11, 8, 9, 2, 3, 0, 1], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (15 : Nat).testBit k.val

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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 114) :
    Classified H := classify separation_checked H hH

end Node114

namespace Node119

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![15, 12, 11, 4, 9, 2, 13, 14, 5, 10, 3, 8, 7, 0, 1, 6, 31, 28, 27, 20, 25, 18, 29, 30, 21, 26, 19, 24, 23, 16, 17, 22, 43, 36, 37, 42, 35, 32, 47, 40, 45, 38, 33, 34, 41, 46, 39, 44, 59, 52, 53, 58, 51, 48, 63, 56, 61, 54, 49, 50, 57, 62, 55, 60], ![44, 55, 52, 43, 12, 31, 38, 61, 58, 37, 14, 29, 26, 5, 20, 11, 60, 39, 36, 59, 28, 15, 54, 45, 42, 53, 30, 13, 10, 21, 4, 27, 62, 41, 56, 47, 8, 19, 16, 7, 32, 51, 2, 25, 22, 1, 34, 49, 46, 57, 40, 63, 24, 3, 0, 23, 48, 35, 18, 9, 6, 17, 50, 33], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![15, 12, 11, 4, 9, 2, 13, 14, 5, 10, 3, 8, 7, 0, 1, 6, 31, 28, 27, 20, 25, 18, 29, 30, 21, 26, 19, 24, 23, 16, 17, 22, 43, 36, 37, 42, 35, 32, 47, 40, 45, 38, 33, 34, 41, 46, 39, 44, 59, 52, 53, 58, 51, 48, 63, 56, 61, 54, 49, 50, 57, 62, 55, 60], ![44, 55, 52, 43, 12, 31, 38, 61, 58, 37, 14, 29, 26, 5, 20, 11, 60, 39, 36, 59, 28, 15, 54, 45, 42, 53, 30, 13, 10, 21, 4, 27, 62, 41, 56, 47, 8, 19, 16, 7, 32, 51, 2, 25, 22, 1, 34, 49, 46, 57, 40, 63, 24, 3, 0, 23, 48, 35, 18, 9, 6, 17, 50, 33], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![13, 12, 7, 2, 9, 8, 3, 6, 1, 0, 11, 14, 5, 4, 15, 10, 29, 28, 23, 18, 25, 24, 19, 22, 17, 16, 27, 30, 21, 20, 31, 26, 41, 40, 35, 38, 45, 44, 39, 34, 37, 36, 47, 42, 33, 32, 43, 46, 57, 56, 51, 54, 61, 60, 55, 50, 53, 52, 63, 58, 49, 48, 59, 62], ![46, 31, 56, 29, 42, 27, 60, 25, 50, 3, 36, 1, 54, 7, 32, 5, 62, 15, 40, 13, 58, 11, 44, 9, 34, 19, 52, 17, 38, 23, 48, 21, 26, 43, 12, 41, 30, 47, 8, 45, 6, 55, 16, 53, 2, 51, 20, 49, 10, 59, 28, 57, 14, 63, 24, 61, 22, 39, 0, 37, 18, 35, 4, 33], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51, 44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![9, 8, 3, 6, 13, 12, 7, 2, 5, 4, 15, 10, 1, 0, 11, 14, 25, 24, 19, 22, 29, 28, 23, 18, 21, 20, 31, 26, 17, 16, 27, 30, 45, 44, 39, 34, 41, 40, 35, 38, 33, 32, 43, 46, 37, 36, 47, 42, 61, 60, 55, 50, 57, 56, 51, 54, 49, 48, 59, 62, 53, 52, 63, 58], ![58, 11, 44, 9, 62, 15, 40, 13, 38, 23, 48, 21, 34, 19, 52, 17, 42, 27, 60, 25, 46, 31, 56, 29, 54, 7, 32, 5, 50, 3, 36, 1, 14, 63, 24, 61, 10, 59, 28, 57, 18, 35, 4, 33, 22, 39, 0, 37, 30, 47, 8, 45, 26, 43, 12, 41, 2, 51, 20, 49, 6, 55, 16, 53], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51, 44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

namespace Mask10

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![46, 57, 30, 13, 52, 43, 40, 63, 28, 15, 58, 37, 2, 25, 8, 19, 62, 41, 14, 29, 36, 59, 56, 47, 12, 31, 42, 53, 18, 9, 24, 3, 38, 61, 44, 55, 10, 21, 50, 33, 16, 7, 4, 27, 48, 35, 22, 1, 54, 45, 60, 39, 26, 5, 34, 49, 0, 23, 20, 11, 32, 51, 6, 17], ![25, 18, 23, 16, 31, 28, 19, 24, 17, 22, 29, 30, 27, 20, 21, 26, 9, 2, 7, 0, 15, 12, 3, 8, 1, 6, 13, 14, 11, 4, 5, 10, 63, 56, 57, 62, 61, 54, 59, 52, 51, 48, 55, 60, 53, 58, 49, 50, 47, 40, 41, 46, 45, 38, 43, 36, 35, 32, 39, 44, 37, 42, 33, 34], ![7, 6, 9, 8, 11, 10, 1, 0, 3, 2, 5, 4, 15, 14, 13, 12, 23, 22, 25, 24, 27, 26, 17, 16, 19, 18, 21, 20, 31, 30, 29, 28, 35, 34, 33, 32, 43, 42, 45, 44, 47, 46, 37, 36, 39, 38, 41, 40, 51, 50, 49, 48, 59, 58, 61, 60, 63, 62, 53, 52, 55, 54, 57, 56], ![6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 14, 15, 12, 13, 22, 23, 24, 25, 26, 27, 16, 17, 18, 19, 20, 21, 30, 31, 28, 29, 34, 35, 32, 33, 42, 43, 44, 45, 46, 47, 36, 37, 38, 39, 40, 41, 50, 51, 48, 49, 58, 59, 60, 61, 62, 63, 52, 53, 54, 55, 56, 57], ![4, 27, 48, 35, 22, 1, 10, 21, 50, 33, 16, 7, 44, 55, 38, 61, 20, 11, 32, 51, 6, 17, 26, 5, 34, 49, 0, 23, 60, 39, 54, 45, 8, 19, 2, 25, 40, 63, 28, 15, 58, 37, 46, 57, 30, 13, 52, 43, 24, 3, 18, 9, 56, 47, 12, 31, 42, 53, 62, 41, 14, 29, 36, 59], ![19, 24, 17, 22, 29, 30, 25, 18, 23, 16, 31, 28, 21, 26, 27, 20, 3, 8, 1, 6, 13, 14, 9, 2, 7, 0, 15, 12, 5, 10, 11, 4, 57, 62, 63, 56, 55, 60, 53, 58, 49, 50, 61, 54, 59, 52, 51, 48, 41, 46, 47, 40, 39, 44, 37, 42, 33, 34, 45, 38, 43, 36, 35, 32]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask10

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![9, 12, 3, 2, 13, 8, 7, 6, 5, 0, 15, 14, 1, 4, 11, 10, 25, 28, 19, 18, 29, 24, 23, 22, 21, 16, 31, 30, 17, 20, 27, 26, 45, 40, 39, 38, 41, 44, 35, 34, 33, 36, 43, 42, 37, 32, 47, 46, 61, 56, 55, 54, 57, 60, 51, 50, 49, 52, 59, 58, 53, 48, 63, 62], ![46, 11, 56, 9, 42, 15, 60, 13, 50, 23, 36, 21, 54, 19, 32, 17, 62, 27, 40, 25, 58, 31, 44, 29, 34, 7, 52, 5, 38, 3, 48, 1, 26, 63, 12, 61, 30, 59, 8, 57, 6, 35, 16, 33, 2, 39, 20, 37, 10, 47, 28, 45, 14, 43, 24, 41, 22, 51, 0, 49, 18, 55, 4, 53], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51, 44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![13, 8, 7, 6, 9, 12, 3, 2, 1, 4, 11, 10, 5, 0, 15, 14, 29, 24, 23, 22, 25, 28, 19, 18, 17, 20, 27, 26, 21, 16, 31, 30, 41, 44, 35, 34, 45, 40, 39, 38, 37, 32, 47, 46, 33, 36, 43, 42, 57, 60, 51, 50, 61, 56, 55, 54, 53, 48, 63, 62, 49, 52, 59, 58], ![58, 31, 44, 29, 62, 27, 40, 25, 38, 3, 48, 1, 34, 7, 52, 5, 42, 15, 60, 13, 46, 11, 56, 9, 54, 19, 32, 17, 50, 23, 36, 21, 14, 43, 24, 41, 10, 47, 28, 45, 18, 55, 4, 53, 22, 51, 0, 49, 30, 59, 8, 57, 26, 63, 12, 61, 2, 39, 20, 37, 6, 35, 16, 33], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51, 44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask11

namespace Mask12

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![11, 4, 5, 10, 3, 0, 15, 8, 13, 6, 1, 2, 9, 14, 7, 12, 27, 20, 21, 26, 19, 16, 31, 24, 29, 22, 17, 18, 25, 30, 23, 28, 47, 44, 43, 36, 41, 34, 45, 46, 37, 42, 35, 40, 39, 32, 33, 38, 63, 60, 59, 52, 57, 50, 61, 62, 53, 58, 51, 56, 55, 48, 49, 54], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![40, 51, 34, 57, 30, 9, 60, 47, 4, 27, 24, 15, 62, 45, 10, 21, 56, 35, 50, 41, 14, 25, 44, 63, 20, 11, 8, 31, 46, 61, 26, 5, 58, 37, 16, 3, 32, 55, 52, 43, 18, 1, 38, 49, 12, 23, 6, 29, 42, 53, 0, 19, 48, 39, 36, 59, 2, 17, 54, 33, 28, 7, 22, 13], ![19, 18, 17, 16, 27, 26, 29, 28, 31, 30, 21, 20, 23, 22, 25, 24, 3, 2, 1, 0, 11, 10, 13, 12, 15, 14, 5, 4, 7, 6, 9, 8, 55, 54, 57, 56, 59, 58, 49, 48, 51, 50, 53, 52, 63, 62, 61, 60, 39, 38, 41, 40, 43, 42, 33, 32, 35, 34, 37, 36, 47, 46, 45, 44], ![33, 38, 39, 32, 45, 46, 37, 42, 35, 40, 47, 44, 43, 36, 41, 34, 49, 54, 55, 48, 61, 62, 53, 58, 51, 56, 63, 60, 59, 52, 57, 50, 1, 2, 9, 14, 7, 12, 3, 0, 15, 8, 13, 6, 5, 10, 11, 4, 17, 18, 25, 30, 23, 28, 19, 16, 31, 24, 29, 22, 21, 26, 27, 20], ![18, 19, 16, 17, 26, 27, 28, 29, 30, 31, 20, 21, 22, 23, 24, 25, 2, 3, 0, 1, 10, 11, 12, 13, 14, 15, 4, 5, 6, 7, 8, 9, 54, 55, 56, 57, 58, 59, 48, 49, 50, 51, 52, 53, 62, 63, 60, 61, 38, 39, 40, 41, 42, 43, 32, 33, 34, 35, 36, 37, 46, 47, 44, 45], ![50, 41, 56, 35, 8, 31, 46, 61, 26, 5, 14, 25, 44, 63, 20, 11, 34, 57, 40, 51, 24, 15, 62, 45, 10, 21, 30, 9, 60, 47, 4, 27, 36, 59, 2, 17, 54, 33, 42, 53, 0, 19, 48, 39, 22, 13, 28, 7, 52, 43, 18, 1, 38, 49, 58, 37, 16, 3, 32, 55, 6, 29, 12, 23]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask12

namespace Mask13

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![13, 12, 3, 6, 9, 8, 7, 2, 1, 0, 15, 10, 5, 4, 11, 14, 29, 28, 19, 22, 25, 24, 23, 18, 17, 16, 31, 26, 21, 20, 27, 30, 41, 40, 39, 34, 45, 44, 35, 38, 37, 36, 43, 46, 33, 32, 47, 42, 57, 56, 55, 50, 61, 60, 51, 54, 53, 52, 59, 62, 49, 48, 63, 58], ![58, 11, 56, 29, 62, 15, 60, 25, 38, 23, 36, 1, 34, 19, 32, 5, 42, 27, 40, 13, 46, 31, 44, 9, 54, 7, 52, 17, 50, 3, 48, 21, 14, 63, 12, 41, 10, 59, 8, 45, 18, 35, 16, 53, 22, 39, 20, 49, 30, 47, 28, 57, 26, 43, 24, 61, 2, 51, 0, 37, 6, 55, 4, 33], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51, 44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![9, 8, 7, 2, 13, 12, 3, 6, 5, 4, 11, 14, 1, 0, 15, 10, 25, 24, 23, 18, 29, 28, 19, 22, 21, 20, 27, 30, 17, 16, 31, 26, 45, 44, 35, 38, 41, 40, 39, 34, 33, 32, 47, 42, 37, 36, 43, 46, 61, 60, 51, 54, 57, 56, 55, 50, 49, 48, 63, 58, 53, 52, 59, 62], ![46, 31, 44, 9, 42, 27, 40, 13, 50, 3, 48, 21, 54, 7, 52, 17, 62, 15, 60, 25, 58, 11, 56, 29, 34, 19, 32, 5, 38, 23, 36, 1, 26, 43, 24, 61, 30, 47, 28, 57, 6, 55, 4, 33, 2, 51, 0, 37, 10, 59, 8, 45, 14, 63, 12, 41, 22, 39, 20, 49, 18, 35, 16, 53], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51, 44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask13

namespace Mask14

private def generators : Fin 8 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![5, 20, 49, 32, 43, 58, 11, 26, 51, 34, 37, 52, 25, 8, 19, 2, 21, 4, 33, 48, 59, 42, 27, 10, 35, 50, 53, 36, 9, 24, 3, 18, 61, 44, 55, 38, 41, 56, 29, 12, 7, 22, 47, 62, 31, 14, 1, 16, 45, 60, 39, 54, 57, 40, 13, 28, 23, 6, 63, 46, 15, 30, 17, 0], ![25, 18, 23, 16, 31, 28, 19, 24, 17, 22, 29, 30, 27, 20, 21, 26, 9, 2, 7, 0, 15, 12, 3, 8, 1, 6, 13, 14, 11, 4, 5, 10, 63, 56, 57, 62, 61, 54, 59, 52, 51, 48, 55, 60, 53, 58, 49, 50, 47, 40, 41, 46, 45, 38, 43, 36, 35, 32, 39, 44, 37, 42, 33, 34], ![7, 6, 9, 8, 11, 10, 1, 0, 3, 2, 5, 4, 15, 14, 13, 12, 23, 22, 25, 24, 27, 26, 17, 16, 19, 18, 21, 20, 31, 30, 29, 28, 35, 34, 33, 32, 43, 42, 45, 44, 47, 46, 37, 36, 39, 38, 41, 40, 51, 50, 49, 48, 59, 58, 61, 60, 63, 62, 53, 52, 55, 54, 57, 56], ![6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 14, 15, 12, 13, 22, 23, 24, 25, 26, 27, 16, 17, 18, 19, 20, 21, 30, 31, 28, 29, 34, 35, 32, 33, 42, 43, 44, 45, 46, 47, 36, 37, 38, 39, 40, 41, 50, 51, 48, 49, 58, 59, 60, 61, 62, 63, 52, 53, 54, 55, 56, 57], ![41, 56, 29, 12, 7, 22, 47, 62, 31, 14, 1, 16, 61, 44, 55, 38, 57, 40, 13, 28, 23, 6, 63, 46, 15, 30, 17, 0, 45, 60, 39, 54, 25, 8, 19, 2, 5, 20, 49, 32, 43, 58, 11, 26, 51, 34, 37, 52, 9, 24, 3, 18, 21, 4, 33, 48, 59, 42, 27, 10, 35, 50, 53, 36], ![19, 24, 17, 22, 29, 30, 25, 18, 23, 16, 31, 28, 21, 26, 27, 20, 3, 8, 1, 6, 13, 14, 9, 2, 7, 0, 15, 12, 5, 10, 11, 4, 57, 62, 63, 56, 55, 60, 53, 58, 49, 50, 61, 54, 59, 52, 51, 48, 41, 46, 47, 40, 39, 44, 37, 42, 33, 34, 45, 38, 43, 36, 35, 32]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask14

namespace Mask15

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 64 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 8 → Fin 64 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![9, 12, 7, 6, 13, 8, 3, 2, 5, 0, 11, 10, 1, 4, 15, 14, 25, 28, 23, 22, 29, 24, 19, 18, 21, 16, 27, 26, 17, 20, 31, 30, 45, 40, 35, 34, 41, 44, 39, 38, 33, 36, 47, 46, 37, 32, 43, 42, 61, 56, 51, 50, 57, 60, 55, 54, 49, 52, 63, 62, 53, 48, 59, 58], ![58, 31, 56, 9, 62, 27, 60, 13, 38, 3, 36, 21, 34, 7, 32, 17, 42, 15, 40, 25, 46, 11, 44, 29, 54, 19, 52, 5, 50, 23, 48, 1, 14, 43, 12, 61, 10, 47, 8, 57, 18, 55, 16, 33, 22, 51, 20, 37, 30, 59, 28, 45, 26, 63, 24, 41, 2, 39, 0, 49, 6, 35, 4, 53], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51, 44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], ![13, 8, 3, 2, 9, 12, 7, 6, 1, 4, 15, 14, 5, 0, 11, 10, 29, 24, 19, 18, 25, 28, 23, 22, 17, 20, 31, 30, 21, 16, 27, 26, 41, 44, 39, 38, 45, 40, 35, 34, 37, 32, 43, 42, 33, 36, 47, 46, 57, 60, 55, 54, 61, 56, 51, 50, 53, 48, 59, 58, 49, 52, 63, 62], ![46, 11, 44, 29, 42, 15, 40, 25, 50, 23, 48, 1, 54, 19, 52, 5, 62, 27, 60, 13, 58, 31, 56, 9, 34, 7, 32, 17, 38, 3, 36, 21, 26, 63, 24, 41, 30, 59, 28, 45, 6, 35, 4, 53, 2, 39, 0, 49, 10, 47, 8, 57, 14, 43, 12, 61, 22, 51, 20, 37, 18, 55, 16, 33], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51, 44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 119) :
    Classified H := classify separation_checked H hH

end Node119

end ReeTwo.SylowModel.SmallEvenMaximalLower
