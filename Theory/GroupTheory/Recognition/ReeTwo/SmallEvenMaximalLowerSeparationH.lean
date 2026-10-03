module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerWordsH
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperCoordinates

/-!+# Nonmembership certificates for lower even maximal subgroups, batch H

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

namespace Node175

namespace Mask1

private def generators : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 4 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![6, 5, 4, 7, 0, 3, 2, 1], ![7, 6, 5, 4, 3, 2, 1, 0], ![3, 0, 1, 2, 5, 6, 7, 4]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 2 → Bool := fun k => (1 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask1

public theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ m : Fin 4,
      (branches (fun k => m.val.testBit k.val)).Separation gen
        (fun k => m.val.testBit k.val) (pivot (fun k => m.val.testBit k.val)) := by
    intro m
    fin_cases m
    · trivial
    · exact Mask1.not_mem
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 2 → Bool),
      σ = fun k => (signatureIndex σ % 4).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 175) :
    Classified H := classify separation_checked H hH

end Node175

namespace Node176

namespace Mask1

private def generators : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 4 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![3, 0, 1, 2, 5, 6, 7, 4], ![7, 6, 5, 4, 3, 2, 1, 0], ![6, 5, 4, 7, 0, 3, 2, 1]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 2 → Bool := fun k => (1 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask1

public theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ m : Fin 4,
      (branches (fun k => m.val.testBit k.val)).Separation gen
        (fun k => m.val.testBit k.val) (pivot (fun k => m.val.testBit k.val)) := by
    intro m
    fin_cases m
    · trivial
    · exact Mask1.not_mem
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 2 → Bool),
      σ = fun k => (signatureIndex σ % 4).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 176) :
    Classified H := classify separation_checked H hH

end Node176

namespace Node177

namespace Mask2

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![6, 5, 4, 7, 0, 3, 2, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![6, 5, 4, 7, 0, 3, 2, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (2 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask2

namespace Mask3

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 2, 3, 0, 7, 4, 5, 6], ![7, 6, 5, 4, 3, 2, 1, 0], ![2, 3, 0, 1, 6, 7, 4, 5], ![3, 0, 1, 2, 5, 6, 7, 4], ![7, 6, 5, 4, 3, 2, 1, 0]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 3 → Bool := fun k => (3 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask3

namespace Mask6

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![6, 7, 4, 5, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4], ![6, 7, 4, 5, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4]]
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
    trunc 7 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 4, 7, 2, 5, 0, 3, 6], ![6, 3, 0, 5, 2, 7, 4, 1], ![4, 5, 6, 7, 0, 1, 2, 3], ![5, 0, 3, 6, 1, 4, 7, 2], ![2, 7, 4, 1, 6, 3, 0, 5]]
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
    trunc 7 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 96 ∉
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
    · exact Mask2.not_mem
    · exact Mask3.not_mem
    · trivial
    · trivial
    · exact Mask6.not_mem
    · exact Mask7.not_mem
  have hs : ∀ (σ : Fin 3 → Bool),
      σ = fun k => (signatureIndex σ % 8).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 177) :
    Classified H := classify separation_checked H hH

end Node177

namespace Node178

namespace Mask3

private def generators : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 4 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 2, 3, 0, 1], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 2 → Bool := fun k => (3 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
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
    · trivial
    · exact Mask3.not_mem
  have hs : ∀ (σ : Fin 2 → Bool),
      σ = fun k => (signatureIndex σ % 4).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 178) :
    Classified H := classify separation_checked H hH

end Node178

namespace Node179

namespace Mask3

private def generators : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 4 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 4, 7, 2, 5, 0, 3, 6], ![3, 2, 1, 0, 7, 6, 5, 4], ![5, 0, 3, 6, 1, 4, 7, 2]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 2 → Bool := fun k => (3 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
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
    · trivial
    · exact Mask3.not_mem
  have hs : ∀ (σ : Fin 2 → Bool),
      σ = fun k => (signatureIndex σ % 4).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 179) :
    Classified H := classify separation_checked H hH

end Node179

namespace Node182

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![9, 8, 11, 10, 1, 0, 3, 2, 13, 12, 15, 14, 5, 4, 7, 6], ![6, 7, 4, 5, 0, 1, 2, 3, 12, 13, 14, 15, 10, 11, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![9, 8, 11, 10, 1, 0, 3, 2, 13, 12, 15, 14, 5, 4, 7, 6], ![6, 7, 4, 5, 0, 1, 2, 3, 12, 13, 14, 15, 10, 11, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
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
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![6, 5, 4, 7, 0, 3, 2, 1, 12, 15, 14, 13, 10, 9, 8, 11], ![13, 0, 15, 2, 5, 8, 7, 10, 9, 4, 11, 6, 1, 12, 3, 14], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 11, 10, 9, 14, 13, 12, 15, 2, 1, 0, 3, 4, 7, 6, 5], ![1, 12, 3, 14, 9, 4, 11, 6, 5, 8, 7, 10, 13, 0, 15, 2]]
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
  ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![8, 5, 10, 7, 0, 13, 2, 15, 12, 1, 14, 3, 4, 9, 6, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![13, 14, 15, 12, 11, 8, 9, 10, 7, 4, 5, 6, 1, 2, 3, 0], ![6, 11, 4, 9, 14, 3, 12, 1, 2, 15, 0, 13, 10, 7, 8, 5], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![15, 12, 13, 14, 9, 10, 11, 8, 5, 6, 7, 4, 3, 0, 1, 2]]
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
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![3, 14, 13, 0, 7, 10, 9, 4, 11, 6, 5, 8, 15, 2, 1, 12], ![10, 3, 0, 9, 14, 7, 4, 13, 2, 11, 8, 1, 6, 15, 12, 5], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![7, 10, 9, 4, 3, 14, 13, 0, 15, 2, 1, 12, 11, 6, 5, 8], ![2, 11, 8, 1, 6, 15, 12, 5, 10, 3, 0, 9, 14, 7, 4, 13]]
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
    trunc 8 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 64 ∉
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 182) :
    Classified H := classify separation_checked H hH

end Node182

namespace Node183

namespace Mask4

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![9, 4, 11, 6, 13, 0, 15, 2, 1, 12, 3, 14, 5, 8, 7, 10], ![7, 12, 5, 14, 3, 8, 1, 10, 15, 4, 13, 6, 11, 0, 9, 2], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![9, 4, 11, 6, 13, 0, 15, 2, 1, 12, 3, 14, 5, 8, 7, 10], ![7, 12, 5, 14, 3, 8, 1, 10, 15, 4, 13, 6, 11, 0, 9, 2], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask5

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![7, 6, 13, 12, 3, 2, 9, 8, 15, 14, 5, 4, 11, 10, 1, 0], ![10, 11, 4, 5, 14, 15, 0, 1, 2, 3, 12, 13, 6, 7, 8, 9], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![3, 2, 9, 8, 7, 6, 13, 12, 11, 10, 1, 0, 15, 14, 5, 4], ![6, 7, 8, 9, 2, 3, 12, 13, 14, 15, 0, 1, 10, 11, 4, 5]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask5

namespace Mask6

private def generators : Fin 6 → E :=
  ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![8, 9, 6, 7, 0, 1, 14, 15, 12, 13, 2, 3, 4, 5, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![3, 2, 11, 10, 13, 12, 5, 4, 1, 0, 9, 8, 15, 14, 7, 6], ![14, 15, 0, 1, 6, 7, 8, 9, 10, 11, 4, 5, 2, 3, 12, 13], ![10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5], ![9, 8, 1, 0, 7, 6, 15, 14, 11, 10, 3, 2, 5, 4, 13, 12]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 8 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

namespace Mask7

private def generators : Fin 6 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 15, 10, 13, 12, 11, 14, 9, 0, 7, 2, 5, 4, 3, 6, 1], ![11, 6, 9, 4, 15, 2, 13, 0, 3, 14, 1, 12, 7, 10, 5, 8], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![2, 5, 0, 7, 6, 1, 4, 3, 10, 13, 8, 15, 14, 9, 12, 11], ![7, 10, 5, 8, 3, 14, 1, 12, 15, 2, 13, 0, 11, 6, 9, 4]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 128 ∉
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 183) :
    Classified H := classify separation_checked H hH

end Node183

namespace Node184

namespace Mask2

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![5, 4, 7, 6, 1, 0, 3, 2], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![5, 4, 7, 6, 1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask2

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4]]
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

namespace Mask7

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1], ![1, 0, 3, 2, 5, 4, 7, 6], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1], ![1, 0, 3, 2, 5, 4, 7, 6], ![3, 2, 1, 0, 7, 6, 5, 4]]
private def witness : E := (⟨0, 0, 1, 1, 0, 1, 0, 1, 1, 1⟩, 1)
private def signature : Fin 4 → Bool := fun k => (7 : Nat).testBit k.val

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

end Mask7

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7]]
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

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![3, 2, 1, 0, 7, 6, 5, 4], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![3, 2, 1, 0, 7, 6, 5, 4], ![1, 0, 3, 2, 5, 4, 7, 6]]
private def witness : E := (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1)
private def signature : Fin 4 → Bool := fun k => (9 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 2068 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

namespace Mask12

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (12 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 8 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask12

namespace Mask13

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 4 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask13

namespace Mask14

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 1)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![0, 1, 2, 3], ![3, 2, 1, 0], ![3, 2, 1, 0], ![1, 0, 3, 2], ![0, 1, 2, 3], ![3, 2, 1, 0], ![3, 2, 1, 0]]
private def witness : E := (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (14 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 104 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask14

namespace Mask15

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 36 ∉
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
    · exact Mask2.not_mem
    · trivial
    · exact Mask4.not_mem
    · trivial
    · trivial
    · exact Mask7.not_mem
    · exact Mask8.not_mem
    · exact Mask9.not_mem
    · trivial
    · trivial
    · exact Mask12.not_mem
    · exact Mask13.not_mem
    · exact Mask14.not_mem
    · exact Mask15.not_mem
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 184) :
    Classified H := classify separation_checked H hH

end Node184

namespace Node185

namespace Mask2

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![5, 4, 7, 6, 1, 0, 3, 2], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![5, 4, 7, 6, 1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask2

namespace Mask13

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 4 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask13

namespace Mask15

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 1⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 36 ∉
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
    · exact Mask2.not_mem
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
    · exact Mask13.not_mem
    · trivial
    · exact Mask15.not_mem
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 185) :
    Classified H := classify separation_checked H hH

end Node185

namespace Node186

namespace Mask2

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![5, 4, 7, 6, 1, 0, 3, 2], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![5, 4, 7, 6, 1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask2

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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 186) :
    Classified H := classify separation_checked H hH

end Node186

namespace Node187

namespace Mask2

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![5, 4, 7, 6, 1, 0, 3, 2], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![5, 4, 7, 6, 1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask2

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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 187) :
    Classified H := classify separation_checked H hH

end Node187

namespace Node188

namespace Mask2

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![3, 2, 1, 0], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![3, 2, 1, 0]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (2 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask2

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)
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

theorem not_mem : Collected.decode 2056 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask8

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3]]
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
    trunc 5 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 4 ∉
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
    · exact Mask2.not_mem
    · trivial
    · exact Mask4.not_mem
    · trivial
    · trivial
    · trivial
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 188) :
    Classified H := classify separation_checked H hH

end Node188

namespace Node189

namespace Mask2

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3], ![3, 2, 1, 0], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3], ![3, 2, 1, 0]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (2 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask2

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4]]
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
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3]]
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
    trunc 5 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 16 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask8

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 36 ∉
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
    · exact Mask2.not_mem
    · trivial
    · exact Mask4.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 189) :
    Classified H := classify separation_checked H hH

end Node189

namespace Node190

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)
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

theorem not_mem : Collected.decode 2056 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask15

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![3, 2, 1, 0, 7, 6, 5, 4]]
private def witness : E := (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 36 ∉
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
    · exact Mask4.not_mem
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
    · exact Mask15.not_mem
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 190) :
    Classified H := classify separation_checked H hH

end Node190

namespace Node191

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4]]
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

namespace Mask13

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 4 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
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
    · exact Mask4.not_mem
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact Mask13.not_mem
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 191) :
    Classified H := classify separation_checked H hH

end Node191

namespace Node192

namespace Mask2

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4], ![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4], ![4, 5, 6, 7, 0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask2

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3]]
private def witness : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 8 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 5 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

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
    · exact Mask4.not_mem
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
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 192) :
    Classified H := classify separation_checked H hH

end Node192

namespace Node193

namespace Mask2

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![3, 2, 1, 0], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![3, 2, 1, 0]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (2 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask2

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 4 ∉
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
    · exact Mask2.not_mem
    · trivial
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 193) :
    Classified H := classify separation_checked H hH

end Node193

namespace Node194

namespace Mask2

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3], ![3, 2, 1, 0], ![2, 3, 0, 1], ![0, 1, 2, 3], ![0, 1, 2, 3], ![3, 2, 1, 0]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (2 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask2

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![3, 2, 1, 0], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3], ![3, 2, 1, 0], ![0, 1, 2, 3], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 36 ∉
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
    · exact Mask2.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 194) :
    Classified H := classify separation_checked H hH

end Node194

namespace Node195

namespace Mask13

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 1, 1⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![3, 2, 1, 0, 7, 6, 5, 4]]
private def witness : E := (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 36 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
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
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact Mask13.not_mem
    · trivial
    · trivial
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 195) :
    Classified H := classify separation_checked H hH

end Node195

namespace Node196

namespace Mask15

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 4 ∉
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
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact Mask15.not_mem
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 196) :
    Classified H := classify separation_checked H hH

end Node196

namespace Node197

namespace Mask3

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 2 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 2 → Fin 2 :=
  ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![1, 0], ![0, 1], ![0, 1]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)
private def signature : Fin 4 → Bool := fun k => (3 : Nat).testBit k.val

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

theorem not_mem : Collected.decode 4 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 3 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask3

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 4 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask6

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1], ![1, 0, 3, 2, 5, 4, 7, 6]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 4 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

namespace Mask9

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 4 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask9

namespace Mask11

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0)]
private def representatives : Fin 4 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3], ![2, 3, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 4 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 6 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask11

namespace Mask12

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 4 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask12

namespace Mask14

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 1)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1], ![5, 4, 7, 6, 1, 0, 3, 2], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1], ![5, 4, 7, 6, 1, 0, 3, 2]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 4 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask14

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
    · exact Mask4.not_mem
    · trivial
    · exact Mask6.not_mem
    · trivial
    · trivial
    · exact Mask9.not_mem
    · trivial
    · exact Mask11.not_mem
    · exact Mask12.not_mem
    · trivial
    · exact Mask14.not_mem
    · trivial
  have hs : ∀ (σ : Fin 4 → Bool),
      σ = fun k => (signatureIndex σ % 16).testBit k.val := by decide +kernel
  intro σ _
  simpa only [← hs σ] using h ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 197) :
    Classified H := classify separation_checked H hH

end Node197

namespace Node198

namespace Mask2

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5]]
private def witness : E := (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 96 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask2

namespace Mask4

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6]]
private def witness : E := (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 4 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask4

namespace Mask6

private def generators : Fin 8 → E :=
  ![(⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6]]
private def witness : E := (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0)
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

theorem not_mem : Collected.decode 36 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 7 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask6

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
    · exact Mask4.not_mem
    · trivial
    · exact Mask6.not_mem
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 198) :
    Classified H := classify separation_checked H hH

end Node198

namespace Node199

namespace Mask4

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![7, 4, 5, 6, 3, 0, 1, 2], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![7, 4, 5, 6, 3, 0, 1, 2], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (4 : Nat).testBit k.val

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

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![7, 6, 5, 4, 1, 0, 3, 2], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 3, 2, 1, 0], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (5 : Nat).testBit k.val

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

end Mask5

namespace Mask6

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 8 → Fin 8 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 6, 1, 4, 7, 2, 5, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![5, 4, 7, 6, 1, 0, 3, 2], ![4, 5, 6, 7, 0, 1, 2, 3], ![7, 2, 5, 0, 3, 6, 1, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (6 : Nat).testBit k.val

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

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 8 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![5, 6, 7, 4, 3, 0, 1, 2], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![7, 4, 5, 6, 1, 2, 3, 0], ![4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (7 : Nat).testBit k.val

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

end Mask7

namespace Mask8

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![7, 4, 5, 6, 3, 0, 1, 2, 15, 12, 13, 14, 11, 8, 9, 10], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![7, 4, 5, 6, 3, 0, 1, 2, 15, 12, 13, 14, 11, 8, 9, 10], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (8 : Nat).testBit k.val

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

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![7, 6, 5, 4, 1, 0, 3, 2, 13, 12, 15, 14, 11, 10, 9, 8], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![5, 4, 7, 6, 3, 2, 1, 0, 15, 14, 13, 12, 9, 8, 11, 10], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (9 : Nat).testBit k.val

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

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![11, 14, 9, 12, 15, 10, 13, 8, 3, 6, 1, 4, 7, 2, 5, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![15, 10, 13, 8, 11, 14, 9, 12, 7, 2, 5, 0, 3, 6, 1, 4], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (10 : Nat).testBit k.val

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

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![5, 6, 7, 4, 3, 0, 1, 2, 15, 12, 13, 14, 9, 10, 11, 8], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![7, 4, 5, 6, 1, 2, 3, 0, 13, 14, 15, 12, 11, 8, 9, 10], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (11 : Nat).testBit k.val

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

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![15, 10, 13, 8, 11, 14, 9, 12, 7, 2, 5, 0, 3, 6, 1, 4], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![15, 10, 13, 8, 11, 14, 9, 12, 7, 2, 5, 0, 3, 6, 1, 4], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (12 : Nat).testBit k.val

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

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![7, 4, 5, 6, 3, 0, 1, 2, 13, 14, 15, 12, 9, 10, 11, 8], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![5, 6, 7, 4, 1, 2, 3, 0, 15, 12, 13, 14, 11, 8, 9, 10], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (13 : Nat).testBit k.val

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

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![9, 10, 11, 8, 13, 14, 15, 12, 1, 2, 3, 0, 5, 6, 7, 4], ![13, 14, 15, 12, 9, 10, 11, 8, 5, 6, 7, 4, 1, 2, 3, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![11, 8, 9, 10, 15, 12, 13, 14, 3, 0, 1, 2, 7, 4, 5, 6], ![15, 12, 13, 14, 11, 8, 9, 10, 7, 4, 5, 6, 3, 0, 1, 2], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (14 : Nat).testBit k.val

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

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0)]
private def representatives : Fin 16 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![5, 4, 7, 6, 1, 0, 3, 2, 15, 14, 13, 12, 11, 10, 9, 8], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![7, 6, 5, 4, 3, 2, 1, 0, 13, 12, 15, 14, 9, 8, 11, 10], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (15 : Nat).testBit k.val

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

namespace Mask16

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![7, 4, 5, 6, 3, 0, 1, 2, 15, 12, 13, 14, 11, 8, 9, 10, 23, 20, 21, 22, 19, 16, 17, 18, 31, 28, 29, 30, 27, 24, 25, 26], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![7, 4, 5, 6, 3, 0, 1, 2, 15, 12, 13, 14, 11, 8, 9, 10, 23, 20, 21, 22, 19, 16, 17, 18, 31, 28, 29, 30, 27, 24, 25, 26], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (16 : Nat).testBit k.val

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

end Mask16

namespace Mask17

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![7, 6, 5, 4, 1, 0, 3, 2, 15, 14, 13, 12, 9, 8, 11, 10, 21, 20, 23, 22, 19, 18, 17, 16, 29, 28, 31, 30, 27, 26, 25, 24], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![5, 4, 7, 6, 3, 2, 1, 0, 13, 12, 15, 14, 11, 10, 9, 8, 23, 22, 21, 20, 17, 16, 19, 18, 31, 30, 29, 28, 25, 24, 27, 26], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (17 : Nat).testBit k.val

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

end Mask17

namespace Mask18

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![19, 22, 17, 20, 23, 18, 21, 16, 27, 30, 25, 28, 31, 26, 29, 24, 3, 6, 1, 4, 7, 2, 5, 0, 11, 14, 9, 12, 15, 10, 13, 8], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 29, 28, 31, 30, 25, 24, 27, 26], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![23, 18, 21, 16, 19, 22, 17, 20, 31, 26, 29, 24, 27, 30, 25, 28, 7, 2, 5, 0, 3, 6, 1, 4, 15, 10, 13, 8, 11, 14, 9, 12]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (18 : Nat).testBit k.val

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

end Mask18

namespace Mask19

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![5, 6, 7, 4, 3, 0, 1, 2, 13, 14, 15, 12, 11, 8, 9, 10, 23, 20, 21, 22, 17, 18, 19, 16, 31, 28, 29, 30, 25, 26, 27, 24], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![7, 4, 5, 6, 1, 2, 3, 0, 15, 12, 13, 14, 9, 10, 11, 8, 21, 22, 23, 20, 19, 16, 17, 18, 29, 30, 31, 28, 27, 24, 25, 26], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (19 : Nat).testBit k.val

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

end Mask19

namespace Mask24

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![15, 10, 13, 8, 11, 14, 9, 12, 7, 2, 5, 0, 3, 6, 1, 4, 31, 26, 29, 24, 27, 30, 25, 28, 23, 18, 21, 16, 19, 22, 17, 20], ![24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![15, 10, 13, 8, 11, 14, 9, 12, 7, 2, 5, 0, 3, 6, 1, 4, 31, 26, 29, 24, 27, 30, 25, 28, 23, 18, 21, 16, 19, 22, 17, 20], ![24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
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
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask24

namespace Mask25

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![7, 4, 5, 6, 3, 0, 1, 2, 13, 14, 15, 12, 9, 10, 11, 8, 21, 22, 23, 20, 17, 18, 19, 16, 31, 28, 29, 30, 27, 24, 25, 26], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![5, 6, 7, 4, 1, 2, 3, 0, 15, 12, 13, 14, 11, 8, 9, 10, 23, 20, 21, 22, 19, 16, 17, 18, 29, 30, 31, 28, 25, 26, 27, 24], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
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
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask25

namespace Mask26

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![13, 14, 15, 12, 9, 10, 11, 8, 5, 6, 7, 4, 1, 2, 3, 0, 29, 30, 31, 28, 25, 26, 27, 24, 21, 22, 23, 20, 17, 18, 19, 16], ![21, 22, 23, 20, 17, 18, 19, 16, 29, 30, 31, 28, 25, 26, 27, 24, 5, 6, 7, 4, 1, 2, 3, 0, 13, 14, 15, 12, 9, 10, 11, 8], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![15, 12, 13, 14, 11, 8, 9, 10, 7, 4, 5, 6, 3, 0, 1, 2, 31, 28, 29, 30, 27, 24, 25, 26, 23, 20, 21, 22, 19, 16, 17, 18], ![23, 20, 21, 22, 19, 16, 17, 18, 31, 28, 29, 30, 27, 24, 25, 26, 7, 4, 5, 6, 3, 0, 1, 2, 15, 12, 13, 14, 11, 8, 9, 10]]
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
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask26

namespace Mask27

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![5, 4, 7, 6, 1, 0, 3, 2, 15, 14, 13, 12, 11, 10, 9, 8, 23, 22, 21, 20, 19, 18, 17, 16, 29, 28, 31, 30, 25, 24, 27, 26], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![7, 6, 5, 4, 3, 2, 1, 0, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 31, 30, 29, 28, 27, 26, 25, 24], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
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
    trunc 9 (mul (generators i) (representatives j)) = representatives (next i j) := by
  decide +kernel

theorem not_mem : Collected.decode 128 ∉
    Subgroup.closure (Set.range (schreier gen signature (pivot signature))) := by
  have h := outside_of_projected_orbit generators 9 representatives 0
    (by decide +kernel) next transitions_checked witness (by decide +kernel)
  rw [generators_eq] at h
  exact h

end Mask27

namespace Mask28

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![7, 4, 5, 6, 3, 0, 1, 2, 15, 12, 13, 14, 11, 8, 9, 10, 23, 20, 21, 22, 19, 16, 17, 18, 31, 28, 29, 30, 27, 24, 25, 26], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![7, 4, 5, 6, 3, 0, 1, 2, 15, 12, 13, 14, 11, 8, 9, 10, 23, 20, 21, 22, 19, 16, 17, 18, 31, 28, 29, 30, 27, 24, 25, 26], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (28 : Nat).testBit k.val

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

end Mask28

namespace Mask29

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![7, 6, 5, 4, 1, 0, 3, 2, 13, 12, 15, 14, 11, 10, 9, 8, 21, 20, 23, 22, 19, 18, 17, 16, 31, 30, 29, 28, 25, 24, 27, 26], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![5, 4, 7, 6, 3, 2, 1, 0, 15, 14, 13, 12, 9, 8, 11, 10, 23, 22, 21, 20, 17, 16, 19, 18, 29, 28, 31, 30, 27, 26, 25, 24], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (29 : Nat).testBit k.val

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

end Mask29

namespace Mask30

private def generators : Fin 10 → E :=
  ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![27, 30, 25, 28, 31, 26, 29, 24, 19, 22, 17, 20, 23, 18, 21, 16, 11, 14, 9, 12, 15, 10, 13, 8, 3, 6, 1, 4, 7, 2, 5, 0], ![11, 14, 9, 12, 15, 10, 13, 8, 3, 6, 1, 4, 7, 2, 5, 0, 27, 30, 25, 28, 31, 26, 29, 24, 19, 22, 17, 20, 23, 18, 21, 16], ![19, 22, 17, 20, 23, 18, 21, 16, 27, 30, 25, 28, 31, 26, 29, 24, 3, 6, 1, 4, 7, 2, 5, 0, 11, 14, 9, 12, 15, 10, 13, 8], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 29, 28, 31, 30, 25, 24, 27, 26], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![31, 26, 29, 24, 27, 30, 25, 28, 23, 18, 21, 16, 19, 22, 17, 20, 15, 10, 13, 8, 11, 14, 9, 12, 7, 2, 5, 0, 3, 6, 1, 4], ![15, 10, 13, 8, 11, 14, 9, 12, 7, 2, 5, 0, 3, 6, 1, 4, 31, 26, 29, 24, 27, 30, 25, 28, 23, 18, 21, 16, 19, 22, 17, 20], ![23, 18, 21, 16, 19, 22, 17, 20, 31, 26, 29, 24, 27, 30, 25, 28, 7, 2, 5, 0, 3, 6, 1, 4, 15, 10, 13, 8, 11, 14, 9, 12]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (30 : Nat).testBit k.val

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

end Mask30

namespace Mask31

private def generators : Fin 10 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0)]
private def representatives : Fin 32 → E :=
  ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 10 → Fin 32 → Fin 32 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![5, 6, 7, 4, 3, 0, 1, 2, 15, 12, 13, 14, 9, 10, 11, 8, 23, 20, 21, 22, 17, 18, 19, 16, 29, 30, 31, 28, 27, 24, 25, 26], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![7, 4, 5, 6, 1, 2, 3, 0, 13, 14, 15, 12, 11, 8, 9, 10, 21, 22, 23, 20, 19, 16, 17, 18, 31, 28, 29, 30, 25, 26, 27, 24], ![28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3], ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23], ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
private def witness : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def signature : Fin 5 → Bool := fun k => (31 : Nat).testBit k.val

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
    · exact Mask8.not_mem
    · exact Mask9.not_mem
    · exact Mask10.not_mem
    · exact Mask11.not_mem
    · exact Mask12.not_mem
    · exact Mask13.not_mem
    · exact Mask14.not_mem
    · exact Mask15.not_mem
    · exact Mask16.not_mem
    · exact Mask17.not_mem
    · exact Mask18.not_mem
    · exact Mask19.not_mem
    · trivial
    · trivial
    · trivial
    · trivial
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

public theorem classified (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 199) :
    Classified H := classify separation_checked H hH

end Node199

end ReeTwo.SylowModel.SmallEvenMaximalLower
