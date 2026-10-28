module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerGenerators

/-!+# Small even maximal-subgroup word witnesses

Reduced generating families and binary Schreier word equations retain the
original node and edge numbering. Each equation is checked by kernel reduction.
Noncentric branches additionally require the explicitly stated separation
certificate; no diagnostic subgroup membership is used as a proof.

Source: Shinoda (1975), (2.3), pp. 81–82, and the diagnostic input provenance
in `SmallEvenDescentEdgeData`. Witness search: `Scratch/small-even-maximal-lower`.
-/

@[expose] public section
namespace ReeTwo.SylowModel.SmallEvenMaximalLower
open Theory.GroupTheory.SubgroupEnumeration
open SmallEvenMaximalBranches
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace Node250

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 1, 3, 1, 0, 3], [0, 0], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 249) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 250 :=
  generated_of_packed 249 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2534 ⟨![[0], [], [1], [2], [0, 4], [4, 5], [1], [2, 3]], ![[0], [2], [3], [3, 7], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .noncentric 24, .edge 2532 ⟨![[0], [1], [], [2], [0], [1], [], [2, 5]], ![[0], [1], [3], [0, 0, 1, 3, 1, 7], [0, 0], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2539 ⟨![[], [1], [0, 4], [2], [4], [1, 4], [0], [2, 5]], ![[6], [1], [3], [1, 3, 5, 7], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2536 ⟨![[0], [], [1, 1, 1], [2], [0, 4], [1, 1], [1], [2, 3]], ![[0], [6], [3], [3, 7], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2541 ⟨![[], [0, 1], [0, 4], [2], [4], [0, 1], [0], [2, 5]], ![[6], [1, 6], [3], [1, 3, 1, 3, 4], [4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2531 ⟨![[0], [1], [2], [], [0, 5], [1, 3], [2, 5], []], ![[0], [1], [2], [0, 1, 5, 4], [0, 0], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2538 ⟨![[], [1], [2], [0, 0, 0], [4], [1, 4], [2], [0]], ![[7], [1], [2], [1, 3, 5, 3], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2535 ⟨![[0], [], [2], [1, 1, 1], [0, 4], [4, 5], [2], [1]], ![[0], [7], [2], [3, 3, 5], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .noncentric 8, .edge 2533 ⟨![[0], [1], [], [2, 5], [0], [1], [], [2]], ![[0], [1], [7], [0, 0, 1, 3, 1, 3], [0, 0], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2540 ⟨![[], [1], [0, 0, 0, 2], [0, 0, 0], [4], [1, 4], [0, 2, 5], [0]], ![[7], [1], [2, 7], [1, 3, 5, 3], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2537 ⟨![[0], [], [1, 2, 4], [1, 1, 1], [0, 4], [4, 5], [1, 2, 5], [1]], ![[0], [7], [2, 7], [3, 3, 5], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2542 ⟨![[], [0, 1, 3], [0, 0, 0, 2], [0, 0, 0], [4], [0, 1, 3], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [1, 3, 1, 7], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 250) : Classified H :=
  classify_of_checks 250 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node250

namespace Node251

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [1, 3, 1, 3], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 250) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 251 :=
  generated_of_packed 250 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2546 ⟨![[0], [], [1], [2], [0, 5], [0, 0], [1, 5], [1, 2, 1]], ![[0], [2], [3], [3, 3], [0, 4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2553 ⟨![[], [0, 4], [1], [2], [4, 5], [0], [0, 1, 0], [2, 3]], ![[5], [2], [3], [3, 3], [2, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2544 ⟨![[0], [1], [], [2], [0, 3, 5], [1, 5], [0, 0, 3], [2, 4]], ![[0], [1], [3], [3, 3], [1, 5], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 2551 ⟨![[], [1], [0, 3, 4], [2], [1, 1], [1, 5], [0], [2, 3]], ![[6], [1], [3], [3, 3], [1, 5], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2548 ⟨![[0], [], [1, 4], [2], [0, 5], [0, 0], [1], [1, 1, 2]], ![[0], [6], [3], [3, 3], [0, 4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2555 ⟨![[], [0, 1, 3], [0, 3, 4], [2], [4, 5], [0, 1, 3, 4], [0], [2, 3]], ![[6], [1, 6], [3], [3, 3], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2543 ⟨![[0], [1], [2], [], [0, 3], [1, 3, 5], [2, 4], [3]], ![[0], [1], [2], [7], [1, 5, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7]]⟩, .edge 2550 ⟨![[], [1], [2], [0, 2, 2], [0, 0], [1, 5], [2, 3, 5], [0]], ![[7], [1], [2], [3, 7], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2547 ⟨![[0], [], [2], [0, 1, 0], [0, 5], [0, 0], [2, 5], [1]], ![[0], [7], [2], [3, 7], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2554 ⟨![[], [0, 0, 0, 1], [2], [0, 2, 2], [0, 0], [0, 1, 5], [2, 3, 5], [0]], ![[7], [1, 7], [2], [3, 7], [2, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2545 ⟨![[0], [1], [], [2, 3, 5], [0, 3, 5], [1, 5], [0, 0, 3], [2]], ![[0], [1], [7], [3, 7], [1, 5], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2552 ⟨![[], [1], [0, 2], [1, 0, 1], [0, 0], [1, 5], [0, 2, 3, 4], [0]], ![[7], [1], [2, 7], [3, 7], [1, 5], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2549 ⟨![[0], [], [1, 2, 3], [0, 1, 0], [0, 5], [0, 0], [2, 1], [1]], ![[0], [7], [2, 7], [3, 7], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2556 ⟨![[], [0, 0, 0, 1], [0, 2], [0, 0, 0, 3], [0, 0], [0, 1, 5], [0, 2, 3, 4], [0]], ![[7], [1, 7], [2, 7], [3, 7], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 251) : Classified H :=
  classify_of_checks 251 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node251

namespace Node252

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [1, 3, 1, 3], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 251) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 252 :=
  generated_of_packed 251 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2560 ⟨![[0], [], [1], [2], [0, 5], [0, 0], [1, 4], [1, 2, 1]], ![[0], [2], [3], [2, 6], [0, 4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2567 ⟨![[], [0, 4], [1], [2], [4, 5], [0], [1, 3], [2, 3]], ![[5], [2], [3], [3, 3], [2, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2558 ⟨![[0], [1], [], [2], [0, 3], [1, 4], [3, 4], [0, 0, 2]], ![[0], [1], [3], [3, 3], [3, 3, 6], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2565 ⟨![[], [1], [0, 1, 1, 3], [2], [1, 1], [1, 5], [0], [2, 3]], ![[6], [1], [3], [3, 3], [1, 5], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2562 ⟨![[0], [], [1, 5], [2], [0, 5], [0, 0], [1], [2, 3, 5]], ![[0], [6], [3], [3, 3], [0, 4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2569 ⟨![[], [1, 0, 5], [0, 1, 1], [2], [4, 5], [0, 1, 3], [0], [2, 3]], ![[6], [1, 6], [3], [3, 3], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2557 ⟨![[0], [1], [2], [], [0, 3], [1, 3, 5], [0, 0, 2], [3]], ![[0], [1], [2], [7], [1, 5, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7]]⟩, .edge 2564 ⟨![[], [1], [2], [1, 0, 1], [0, 0], [1, 5], [2, 3], [0]], ![[7], [1], [2], [3, 7], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2561 ⟨![[0], [], [2], [0, 1, 0], [0, 5], [0, 0], [2, 4], [1]], ![[0], [7], [2], [2, 6], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2568 ⟨![[], [0, 0, 0, 1], [2], [0, 0, 0, 3], [0, 0], [0, 1, 5], [2, 3], [0]], ![[7], [1, 7], [2], [3, 7], [2, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2559 ⟨![[0], [1], [], [2, 3, 5], [0, 3], [1, 4], [3, 4], [2]], ![[0], [1], [7], [3, 7], [3, 6, 7], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2566 ⟨![[], [1], [0, 2], [1, 0, 1], [0, 0], [1, 5], [2, 0, 3], [0]], ![[7], [1], [2, 7], [3, 7], [1, 5], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2563 ⟨![[0], [], [2, 1, 4], [0, 1, 0], [0, 5], [0, 0], [0, 0, 2, 1], [1]], ![[0], [7], [2, 7], [3, 7], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2570 ⟨![[], [0, 0, 0, 1], [0, 2], [0, 0, 0, 3], [0, 0], [0, 1, 5], [2, 0, 3], [0]], ![[7], [1, 7], [2, 7], [3, 7], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 252) : Classified H :=
  classify_of_checks 252 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node252

namespace Node253

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 1, 2, 1, 2], [0, 0, 0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 252) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 253 :=
  generated_of_packed 252 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2574 ⟨![[0], [], [1], [2], [0, 5], [0, 0], [1, 4], [0, 2, 0]], ![[0], [2], [3], [2, 6], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2581 ⟨![[], [0, 4], [1], [2], [4, 5], [0], [1, 3], [2, 2, 2]], ![[5], [2], [3], [1, 1, 3, 3], [2, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2572 ⟨![[0], [1], [], [2], [0, 3], [1, 4], [3, 4], [2, 4]], ![[0], [1], [3], [0, 0, 0, 4], [0, 0, 1, 5], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2579 ⟨![[], [1], [0, 1, 1, 3], [2], [1, 1], [1, 5], [0], [1, 2, 1]], ![[6], [1], [3], [1, 2, 6, 5], [1, 5], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2576 ⟨![[0], [], [1, 5], [2], [0, 5], [0, 0], [1], [0, 2, 0]], ![[0], [6], [3], [2, 2, 5], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2583 ⟨![[], [1, 0, 5], [0, 1, 1], [2], [4, 5], [0, 1, 3], [0], [2, 2, 2]], ![[6], [1, 6], [3], [1, 1, 3, 3], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2571 ⟨![[0], [1], [2], [], [0, 3, 5], [1, 2, 2], [2, 4], [3, 5]], ![[0], [1], [2], [2, 6], [0, 1, 4, 5], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7]]⟩, .edge 2578 ⟨![[], [1], [2], [0, 2, 2], [0, 0], [1, 5], [2, 3], [0]], ![[7], [1], [2], [1, 2, 2, 5], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2575 ⟨![[0], [], [2], [1, 3, 5], [0, 5], [0, 0], [2, 4], [1]], ![[0], [7], [2], [2, 6], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2582 ⟨![[], [0, 1, 5], [2], [0, 2, 2], [0, 0], [1, 0, 5], [2, 3], [0]], ![[7], [1, 7], [2], [1, 1, 3, 7], [2, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2573 ⟨![[0], [1], [], [2, 3], [0, 3], [1, 4], [3, 4], [2]], ![[0], [1], [7], [0, 0, 0, 4], [0, 0, 1, 5], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2580 ⟨![[], [1], [0, 2], [0, 3, 4], [0, 0], [1, 5], [2, 0, 3], [0]], ![[7], [1], [2, 7], [1, 2, 6, 5], [1, 5], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2577 ⟨![[0], [], [2, 1], [1, 3, 5], [0, 5], [0, 0], [2, 1, 5], [1]], ![[0], [7], [2, 7], [2, 2, 5], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2584 ⟨![[], [0, 1, 5], [0, 2], [0, 3, 4], [0, 0], [1, 0, 5], [2, 0, 3], [0]], ![[7], [1, 7], [2, 7], [1, 1, 3, 7], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 253) : Classified H :=
  classify_of_checks 253 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node253

namespace Node254

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 1, 0, 1, 3, 3], [0, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 253) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 254 :=
  generated_of_packed 253 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2588 ⟨![[0], [], [1], [2], [0, 4, 5], [], [1], [1, 1, 2]], ![[0], [2], [3], [0, 3, 0, 7], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2595 ⟨![[], [0, 5], [1], [2], [4], [0], [1, 3], [2, 3]], ![[5], [2], [3], [1, 1, 3, 3], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2586 ⟨![[0], [1], [], [2], [0, 3], [1], [2, 2, 4], [2, 4, 5]], ![[0], [1], [3], [0, 0, 0, 4], [0, 0], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 2593 ⟨![[], [1], [0, 3, 4], [2], [4], [1, 4, 5], [0], [2, 3]], ![[6], [1], [3], [1, 2, 1, 6], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2590 ⟨![[0], [], [1], [2], [0, 4, 5], [], [1], [1, 1, 2]], ![[0], [2], [3], [0, 3, 0, 7], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2597 ⟨![[], [1, 0, 5], [0, 3, 4], [2], [4], [1, 0], [0], [2, 3]], ![[6], [1, 6], [3], [1, 1, 3, 3], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2585 ⟨![[0], [1], [2], [], [0, 3], [1, 2, 2], [2, 4, 5], [3, 5]], ![[0], [1], [2], [2, 6], [0, 0], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7]]⟩, .edge 2592 ⟨![[], [1], [2], [0, 3, 4], [4], [0, 0, 1], [2, 3], [0]], ![[7], [1], [2], [1, 2, 2, 5], [4], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2589 ⟨![[0], [], [2], [1, 2, 2], [0, 4, 5], [], [2], [1]], ![[0], [7], [2], [0, 3, 4, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2596 ⟨![[], [0, 0, 0, 1], [2], [0, 3, 4], [4], [0, 1, 4], [2, 3], [0]], ![[7], [1, 7], [2], [1, 1, 3, 7], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2587 ⟨![[0], [1], [], [2, 3], [0, 3], [1], [3, 4, 5], [2]], ![[0], [1], [7], [0, 0, 0, 4], [0, 0], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2594 ⟨![[], [1], [0, 2], [0, 3, 4], [4], [0, 0, 1], [0, 2, 3, 4], [0]], ![[7], [1], [2, 7], [1, 2, 1, 6], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2591 ⟨![[0], [], [2, 1, 4], [0, 1, 0, 4], [0, 4, 5], [], [2, 1, 4], [1]], ![[0], [7], [2, 7], [0, 3, 4, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2598 ⟨![[], [0, 0, 0, 1], [0, 2], [0, 3, 4], [4], [0, 1, 4], [0, 1, 2, 1], [0]], ![[7], [1, 7], [2, 7], [1, 1, 3, 7], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 254) : Classified H :=
  classify_of_checks 254 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node254

namespace Node255

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 254) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 255 :=
  generated_of_packed 254 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2602 ⟨![[0], [], [1], [2], [0, 4, 5], [], [1, 4, 5], [2, 3]], ![[0], [2], [3], [3, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2609 ⟨![[], [0, 5], [1], [2], [4], [0], [1, 3, 5], [1, 2, 1]], ![[5], [2], [3], [3, 3], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2600 ⟨![[0], [1], [], [2], [0, 3, 5], [1, 4, 5], [3, 4], [2, 4, 5]], ![[0], [1], [3], [3, 3], [0, 0], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 2607 ⟨![[], [1], [0, 3, 4, 5], [2], [4], [1, 4, 5], [0], [2, 3, 5]], ![[6], [1], [3], [3, 3], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2604 ⟨![[0], [], [1, 4, 5], [2], [0, 4, 5], [], [1], [2, 3]], ![[0], [6], [3], [3, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2611 ⟨![[], [0, 1, 3], [0, 1, 1, 4], [2], [4], [1, 0], [0], [1, 1, 2]], ![[6], [1, 6], [3], [3, 3], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2599 ⟨![[0], [1], [2], [], [0, 3, 5], [1, 3], [1, 2, 1], [3]], ![[0], [1], [2], [7], [0, 0], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7]]⟩, .edge 2606 ⟨![[], [1], [2], [1, 0, 1], [4], [0, 0, 1], [0, 2, 0], [0]], ![[7], [1], [2], [3, 7], [4], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2603 ⟨![[0], [], [2], [1, 3], [0, 4, 5], [], [2, 4, 5], [1]], ![[0], [7], [2], [3, 7], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2610 ⟨![[], [0, 1, 5], [2], [0, 0, 0, 3], [4], [0, 1], [0, 2, 0], [0]], ![[7], [1, 7], [2], [3, 7], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2601 ⟨![[0], [1], [], [2, 3, 5], [0, 3, 5], [1, 4, 5], [3, 4], [2]], ![[0], [1], [7], [3, 7], [0, 0], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2608 ⟨![[], [1], [0, 2], [1, 0, 1], [4], [0, 0, 1], [2, 0, 3], [0]], ![[7], [1], [2, 7], [3, 7], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2605 ⟨![[0], [], [2, 1], [1, 3], [0, 4, 5], [], [2, 1, 4, 5], [1]], ![[0], [7], [2, 7], [3, 7], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2612 ⟨![[], [0, 1, 5], [0, 2], [0, 0, 0, 3], [4], [0, 1], [2, 0, 3], [0]], ![[7], [1, 7], [2, 7], [3, 7], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 255) : Classified H :=
  classify_of_checks 255 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node255

namespace Node256

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 0, 1, 0, 1], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 255) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 256 :=
  generated_of_packed 255 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2616 ⟨![[0], [], [1], [2], [0, 3], [], [1, 3], [0, 0, 2]], ![[0], [2], [3], [0, 0, 0, 4], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2623 ⟨![[], [0, 0, 0], [1], [2], [4, 5], [0], [1, 4, 5], [2]], ![[5], [2], [3], [1, 1, 4], [2, 6], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2614 ⟨![[0], [1], [], [2], [0, 0, 0], [1, 3], [5], [2]], ![[0], [1], [3], [1, 5], [0, 0, 6], [6], [6], [6], [6], [6]]⟩, .edge 2621 ⟨![[], [1], [0], [2], [4, 5], [1, 3], [0], [2]], ![[2], [1], [3], [1, 5], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2618 ⟨![[0], [], [1, 3], [2], [0, 3], [], [1], [0, 0, 2]], ![[0], [6], [3], [0, 0, 0, 4], [0, 0, 2, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2625 ⟨![[], [0, 1, 4], [0], [2], [4, 5], [0, 1, 1, 1], [0], [2]], ![[2], [1, 2], [3], [1, 1, 4], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2613 ⟨![[0], [1], [2], [], [0], [0, 0, 1], [2], []], ![[0], [1], [2], [0, 1, 0, 5], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2620 ⟨![[], [1], [2], [0, 0, 0], [0, 0], [1, 3], [0, 0, 2], [0]], ![[7], [1], [2], [1, 5], [2, 6], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2617 ⟨![[0], [], [2], [0, 0, 1], [0, 3], [], [2, 3], [1]], ![[0], [7], [2], [0, 0, 0, 4], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2624 ⟨![[], [0, 1, 3], [2], [0, 0, 0], [0, 0], [1, 0, 3], [0, 0, 2], [0]], ![[7], [1, 7], [2], [1, 1, 4], [2, 6], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2615 ⟨![[0], [1], [], [2, 5], [0, 0, 0], [1, 3], [5], [2]], ![[0], [1], [7], [1, 5], [0, 0, 6], [6], [6], [6], [6], [6]]⟩, .edge 2622 ⟨![[], [1], [0, 2], [0, 0, 0], [0, 0], [1, 3], [0, 2], [0]], ![[7], [1], [2, 7], [1, 5], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2619 ⟨![[0], [], [1, 2, 3], [0, 0, 1], [0, 3], [], [1, 2], [1]], ![[0], [7], [2, 7], [0, 0, 0, 4], [0, 0, 2, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2626 ⟨![[], [0, 1, 3], [0, 2], [0, 0, 0], [0, 0], [1, 0, 3], [0, 2], [0]], ![[7], [1, 7], [2, 7], [1, 1, 4], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 256) : Classified H :=
  classify_of_checks 256 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node256

namespace Node257

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 2, 2], [0, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 256) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 257 :=
  generated_of_packed 256 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2630 ⟨![[0], [], [1], [2], [0, 4, 5], [], [1, 4, 5], [0, 2, 0, 5]], ![[0], [2], [3], [0, 0, 2, 2], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2637 ⟨![[], [0, 5], [1], [2], [4], [0], [1, 2, 2], [2, 3]], ![[5], [2], [3], [2, 2, 4], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2628 ⟨![[0], [1], [], [2], [0, 2, 2], [1, 4, 5], [3, 4], [2, 4]], ![[0], [1], [3], [0, 0, 6], [0, 0], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 2635 ⟨![[], [1], [0, 2, 2, 4], [2], [4], [1, 4, 5], [0], [2, 3]], ![[6], [1], [3], [2, 4, 6], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2632 ⟨![[0], [], [1, 4, 5], [2], [0, 4, 5], [], [1], [0, 2, 0, 5]], ![[0], [6], [3], [0, 0, 2, 6], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2639 ⟨![[], [0, 1, 3], [0, 1, 1, 4], [2], [4], [1, 0], [0], [2, 3]], ![[6], [1, 6], [3], [2, 4, 6], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2627 ⟨![[0], [1], [2], [], [0, 3], [1, 2, 2, 5], [2, 4], [3, 5]], ![[0], [1], [2], [2, 6], [0, 0], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7]]⟩, .edge 2634 ⟨![[], [1], [2], [0, 2, 2], [4], [0, 0, 1], [2, 3, 5], [0]], ![[7], [1], [2], [2, 2, 4], [4], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2631 ⟨![[0], [], [2], [2, 1, 2], [0, 4, 5], [], [1, 2, 1], [1]], ![[0], [7], [2], [0, 0, 2, 2], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2638 ⟨![[], [0, 0, 0, 1], [2], [0, 2, 2], [4], [0, 1, 4], [2, 3, 5], [0]], ![[7], [1, 7], [2], [2, 2, 4], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2629 ⟨![[0], [1], [], [2, 3], [0, 3, 5], [1, 4, 5], [3, 4], [2]], ![[0], [1], [7], [0, 0, 6], [0, 0], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2636 ⟨![[], [1], [0, 2], [0, 3, 4], [4], [0, 0, 1], [2, 0, 3], [0]], ![[7], [1], [2, 7], [2, 4, 6], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2633 ⟨![[0], [], [1, 2, 3], [2, 1, 2], [0, 4, 5], [], [2, 1, 5], [1]], ![[0], [7], [2, 7], [0, 0, 2, 6], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2640 ⟨![[], [0, 0, 0, 1], [0, 2], [0, 3, 4], [4], [0, 1, 4], [2, 0, 3], [0]], ![[7], [1, 7], [2, 7], [2, 4, 6], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 257) : Classified H :=
  classify_of_checks 257 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node257

namespace Node258

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 0], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 257) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 258 :=
  generated_of_packed 257 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2644 ⟨![[0], [], [1], [2], [0, 4], [4, 5], [1, 5], [1, 2, 1]], ![[0], [2], [3], [3, 3], [0, 0], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2651 ⟨![[], [0], [1], [2], [4], [0], [1, 3], [1, 2, 1]], ![[1], [2], [3], [3, 3], [4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2642 ⟨![[0], [1], [], [2], [0, 3], [1, 5], [1, 1, 3], [2, 4]], ![[0], [1], [3], [3, 3], [0, 0], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 2649 ⟨![[], [1], [0, 3, 4], [2], [4], [1, 4], [0], [2, 3, 5]], ![[6], [1], [3], [3, 3], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2646 ⟨![[0], [], [1, 4], [2], [0, 4], [4, 5], [1], [1, 1, 2]], ![[0], [6], [3], [3, 3], [0, 0], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2653 ⟨![[], [1, 0, 5], [0, 3, 4], [2], [4], [1, 0, 5], [0], [1, 1, 2]], ![[6], [1, 6], [3], [3, 3], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2641 ⟨![[0], [1], [2], [], [0, 3, 5], [1, 3, 5], [2, 4], [3]], ![[0], [1], [2], [7], [0, 0], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7]]⟩, .edge 2648 ⟨![[], [1], [2], [0, 2, 2], [4], [1, 4], [2, 3], [0]], ![[7], [1], [2], [3, 7], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2645 ⟨![[0], [], [2], [1, 3, 4], [0, 4], [4, 5], [2, 5], [1]], ![[0], [7], [2], [3, 7], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2652 ⟨![[], [0, 1, 5], [2], [0, 2, 2], [4], [0, 1, 5], [2, 3], [0]], ![[7], [1, 7], [2], [3, 7], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 2643 ⟨![[0], [1], [], [2, 3, 5], [0, 3], [1, 5], [1, 1, 3], [2]], ![[0], [1], [7], [3, 7], [0, 0], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2650 ⟨![[], [1], [0, 2], [0, 0, 0, 3], [4], [1, 4], [0, 2, 3, 4], [0]], ![[7], [1], [2, 7], [3, 7], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2647 ⟨![[0], [], [1, 2, 3], [1, 3, 4], [0, 4], [4, 5], [2, 1], [1]], ![[0], [7], [2, 7], [3, 7], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2654 ⟨![[], [0, 1, 5], [0, 2], [0, 0, 0, 3], [4], [0, 1, 5], [0, 2, 3, 4], [0]], ![[7], [1, 7], [2, 7], [3, 7], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 258) : Classified H :=
  classify_of_checks 258 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node258

namespace Node259

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 1, 2, 2], [0, 0], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 258) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 259 :=
  generated_of_packed 258 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2658 ⟨![[0], [], [1], [2], [0, 4], [4, 5], [1, 5], [0, 2, 0]], ![[0], [2], [3], [2, 2, 5], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2665 ⟨![[], [0], [1], [2], [4], [0], [1, 3], [2, 3]], ![[1], [2], [3], [1, 1, 2, 2], [4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2656 ⟨![[0], [1], [], [2], [0, 3], [1, 5], [1, 1, 3], [1, 1, 2]], ![[0], [1], [3], [1, 1, 6], [0, 0], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 2663 ⟨![[], [1], [0, 3, 4], [2], [4], [1, 4], [0], [2, 3]], ![[6], [1], [3], [1, 1, 2, 6], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2660 ⟨![[0], [], [1, 4], [2], [0, 4], [4, 5], [1], [0, 2, 0]], ![[0], [6], [3], [2, 5, 6], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2667 ⟨![[], [1, 0, 5], [0, 3, 4], [2], [4], [1, 0, 5], [0], [2, 3]], ![[6], [1, 6], [3], [1, 1, 2, 6], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2655 ⟨![[0], [1], [2], [], [0, 3], [1, 3, 4], [1, 1, 2], [3, 5]], ![[0], [1], [2], [2, 6], [0, 0], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7]]⟩, .edge 2662 ⟨![[], [1], [2], [0, 3, 4], [4], [1, 4], [2, 3], [0]], ![[7], [1], [2], [1, 1, 2, 2], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2659 ⟨![[0], [], [2], [1, 3, 5], [0, 4], [4, 5], [2, 5], [1]], ![[0], [7], [2], [2, 2, 5], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2666 ⟨![[], [0, 0, 0, 1], [2], [0, 3, 4], [4], [0, 0, 0, 1], [2, 3], [0]], ![[7], [1, 7], [2], [1, 1, 2, 2], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 2657 ⟨![[0], [1], [], [2, 3], [0, 3], [1, 5], [1, 1, 3], [2]], ![[0], [1], [7], [1, 1, 6], [0, 0], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2664 ⟨![[], [1], [0, 2], [0, 3, 4], [4], [1, 4], [0, 2, 3, 4], [0]], ![[7], [1], [2, 7], [1, 1, 2, 6], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2661 ⟨![[0], [], [2, 1], [1, 3, 5], [0, 4], [4, 5], [2, 1, 4], [1]], ![[0], [7], [2, 7], [2, 5, 6], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2668 ⟨![[], [0, 0, 0, 1], [0, 2], [0, 3, 4], [4], [0, 0, 0, 1], [0, 2, 3, 4], [0]], ![[7], [1, 7], [2, 7], [1, 1, 2, 6], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 259) : Classified H :=
  classify_of_checks 259 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node259

namespace Node260

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 0], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 259) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 260 :=
  generated_of_packed 259 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2672 ⟨![[0], [], [1], [2], [0, 4], [4, 5], [1, 4], [1, 2, 1]], ![[0], [2], [3], [2, 6], [0, 0], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2679 ⟨![[], [0], [1], [2], [4], [0], [1, 3, 5], [1, 2, 1]], ![[1], [2], [3], [3, 3], [4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2670 ⟨![[0], [1], [], [2], [0, 3, 5], [1, 4], [3, 4], [1, 1, 2]], ![[0], [1], [3], [3, 3], [0, 0], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2677 ⟨![[], [1], [0, 1, 1, 3], [2], [4], [1, 4], [0], [2, 3, 5]], ![[6], [1], [3], [3, 3], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2674 ⟨![[0], [], [1, 5], [2], [0, 4], [4, 5], [1], [2, 3, 5]], ![[0], [6], [3], [3, 3], [0, 0], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2681 ⟨![[], [0, 1, 3], [0, 1, 1], [2], [4], [0, 1, 3], [0], [2, 3, 5]], ![[6], [1, 6], [3], [3, 3], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2669 ⟨![[0], [1], [2], [], [0, 3, 5], [1, 3, 5], [1, 1, 2], [3]], ![[0], [1], [2], [7], [0, 0], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7]]⟩, .edge 2676 ⟨![[], [1], [2], [0, 0, 0, 3], [4], [1, 4], [0, 2, 0], [0]], ![[7], [1], [2], [3, 7], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2673 ⟨![[0], [], [2], [1, 2, 2], [0, 4], [4, 5], [2, 4], [1]], ![[0], [7], [2], [2, 6], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2680 ⟨![[], [0, 1, 5], [2], [0, 0, 0, 3], [4], [0, 1, 5], [0, 2, 0], [0]], ![[7], [1, 7], [2], [3, 7], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 2671 ⟨![[0], [1], [], [2, 3, 5], [0, 3, 5], [1, 4], [3, 4], [2]], ![[0], [1], [7], [3, 7], [0, 0], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2678 ⟨![[], [1], [0, 2], [0, 0, 0, 3], [4], [1, 4], [2, 0, 3], [0]], ![[7], [1], [2, 7], [3, 7], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2675 ⟨![[0], [], [2, 1, 4], [1, 3, 4], [0, 4], [4, 5], [2, 1, 4, 5], [1]], ![[0], [7], [2, 7], [3, 7], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2682 ⟨![[], [0, 1, 5], [0, 2], [0, 0, 0, 3], [4], [0, 1, 5], [2, 0, 3], [0]], ![[7], [1, 7], [2, 7], [3, 7], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 260) : Classified H :=
  classify_of_checks 260 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node260

namespace Node261

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 1, 2, 1, 2], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 260) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 261 :=
  generated_of_packed 260 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2686 ⟨![[0], [], [1], [2], [0], [], [1, 3, 4], [2, 4]], ![[0], [2], [3], [0, 0, 2, 6], [3, 7], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2692 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [0, 0, 1], [2]], ![[5], [2], [3], [1, 2, 1, 6], [2, 6], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2684 ⟨![[0], [1], [], [2], [0, 0, 0], [1, 3, 4], [5], [2]], ![[0], [1], [3], [1, 3, 5, 3], [0, 0, 6], [6], [6], [6], [6], [6]]⟩, .noncentric 36, .edge 2688 ⟨![[0], [], [1, 3, 4], [2], [0], [], [1], [2, 4]], ![[0], [6], [3], [0, 0, 2, 2], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 100, .edge 2683 ⟨![[0], [1], [2], [], [0], [1, 4], [2], []], ![[0], [1], [2], [0, 0, 1, 2, 1, 2], [1, 5], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2690 ⟨![[], [1], [2], [0, 0, 0], [0, 0], [1], [0, 0, 2], [0]], ![[7], [1], [2], [1, 2, 1, 6], [2, 6], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2687 ⟨![[0], [], [2], [1, 4], [0], [], [2, 3, 4], [1]], ![[0], [7], [2], [0, 0, 2, 6], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2693 ⟨![[], [0, 1, 5], [2], [0, 0, 0], [0, 0], [1, 0], [0, 0, 2], [0]], ![[7], [1, 7], [2], [1, 2, 1, 6], [2, 6], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2685 ⟨![[0], [1], [], [2, 5], [0, 0, 0], [1, 3, 4], [5], [2]], ![[0], [1], [7], [1, 3, 1, 7], [0, 0, 6], [6], [6], [6], [6], [6]]⟩, .edge 2691 ⟨![[], [1], [0, 2], [0, 0, 0], [0, 0], [1], [0, 2], [0]], ![[7], [1], [2, 7], [1, 2, 1, 2, 4], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2689 ⟨![[0], [], [2, 1, 4], [1, 4], [0], [], [1, 2], [1]], ![[0], [7], [2, 7], [0, 0, 2, 2], [3, 3], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2694 ⟨![[], [0, 1, 5], [0, 2], [0, 0, 0], [0, 0], [1, 0], [0, 2], [0]], ![[7], [1, 7], [2, 7], [1, 2, 5, 2], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 261) : Classified H :=
  classify_of_checks 261 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node261

namespace Node262

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 2, 0, 2], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 261) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 262 :=
  generated_of_packed 261 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2698 ⟨![[0], [], [1], [2], [0, 3], [3, 4], [1, 5], [2, 3, 5]], ![[0], [2], [3], [3, 3], [3, 3, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2705 ⟨![[], [0, 3, 4, 5], [1], [2], [4, 5], [0], [1, 5], [2, 3]], ![[5], [2], [3], [3, 3], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2696 ⟨![[0], [1], [], [2], [0, 5], [1, 5], [], [0, 0, 2]], ![[0], [1], [3], [3, 3], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2703 ⟨![[], [1], [0, 4], [2], [4, 5], [1, 3], [0], [2, 3]], ![[6], [1], [3], [3, 3], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2700 ⟨![[0], [], [1, 1, 1], [2], [0, 3], [3, 4], [1], [2, 3, 5]], ![[0], [6], [3], [3, 3], [3, 3, 5], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2707 ⟨![[], [1, 0, 4], [0, 4], [2], [4, 5], [0, 1, 5], [0], [2, 3]], ![[6], [1, 6], [3], [3, 3], [2, 2], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2695 ⟨![[0], [1], [2], [], [0, 3], [1, 3, 5], [0, 0, 2], [3]], ![[0], [1], [2], [7], [1, 1, 7], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 2702 ⟨![[], [1], [2], [1, 0, 1], [0, 0], [1, 3], [2, 5], [0]], ![[7], [1], [2], [3, 7], [1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2699 ⟨![[0], [], [2], [0, 0, 1], [0, 3], [3, 4], [2, 5], [1]], ![[0], [7], [2], [3, 7], [3, 5, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2706 ⟨![[], [0, 0, 1, 0], [2], [0, 1, 1], [0, 0], [0, 1, 5], [2, 5], [0]], ![[7], [1, 7], [2], [3, 7], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2697 ⟨![[0], [1], [], [0, 0, 2], [0, 5], [1, 5], [], [2]], ![[0], [1], [7], [3, 7], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2704 ⟨![[], [1], [0, 0, 2, 0], [0, 2, 2], [0, 0], [1, 3], [2, 0, 5], [0]], ![[7], [1], [2, 7], [3, 7], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2701 ⟨![[0], [], [1, 2], [0, 0, 1], [0, 3], [3, 4], [2, 1], [1]], ![[0], [7], [2, 7], [3, 7], [3, 5, 7], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2708 ⟨![[], [0, 0, 1, 0], [0, 0, 2, 0], [0, 1, 1], [0, 0], [0, 1, 5], [2, 0, 5], [0]], ![[7], [1, 7], [2, 7], [3, 7], [2, 2], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 262) : Classified H :=
  classify_of_checks 262 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node262

namespace Node263

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 0, 1, 0, 1], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 262) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 263 :=
  generated_of_packed 262 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2712 ⟨![[0], [], [1], [2], [0, 3], [], [0, 0, 1], [0, 0, 2]], ![[0], [2], [3], [0, 0, 0, 4], [0, 2, 0, 6], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2719 ⟨![[], [0, 0, 0], [1], [2], [4, 5], [0], [1, 4], [2, 2, 2]], ![[5], [2], [3], [1, 1, 4], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2710 ⟨![[0], [1], [], [2], [0, 4], [0, 0, 1], [], [2, 4]], ![[0], [1], [3], [0, 0, 3, 7], [0, 0, 0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2717 ⟨![[], [1], [0, 5], [2], [4, 5], [1, 3], [0], [2, 2, 2]], ![[6], [1], [3], [1, 5], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2714 ⟨![[0], [], [0, 0, 1], [2], [0, 3], [], [1], [0, 0, 2]], ![[0], [6], [3], [0, 0, 0, 4], [0, 2, 4, 2], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6]]⟩, .edge 2721 ⟨![[], [0, 1, 3], [0, 5], [2], [1, 1], [0, 1, 1, 1], [0], [2, 2, 2]], ![[6], [1, 6], [3], [1, 1, 4], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2709 ⟨![[0], [1], [2], [], [0, 3, 5], [0, 0, 1], [2, 4], [3, 5]], ![[0], [1], [2], [0, 1, 0, 5], [2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 2716 ⟨![[], [1], [2], [0, 3, 4], [0, 0], [1, 3], [2, 4], [0]], ![[7], [1], [2], [1, 5], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2713 ⟨![[0], [], [2], [0, 0, 1], [0, 3], [], [0, 0, 2], [1]], ![[0], [7], [2], [0, 0, 0, 4], [0, 2, 0, 6], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2720 ⟨![[], [0, 1, 5], [2], [0, 1, 1], [0, 0], [1, 0, 3], [2, 4], [0]], ![[7], [1, 7], [2], [1, 1, 4], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2711 ⟨![[0], [1], [], [2, 4], [0, 4], [0, 0, 1], [], [2]], ![[0], [1], [7], [0, 0, 3, 3], [0, 0, 0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2718 ⟨![[], [1], [0, 0, 2, 0], [0, 3, 4], [0, 0], [1, 3], [2, 0, 4], [0]], ![[7], [1], [2, 7], [1, 5], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2715 ⟨![[0], [], [1, 2, 3], [0, 0, 1], [0, 3], [], [0, 2, 1, 0], [1]], ![[0], [7], [2, 7], [0, 0, 0, 4], [0, 2, 4, 2], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6]]⟩, .edge 2722 ⟨![[], [0, 1, 5], [0, 0, 2, 0], [0, 1, 1], [0, 0], [1, 0, 3], [2, 0, 4], [0]], ![[7], [1, 7], [2, 7], [1, 1, 4], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 263) : Classified H :=
  classify_of_checks 263 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node263

namespace Node264

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 1, 3, 1, 0, 3], [0, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 263) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 264 :=
  generated_of_packed 263 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 64, .edge 2732 ⟨![[], [0, 5], [1], [2], [4], [0], [1, 4, 5], [2, 5]], ![[5], [2], [3], [1, 3, 1, 4, 7], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2724 ⟨![[0], [1], [], [2], [0, 4, 5], [1, 4, 5], [], [2, 5]], ![[0], [1], [3], [1, 3, 5, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2730 ⟨![[], [1], [0, 5], [2], [4], [1, 4, 5], [0], [2, 5]], ![[6], [1], [3], [1, 3, 5, 3], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2727 ⟨![[0], [], [1, 1, 1], [2], [0, 1, 1], [], [1], [0, 2, 0, 3]], ![[0], [6], [3], [0, 3, 0, 7], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .noncentric 68, .edge 2723 ⟨![[0], [1], [2], [], [0, 5], [1, 3, 4, 5], [2, 5], []], ![[0], [1], [2], [0, 1, 5, 4], [0, 0], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2729 ⟨![[], [1], [2], [0, 0, 0], [4], [0, 0, 1], [0, 0, 2], [0]], ![[7], [1], [2], [1, 3, 1, 7], [4], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2726 ⟨![[0], [], [2], [1, 1, 1], [0, 4, 5], [], [2, 4, 5], [1]], ![[0], [7], [2], [0, 3, 4, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2733 ⟨![[], [0, 0, 1, 0], [2], [0, 0, 0], [4], [1, 0, 4], [0, 0, 2], [0]], ![[7], [1, 7], [2], [1, 3, 1, 7], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2725 ⟨![[0], [1], [], [2, 5], [0, 4, 5], [1, 4, 5], [], [2]], ![[0], [1], [7], [1, 3, 1, 7], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2731 ⟨![[], [1], [0, 2], [0, 0, 0], [4], [0, 0, 1], [0, 2, 5], [0]], ![[7], [1], [2, 7], [1, 3, 1, 7], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2728 ⟨![[0], [], [1, 2, 4], [1, 1, 1], [0, 4, 5], [], [1, 2, 5], [1]], ![[0], [7], [2, 7], [0, 3, 4, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2734 ⟨![[], [0, 0, 1, 0], [0, 2], [0, 0, 0], [4], [1, 0, 4], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [1, 3, 1, 7], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 264) : Classified H :=
  classify_of_checks 264 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node264

namespace Node265

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 264) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 265 :=
  generated_of_packed 264 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2738 ⟨![[0], [], [1], [2], [0, 3, 4, 5], [3, 4], [1, 5], [2, 3, 5]], ![[0], [2], [3], [3, 3], [0, 0], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2745 ⟨![[], [0, 3, 5], [1], [2], [4], [0], [0, 0, 1], [2, 3, 5]], ![[5], [2], [3], [3, 3], [4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2736 ⟨![[0], [1], [], [2], [0, 4, 5], [1, 5], [], [1, 2, 1]], ![[0], [1], [3], [3, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2743 ⟨![[], [1], [0, 5], [2], [4], [0, 1, 0], [0], [2, 3, 5]], ![[6], [1], [3], [3, 3], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2740 ⟨![[0], [], [1, 1, 1], [2], [0, 1, 1], [3, 4], [1], [2, 3, 5]], ![[0], [6], [3], [3, 3], [0, 0], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2747 ⟨![[], [0, 1, 3], [0, 5], [2], [4], [0, 1, 5], [0], [2, 3, 5]], ![[6], [1, 6], [3], [3, 3], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2735 ⟨![[0], [1], [2], [], [0, 3, 5], [0, 1, 0], [2, 4, 5], [3]], ![[0], [1], [2], [7], [0, 0], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5]]⟩, .edge 2742 ⟨![[], [1], [2], [0, 0, 0, 3], [4], [0, 0, 1, 3], [0, 0, 2], [0]], ![[7], [1], [2], [3, 7], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2739 ⟨![[0], [], [2], [1, 4, 5], [0, 1, 1], [3, 4], [2, 5], [1]], ![[0], [7], [2], [3, 7], [0, 0], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2746 ⟨![[], [0, 1, 3], [2], [0, 1, 1], [4], [0, 1, 5], [0, 0, 2], [0]], ![[7], [1, 7], [2], [3, 7], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 2737 ⟨![[0], [1], [], [2, 4, 5], [0, 4, 5], [1, 5], [], [2]], ![[0], [1], [7], [3, 7], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2744 ⟨![[], [1], [0, 0, 2, 0], [0, 2, 2], [4], [1, 2, 2], [2, 0, 4], [0]], ![[7], [1], [2, 7], [3, 7], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2741 ⟨![[0], [], [1, 2], [1, 4, 5], [0, 1, 1], [3, 4], [2, 1], [1]], ![[0], [7], [2, 7], [3, 7], [0, 0], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 2748 ⟨![[], [0, 1, 3], [0, 0, 2, 0], [0, 1, 1], [4], [0, 1, 5], [2, 0, 4], [0]], ![[7], [1, 7], [2, 7], [3, 7], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 265) : Classified H :=
  classify_of_checks 265 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node265

namespace Node266

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 265) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 266 :=
  generated_of_packed 265 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2752 ⟨![[0], [], [1], [2], [0, 3, 5], [4], [1], [2, 5]], ![[0], [2], [3], [3, 3], [5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2759 ⟨![[], [0, 3, 4], [1], [2], [4, 5], [0], [1, 5], [2, 3, 5]], ![[5], [2], [3], [1, 1], [1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2750 ⟨![[0], [1], [], [2], [0, 5], [1], [], [2, 4]], ![[0], [1], [3], [3, 3], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2757 ⟨![[], [1], [0, 4], [2], [4, 5], [1, 3, 5], [0], [0, 2, 0]], ![[6], [1], [3], [3, 3], [1, 1], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2754 ⟨![[0], [], [1, 4], [2], [0, 3, 5], [4], [1], [2, 5]], ![[0], [6], [3], [3, 3], [5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2761 ⟨![[], [1, 0, 4], [0, 4], [2], [4, 5], [0, 1], [0], [0, 2, 0]], ![[6], [1, 6], [3], [1, 1], [1, 5], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2749 ⟨![[0], [1], [2], [], [0, 3, 5], [1, 5], [2, 4], [3]], ![[0], [1], [2], [7], [1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩, .edge 2756 ⟨![[], [1], [2], [0, 3, 4], [4, 5], [1, 3, 5], [2, 5], [0]], ![[7], [1], [2], [3, 7], [1, 1], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2753 ⟨![[0], [], [2], [0, 0, 1], [0, 3, 5], [4], [2], [1]], ![[0], [7], [2], [3, 7], [5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2760 ⟨![[], [1, 0, 4], [2], [0, 3, 4], [4, 5], [1, 0, 3], [2, 5], [0]], ![[7], [1, 7], [2], [1, 1], [1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2751 ⟨![[0], [1], [], [2, 4], [0, 5], [1], [], [2]], ![[0], [1], [7], [3, 7], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2758 ⟨![[], [1], [0, 2, 3], [0, 2, 2], [4, 5], [1, 3, 5], [2, 0], [0]], ![[7], [1], [2, 7], [3, 7], [1, 1], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 2755 ⟨![[0], [], [1, 2, 3], [0, 0, 1], [0, 3, 5], [4], [1, 2, 2, 2], [1]], ![[0], [7], [2, 7], [3, 7], [5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2762 ⟨![[], [1, 0, 4], [0, 2, 3], [0, 2, 2], [4, 5], [1, 0, 3], [2, 0], [0]], ![[7], [1, 7], [2, 7], [1, 1], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 266) : Classified H :=
  classify_of_checks 266 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node266

namespace Node267

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 1], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 266) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 267 :=
  generated_of_packed 266 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 64, .edge 2771 ⟨![[], [2, 0, 2], [1], [2], [4], [0], [0, 0, 1], [2, 5]], ![[5], [2], [3], [1, 5], [4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2764 ⟨![[0], [1], [], [2], [0, 4, 5], [1, 5], [], [2, 5]], ![[0], [1], [3], [1, 1], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .noncentric 36, .edge 2767 ⟨![[0], [], [1, 1, 1], [2], [0, 1, 1], [3], [1], [2, 3, 4]], ![[0], [6], [3], [5], [0, 0], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 2773 ⟨![[], [1, 0, 5], [0, 5], [2], [4], [0, 1, 5], [0], [2, 5]], ![[6], [1, 6], [3], [1, 5], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2763 ⟨![[0], [1], [2], [], [0, 5], [1, 3, 4], [2, 5], []], ![[0], [1], [2], [1, 1], [0, 0], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2769 ⟨![[], [1], [2], [0, 0, 0], [4], [1, 3, 5], [0, 0, 2], [0]], ![[7], [1], [2], [1, 1], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2766 ⟨![[0], [], [2], [1, 4], [0, 3, 5], [3], [2, 5], [1]], ![[0], [7], [2], [5], [0, 0], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2772 ⟨![[], [0, 1, 5], [2], [0, 0, 0], [4], [1, 0, 3], [0, 0, 2], [0]], ![[7], [1, 7], [2], [1, 5], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 2765 ⟨![[0], [1], [], [2, 5], [0, 4, 5], [1, 5], [], [2]], ![[0], [1], [7], [1, 1], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2770 ⟨![[], [1], [0, 2], [0, 0, 0], [4], [1, 3, 5], [0, 2, 5], [0]], ![[7], [1], [2, 7], [1, 1], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2768 ⟨![[0], [], [1, 2, 3], [1, 4], [0, 3, 5], [3], [1, 2, 5], [1]], ![[0], [7], [2, 7], [5], [0, 0], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 2774 ⟨![[], [0, 1, 5], [0, 2], [0, 0, 0], [4], [1, 0, 3], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [1, 5], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 267) : Classified H :=
  classify_of_checks 267 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node267

namespace Node268

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 1], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 267) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 268 :=
  generated_of_packed 267 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2778 ⟨![[0], [], [1], [2], [0, 5], [3], [0, 0, 1], [2, 4]], ![[0], [2], [3], [5], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2785 ⟨![[], [0, 4], [1], [2], [4, 5], [0], [1, 4], [2]], ![[5], [2], [3], [1, 5], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2776 ⟨![[0], [1], [], [2], [0, 4], [0, 0, 1], [], [2]], ![[0], [1], [3], [1, 1], [0, 0, 0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2783 ⟨![[], [1], [0, 5], [2], [4, 5], [1, 5], [0], [2]], ![[6], [1], [3], [1, 1], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2780 ⟨![[0], [], [1, 1, 1], [2], [0, 5], [3], [1], [2, 4]], ![[0], [6], [3], [5], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2787 ⟨![[], [0, 1, 5], [0, 5], [2], [4, 5], [0, 1, 4, 5], [0], [2]], ![[6], [1, 6], [3], [1, 5], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2775 ⟨![[0], [1], [2], [], [0], [1, 4], [2], []], ![[0], [1], [2], [1, 1], [1, 1, 1, 5], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2782 ⟨![[], [1], [2], [0, 0, 0], [0, 0], [1, 5], [2, 4], [0]], ![[7], [1], [2], [1, 1], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2779 ⟨![[0], [], [2], [1, 1, 1], [0, 5], [3], [0, 0, 2], [1]], ![[0], [7], [2], [5], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2786 ⟨![[], [0, 1], [2], [0, 0, 0], [0, 0], [0, 1, 4], [2, 4], [0]], ![[7], [1, 7], [2], [1, 5], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2777 ⟨![[0], [1], [], [2], [0, 4], [0, 0, 1], [], [2]], ![[0], [1], [3], [1, 1], [0, 0, 0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2784 ⟨![[], [1], [0, 2, 5], [0, 0, 0], [0, 0], [1, 5], [0, 2], [0]], ![[7], [1], [2, 7], [1, 1], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2781 ⟨![[0], [], [1, 1, 2, 1], [1, 1, 1], [0, 5], [3], [1, 2], [1]], ![[0], [7], [2, 7], [5], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2788 ⟨![[], [0, 1], [0, 2, 5], [0, 0, 0], [0, 0], [0, 1, 4], [0, 2], [0]], ![[7], [1, 7], [2, 7], [1, 5], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 268) : Classified H :=
  classify_of_checks 268 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node268

namespace Node269

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [5]],
   ![[0], [1], [0, 0], [0, 0, 0, 1, 1, 1, 0, 1], [1, 1], [2], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 268) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 269 :=
  generated_of_packed 268 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 2789 ⟨![[0], [], [1], [3, 0], [4], [1]], ![[0], [2], [0, 0], [0, 0, 3, 0], [4], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 2790 ⟨![[], [0, 2, 3], [1], [2], [0], [1]], ![[4], [2], [3], [1, 1, 1, 4, 3], [1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .noncentric 256, .noncentric 96, .noncentric 256, .noncentric 96] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 269) : Classified H :=
  classify_of_checks 269 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node269

namespace Node270

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [3], [4]],
   ![[0], [1], [0, 0], [2], [3], [0, 0, 0, 1, 0, 1, 3], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 269) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 270 :=
  generated_of_packed 269 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2791 ⟨![[0], [], [1], [2, 4], [0, 4], [], [1], [2, 4]], ![[0], [2], [0, 0, 0, 4, 3], [0, 0], [0, 0, 0, 4], [0, 0, 4, 4], [0, 0, 4, 4], [0, 0, 4, 4], [0, 0, 4, 4], [0, 0, 4, 4]]⟩, .edge 2792 ⟨![[], [0, 0, 0], [1], [2, 4], [3], [0], [1, 5], [2, 4, 5]], ![[5], [2], [1, 1, 3, 4], [4], [1, 1, 4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 64, .noncentric 320, .noncentric 64, .noncentric 320, .noncentric 256, .noncentric 256, .noncentric 256, .noncentric 256, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 270) : Classified H :=
  classify_of_checks 270 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node270

namespace Node271

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [3], [4]],
   ![[0], [1], [1, 1], [2], [3], [0, 0], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 270) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 271 :=
  generated_of_packed 270 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2796 ⟨![[0], [], [1], [2], [0, 5], [3], [1, 5], [2, 5]], ![[0], [2], [3], [5], [0, 0], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2803 ⟨![[], [0, 4, 5], [1], [2], [4], [0], [1, 5], [2]], ![[5], [2], [3], [1, 5], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2794 ⟨![[0], [1], [], [2], [0, 5], [1, 5], [], [2]], ![[0], [1], [3], [1, 1], [0, 0], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2801 ⟨![[], [1], [0, 0, 0], [2], [4], [1, 5], [0], [2]], ![[6], [1], [3], [1, 1], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2798 ⟨![[0], [], [1, 1, 1], [2], [0, 5], [3], [1], [2, 5]], ![[0], [6], [3], [5], [0, 0], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2805 ⟨![[], [0, 1, 4], [0, 0, 0], [2], [4], [1, 0], [0], [2]], ![[6], [1, 6], [3], [1, 5], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2793 ⟨![[0], [1], [2], [], [0], [1, 5], [2], []], ![[0], [1], [2], [1, 1], [0, 0], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5]]⟩, .edge 2800 ⟨![[], [1], [2], [0, 4], [4], [1, 5], [2, 5], [0]], ![[7], [1], [2], [1, 1], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2797 ⟨![[0], [], [2], [1, 1, 1], [0, 5], [3], [2, 5], [1]], ![[0], [7], [2], [5], [0, 0], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2804 ⟨![[], [0, 1, 4], [2], [0, 4], [4], [0, 1, 5], [2, 5], [0]], ![[7], [1, 7], [2], [1, 5], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2795 ⟨![[0], [1], [], [2], [0, 5], [1, 5], [], [2]], ![[0], [1], [3], [1, 1], [0, 0], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2802 ⟨![[], [1], [2, 0, 4], [0, 4], [4], [1, 5], [0, 2], [0]], ![[7], [1], [2, 7], [1, 1], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2799 ⟨![[0], [], [1, 1, 1, 2], [1, 1, 1], [0, 5], [3], [1, 2], [1]], ![[0], [7], [2, 7], [5], [0, 0], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 2806 ⟨![[], [0, 1, 4], [2, 0, 4], [0, 4], [4], [0, 1, 5], [0, 2], [0]], ![[7], [1, 7], [2, 7], [1, 5], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 271) : Classified H :=
  classify_of_checks 271 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node271

namespace Node272

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0, 0, 1, 0, 1, 2], [0, 0, 0, 1, 0, 1, 1, 1], [0, 0], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 271) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 272 :=
  generated_of_packed 271 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 2807 ⟨![[0], [], [1, 2, 3, 5], [0, 3, 5], [2], [1, 2, 3]], ![[0], [0, 0, 0, 2, 3, 4], [4], [0, 0, 0, 2, 3, 5], [0, 0], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .edge 2808 ⟨![[], [0, 3, 4], [0, 0, 1, 4], [4], [0], [0, 0, 1, 4]], ![[4], [1, 2, 1, 3], [1, 4], [1, 1, 1, 3, 4], [3], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .noncentric 160, .noncentric 160, .noncentric 160, .noncentric 160] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 272) : Classified H :=
  classify_of_checks 272 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node272

namespace Node273

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [4]],
   ![[0], [1], [1, 1], [0, 0, 0, 1, 0, 1, 1, 1], [2], [0, 1, 1, 0, 1, 1], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 272) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 273 :=
  generated_of_packed 272 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 2809 ⟨![[0], [], [1], [0, 3, 5], [2], [1, 5]], ![[0], [2], [4], [0, 0, 0, 2, 3, 5], [0, 0], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .edge 2810 ⟨![[], [0, 3, 4], [1], [4], [0], [1]], ![[4], [2], [1, 4], [1, 1, 1, 3, 4], [3], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .noncentric 192, .noncentric 192, .noncentric 192, .noncentric 192] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 273) : Classified H :=
  classify_of_checks 273 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node273

namespace Node274

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [1, 1], [1, 1, 1, 2, 1, 2], [0, 0], [1, 1, 2, 1, 1, 2], [1, 1, 2, 1, 1, 2], [1, 1, 2, 1, 1, 2], [1, 1, 2, 1, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 273) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 274 :=
  generated_of_packed 273 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 2812 ⟨![[0], [], [1], [0, 5], [2], [1, 3, 5]], ![[0], [2], [4], [2, 4, 5, 4], [0, 0], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]⟩, .noncentric 904, .edge 2811 ⟨![[0], [1], [], [0], [1, 3], []], ![[0], [1], [1, 1], [1, 1, 1, 4], [0, 0], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .noncentric 904, .edge 2813 ⟨![[0], [], [1, 1, 1], [0, 5], [2], [1]], ![[0], [5], [4], [2, 2, 4], [0, 0], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]⟩, .noncentric 904] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 274) : Classified H :=
  classify_of_checks 274 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node274

end ReeTwo.SylowModel.SmallEvenMaximalLower
