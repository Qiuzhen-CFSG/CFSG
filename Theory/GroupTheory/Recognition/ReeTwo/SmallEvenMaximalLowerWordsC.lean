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

namespace Node50

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 1, 1, 1, 0, 1, 3], [1, 0, 1, 0], [3, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 49) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 50 :=
  generated_of_packed 49 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 546 ⟨![[], [0], [1], [2, 3], [], [0, 3], [1, 6], [2, 3, 5]], ![[1], [2], [1, 1, 1, 3, 5], [1, 1, 1, 5], [1, 5], [3, 3], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .core, .edge 550 ⟨![[], [0, 3], [1], [2, 3], [], [0], [1, 6], [2, 3, 5]], ![[5], [2], [1, 1, 1, 5, 3], [1, 1, 1, 5], [1, 1], [3, 3], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 541 ⟨![[0], [1], [], [2, 3], [0, 6], [1, 6], [], [2, 3, 6]], ![[0], [1], [0, 1, 0, 1, 1, 1, 7], [0, 1, 0, 1, 1, 5], [0, 1, 0, 5], [3, 3], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 548 ⟨![[], [1], [0, 6], [2, 3], [], [1, 3], [0], [2, 3, 5]], ![[6], [1], [1, 1, 1, 3, 5], [1, 1, 1, 5], [1, 5], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 544 ⟨![[0], [], [1, 1, 1], [2, 3], [0, 3, 6], [3, 4], [1], [2, 3]], ![[0], [6], [0, 2, 0, 3, 6], [0, 5, 4, 5], [0, 5, 4], [3, 3], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 552 ⟨![[], [0, 3, 1], [0, 6], [2, 3], [], [0, 1, 6], [0], [2, 3, 5]], ![[6], [1, 6], [1, 1, 1, 5, 3], [1, 1, 1, 5], [1, 1], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 540 ⟨![[0], [1], [2], [], [0, 5], [1], [2, 6], [5]], ![[0], [1], [2], [0, 1, 1, 1, 0, 1], [1, 0, 1, 0], [7], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 547 ⟨![[], [1], [2], [0, 3, 5], [], [1, 3], [2, 6], [0, 3]], ![[1, 1, 1, 5, 7], [1], [2], [1, 1, 1, 5], [1, 5], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 543 ⟨![[0], [], [2], [1, 4], [0, 3, 6], [3, 4], [2, 6], [1, 3]], ![[0], [0, 4, 7], [2], [0, 2, 4, 2], [0, 5, 4], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 551 ⟨![[], [1, 0], [2], [0, 3, 5], [], [1, 0, 3], [2, 6], [0, 3]], ![[1, 1, 1, 3, 1], [3, 1], [2], [1, 1, 1, 5], [1, 1], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 542 ⟨![[0], [1], [], [2, 3, 6], [0, 6], [1, 6], [], [2, 3]], ![[0], [1], [0, 1, 0, 1, 1, 1, 3], [0, 1, 0, 1, 1, 5], [0, 1, 0, 5], [3, 7], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 549 ⟨![[], [1], [2, 0], [0, 3, 5], [], [1, 3], [2, 0, 6], [0, 3]], ![[1, 1, 1, 5, 7], [1], [1, 1, 1, 3, 1, 2], [1, 1, 1, 5], [1, 5], [3, 7], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 545 ⟨![[0], [], [1, 1, 2, 1], [1, 4], [0, 3, 6], [3, 4], [2, 1, 5], [1, 3]], ![[0], [0, 4, 7], [0, 4, 3, 6], [0, 3, 0, 7], [0, 5, 4], [3, 7], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 553 ⟨![[], [1, 0], [2, 0], [0, 3, 5], [], [1, 0, 3], [2, 0, 6], [0, 3]], ![[1, 1, 1, 3, 1], [3, 1], [1, 1, 1, 2, 1, 7], [1, 1, 1, 5], [1, 1], [3, 7], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 50) : Classified H :=
  classify_of_checks 50 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node50

namespace Node51

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [3]],
   ![[0], [1], [0, 0], [2], [2, 1, 1, 2, 2], [2, 2], [1, 0, 1, 0], [0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 50) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 51 :=
  generated_of_packed 50 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 556 ⟨![[], [0], [3, 1], [2], [0, 2, 3, 5], [0, 1, 0, 4]], ![[1], [5, 1, 1], [3], [1, 1], [1, 2, 2, 4, 3], [1, 4, 3], [1, 2, 2, 3, 4], [1, 2, 2, 3, 4], [1, 2, 2, 3, 4], [1, 2, 2, 3, 4]]⟩, .core, .edge 558 ⟨![[], [0, 0, 3, 0], [3, 1], [2], [0], [0, 1, 3, 0]], ![[4], [5, 1, 4], [3], [1, 4], [1, 2, 1, 5], [1, 1, 4, 4], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 554 ⟨![[0], [1], [], [0, 2, 2], [1, 5], [2, 2]], ![[0], [1], [0, 0], [1, 1], [1, 0, 1, 3], [1, 0, 1, 0], [0, 1, 0, 4], [0, 1, 0, 4], [0, 1, 0, 4], [0, 1, 0, 4]]⟩, .edge 557 ⟨![[], [1], [0, 2, 3], [2], [1, 0, 0, 3], [0, 3, 6]], ![[1, 3, 1, 2], [1], [3], [1, 1], [1, 4, 2, 2], [1, 4, 3], [1, 2, 2, 4], [1, 2, 2, 4], [1, 2, 2, 4], [1, 2, 2, 4]]⟩, .edge 555 ⟨![[0], [], [5, 1], [0, 2, 1, 1], [3], [3, 1]], ![[0], [0, 3, 2, 4], [0, 0], [4], [2, 2, 4], [3, 4, 0], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 559 ⟨![[], [0, 1, 3, 4], [0, 2, 3], [2], [0, 1, 5], [0, 3, 6]], ![[1, 3, 4, 2], [4, 4, 2, 1], [3], [1, 4], [1, 2, 4, 2], [1, 1, 4, 4], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 51) : Classified H :=
  classify_of_checks 51 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node51

namespace Node52

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 2, 0, 1, 2, 1], [0, 0, 0, 1, 0, 2, 1, 2], [2, 2], [1, 2, 1, 2, 2, 2], [0, 0, 1, 0, 0, 2, 1, 2], [0, 0, 1, 0, 0, 2, 1, 2], [0, 0, 1, 0, 0, 2, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 51) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 52 :=
  generated_of_packed 51 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 561 ⟨![[0], [], [1], [3, 0], [], [1, 5]], ![[0], [2], [0, 2, 0, 5], [0, 0, 0, 3, 2, 5], [2, 2], [2, 2, 2, 5], [0, 0, 2, 3, 3, 5], [0, 0, 2, 3, 3, 5], [0, 0, 2, 3, 3, 5], [0, 0, 2, 3, 3, 5]]⟩, .edge 564 ⟨![[], [0, 3, 2, 4], [1], [2, 5], [0], [1, 4]], ![[4], [2], [4, 3, 1], [1, 3, 1], [2, 2], [1, 2, 4, 2], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1, 2, 2]]⟩, .edge 560 ⟨![[0], [1], [], [0, 4], [1, 5], [4]], ![[0], [1], [0, 0, 1, 4], [0, 0, 0, 1, 3, 4], [5], [1, 4], [0, 0, 1, 0, 3, 4], [0, 0, 1, 0, 3, 4], [0, 0, 1, 0, 3, 4], [0, 0, 1, 0, 3, 4]]⟩, .edge 563 ⟨![[], [1], [0, 0, 0], [0, 0], [1, 3], [0]], ![[5], [1], [4, 3, 4], [1, 4], [2, 5], [1, 2, 4, 2, 3], [1, 2, 3, 4, 2], [1, 2, 3, 4, 2], [1, 2, 3, 4, 2], [1, 2, 3, 4, 2]]⟩, .edge 562 ⟨![[0], [], [1, 5], [3, 0], [], [1]], ![[0], [5], [0, 2, 3, 2], [0, 0, 0, 3, 2, 2], [2, 5], [2, 2, 2, 5], [0, 0, 2, 0, 0, 2], [0, 0, 2, 0, 0, 2], [0, 0, 2, 0, 0, 2], [0, 0, 2, 0, 0, 2]]⟩, .edge 565 ⟨![[], [0, 2, 1, 3], [0, 0, 0], [0, 0], [3, 1, 0], [0]], ![[5], [1, 5], [4, 3, 1], [1, 3, 1], [2, 5], [1, 2, 3, 1, 5], [1, 2, 1, 2], [1, 2, 1, 2], [1, 2, 1, 2], [1, 2, 1, 2]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 52) : Classified H :=
  classify_of_checks 52 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node52

namespace Node53

def gen : Fin 5 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [3], [4]],
   ![[0], [1], [2], [3], [4], [2, 2], [0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 52) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 53 :=
  generated_of_packed 52 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .core, .edge 573 ⟨![[0], [], [1], [2], [3], [0], [], [1, 5], [0, 0, 2], [3]], ![[0], [2], [3], [4], [2, 2], [0, 3, 0, 3], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7]]⟩, .edge 588 ⟨![[], [0, 0, 0], [1], [2], [3], [0, 0], [0], [1, 4], [0, 2, 0], [3, 6]], ![[6], [2], [3], [4], [2, 2], [3, 5, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 569 ⟨![[0], [1], [], [2], [3], [0, 4], [1, 5], [4], [2], [3, 6]], ![[0], [1], [3], [4], [7], [1, 6], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 584 ⟨![[], [1], [0, 0, 0, 4], [2], [3], [0, 0], [1], [0], [2, 4, 6], [3, 6]], ![[7], [1], [3], [4], [2, 7], [3, 5, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 577 ⟨![[0], [], [1, 5], [2], [3], [0], [], [1], [0, 0, 2], [3]], ![[0], [7], [3], [4], [2, 7], [0, 3, 0, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 592 ⟨![[], [0, 0, 1, 0], [0, 0, 0, 4], [2], [3], [0, 0], [1, 0], [0], [1, 2, 1], [3, 6]], ![[7], [1, 7], [3], [4], [2, 7], [3, 5, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 567 ⟨![[0], [1], [2], [], [3], [0, 4, 6], [0, 0, 1], [2], [4], [3, 6]], ![[0], [1], [2], [4], [8], [0, 5, 8], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 582 ⟨![[], [1], [2], [0, 4, 5], [3], [5, 6], [1], [2, 4], [0], [3, 6]], ![[8], [1], [2], [4], [2, 2], [3, 3], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 575 ⟨![[0], [], [2], [0, 0, 1], [3], [0], [], [2, 5], [1], [3]], ![[0], [8], [2], [4], [2, 2], [0, 3, 0, 8], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7]]⟩, .edge 590 ⟨![[], [0, 1, 4], [2], [0, 4, 5], [3], [5, 6], [1, 0, 6], [2, 4], [0], [3, 6]], ![[8], [1, 8], [2], [4], [2, 2], [3, 3], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 571 ⟨![[0], [1], [], [2, 4], [3], [0, 4], [1, 5], [4], [2], [3, 6]], ![[0], [1], [8], [4], [7], [1, 6], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 586 ⟨![[], [1], [2, 0, 5], [0, 4, 5], [3], [5, 6], [1], [0, 2, 4], [0], [3, 6]], ![[8], [1], [2, 8], [4], [2, 7], [3, 3], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 579 ⟨![[0], [], [0, 1, 0, 2], [0, 0, 1], [3], [0], [], [1, 2, 4], [1], [3]], ![[0], [8], [2, 8], [4], [2, 7], [0, 3, 0, 8], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 594 ⟨![[], [0, 1, 4], [2, 0, 5], [0, 4, 5], [3], [5, 6], [1, 0, 6], [0, 2, 4], [0], [3, 6]], ![[8], [1, 8], [2, 8], [4], [2, 7], [3, 3], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 566 ⟨![[0], [1], [2], [3], [], [0, 6], [1], [2, 6], [3, 6], []], ![[0], [1], [2], [3], [2, 2], [0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 581 ⟨![[], [1], [2], [3], [0, 5], [5, 6], [1], [2, 4], [3, 4, 6], [0]], ![[9], [1], [2], [3], [2, 2], [4, 4], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 574 ⟨![[0], [], [2], [3], [1], [0], [], [2, 5], [0, 0, 3], [1]], ![[0], [4], [2], [3], [2, 2], [0, 3, 0, 3], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7]]⟩, .edge 589 ⟨![[], [1, 0, 5], [2], [3], [0, 5], [5, 6], [0, 1], [2, 4], [3, 4, 6], [0]], ![[9], [1, 9], [2], [3], [2, 2], [4, 4], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 570 ⟨![[0], [1], [], [3], [2, 2, 2], [0, 4], [1, 5], [4], [3], [2]], ![[0], [1], [9], [3], [7], [1, 6], [4, 4, 7], [4, 4, 7], [4, 4, 7], [4, 4, 7]]⟩, .edge 585 ⟨![[], [1], [2, 0, 5], [3], [0, 5], [5, 6], [1], [0, 2, 6], [2, 2, 3], [0]], ![[9], [1], [2, 9], [3], [2, 7], [4, 4], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 578 ⟨![[0], [], [2, 1], [3], [1], [0], [], [1, 2, 6], [0, 0, 3], [1]], ![[0], [4], [2, 4], [3], [2, 7], [0, 3, 0, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 593 ⟨![[], [1, 0, 5], [2, 0, 5], [3], [0, 5], [5, 6], [0, 1], [0, 2, 6], [2, 2, 3], [0]], ![[9], [1, 9], [2, 9], [3], [2, 7], [4, 4], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 568 ⟨![[0], [1], [2], [], [2, 3, 2], [0, 3, 3], [0, 0, 1], [2], [4], [3]], ![[0], [1], [2], [9], [8], [0, 5, 8], [4, 4, 8], [4, 4, 8], [4, 4, 8], [4, 4, 8]]⟩, .edge 583 ⟨![[], [1], [2], [3, 0, 5], [0, 5], [5, 6], [1], [2, 4], [0, 3, 6], [0]], ![[9], [1], [2], [3, 9], [2, 2], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 576 ⟨![[0], [], [2], [3, 1], [1], [0], [], [2, 5], [1, 3, 6], [1]], ![[0], [4], [2], [3, 4], [2, 2], [0, 3, 0, 8], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7]]⟩, .edge 591 ⟨![[], [1, 0, 5], [2], [3, 0, 5], [0, 5], [5, 6], [0, 1], [2, 4], [0, 3, 6], [0]], ![[9], [1, 9], [2], [3, 9], [2, 2], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 572 ⟨![[0], [1], [], [2, 2, 2, 3], [2, 2, 2], [0, 4], [1, 5], [4], [2, 3, 6], [2]], ![[0], [1], [9], [3, 9], [7], [1, 6], [4, 4, 7], [4, 4, 7], [4, 4, 7], [4, 4, 7]]⟩, .edge 587 ⟨![[], [1], [2, 0, 5], [3, 0, 5], [0, 5], [5, 6], [1], [0, 2, 6], [0, 3, 6], [0]], ![[9], [1], [2, 9], [3, 9], [2, 7], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 580 ⟨![[0], [], [2, 1], [3, 1], [1], [0], [], [1, 2, 6], [1, 3, 6], [1]], ![[0], [4], [2, 4], [3, 4], [2, 7], [0, 3, 0, 8], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 595 ⟨![[], [1, 0, 5], [2, 0, 5], [3, 0, 5], [0, 5], [5, 6], [0, 1], [0, 2, 6], [0, 3, 6], [0]], ![[9], [1, 9], [2, 9], [3, 9], [2, 7], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 5 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 53) : Classified H :=
  classify_of_checks 53 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node53

namespace Node54

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [3]],
   ![[0], [1], [0, 0], [2], [2, 0, 1, 1, 0], [2, 2], [1, 0, 1, 0], [0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 53) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 54 :=
  generated_of_packed 53 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 598 ⟨![[], [0], [0, 1, 2, 0], [2], [3, 0, 6], [1, 3, 5]], ![[1], [2, 4, 4, 3], [3], [4, 3, 4], [2, 2], [1, 4, 3], [1, 3, 4], [1, 3, 4], [1, 3, 4], [1, 3, 4]]⟩, .core, .edge 600 ⟨![[], [3, 0, 2], [0, 3, 0, 1], [2], [0], [1, 3, 5]], ![[4], [2, 4, 1, 3], [3], [4, 3, 1], [2, 2], [1, 2, 1, 5], [1, 1, 2, 2], [1, 1, 2, 2], [1, 1, 2, 2], [1, 1, 2, 2]]⟩, .edge 596 ⟨![[0], [1], [], [0, 4], [1, 5], [4]], ![[0], [1], [0, 0], [0, 1, 4, 0], [5], [1, 0, 1, 0], [0, 1, 0, 4], [0, 1, 0, 4], [0, 1, 0, 4], [0, 1, 0, 4]]⟩, .edge 599 ⟨![[], [1], [1, 1, 0], [2], [3, 1, 6], [3, 0]], ![[1, 1, 2], [1], [3], [4, 3, 4], [2, 5], [1, 4, 3], [1, 3, 4], [1, 3, 4], [1, 3, 4], [1, 3, 4]]⟩, .edge 597 ⟨![[0], [], [1, 2], [3, 0, 4], [2, 3], [1, 3, 4, 5]], ![[0], [0, 5, 4, 3], [0, 0], [0, 5, 3, 5], [2, 5], [3, 4, 0], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 601 ⟨![[], [0, 0, 3, 0, 1], [2, 3, 0], [2], [0, 1, 6], [3, 0]], ![[1, 4, 2], [1, 1, 4, 2], [3], [4, 3, 1], [2, 5], [1, 2, 4, 2], [1, 1, 2, 5], [1, 1, 2, 5], [1, 1, 2, 5], [1, 1, 2, 5]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 54) : Classified H :=
  classify_of_checks 54 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node54

namespace Node55

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0, 1, 2, 1, 2], [0, 1, 0, 0, 0, 2, 1], [2, 2], [1, 2, 1, 2], [0, 0, 1, 0, 2, 0, 1, 2], [0, 0, 1, 0, 2, 0, 1, 2], [0, 0, 1, 0, 2, 0, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 54) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 55 :=
  generated_of_packed 54 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 603 ⟨![[0], [], [2, 1], [2, 0, 5], [], [2, 1, 4]], ![[0], [0, 2, 3, 0, 0], [0, 3, 0, 0], [0, 0], [0, 3, 3, 0], [0, 0, 0, 5, 0, 2], [0, 0, 2, 3, 5, 3], [0, 0, 2, 3, 5, 3], [0, 0, 2, 3, 5, 3], [0, 0, 2, 3, 5, 3]]⟩, .edge 606 ⟨![[], [0, 0, 0], [2, 1], [3], [0], [1, 2, 2, 2]], ![[4], [1, 3, 5, 1], [1, 1, 3], [3], [1, 2, 4, 2], [2, 4, 5, 1], [1, 1, 2, 1, 1, 5], [1, 1, 2, 1, 1, 5], [1, 1, 2, 1, 1, 5], [1, 1, 2, 1, 1, 5]]⟩, .edge 602 ⟨![[0], [1], [], [0, 3, 3], [1, 4], [3, 3]], ![[0], [1], [0, 0, 0, 4, 0, 4], [0, 0], [1, 4], [0, 0, 0, 1, 4, 0], [0, 0, 1, 0, 0, 4], [0, 0, 1, 0, 0, 4], [0, 0, 1, 0, 0, 4], [0, 0, 1, 0, 0, 4]]⟩, .edge 605 ⟨![[], [1], [0, 3, 2], [3], [1, 2, 5, 6], [0, 2, 6]], ![[1, 4, 5], [1], [2, 1, 4, 5], [3], [3, 4, 3, 4], [4, 5, 1, 2], [1, 5, 4, 2], [1, 5, 4, 2], [1, 5, 4, 2], [1, 5, 4, 2]]⟩, .edge 604 ⟨![[0], [], [2, 1, 5], [2, 0, 5], [], [1, 2, 6]], ![[0], [0, 0, 2, 0, 3], [0, 3, 0, 0], [0, 0], [0, 3, 3, 0], [0, 0, 0, 5, 3, 5], [0, 0, 2, 0, 2, 3], [0, 0, 2, 0, 2, 3], [0, 0, 2, 0, 2, 3], [0, 0, 2, 0, 2, 3]]⟩, .edge 607 ⟨![[], [0, 3, 2, 1], [0, 3, 2], [3], [0, 1, 5], [0, 2, 6]], ![[1, 3, 1, 5], [2, 3, 1], [1, 1, 3], [3], [3, 4, 3, 1], [4, 2, 4, 2], [2, 3, 4, 5, 4], [2, 3, 4, 5, 4], [2, 3, 4, 5, 4], [2, 3, 4, 5, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 55) : Classified H :=
  classify_of_checks 55 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node55

namespace Node56

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0, 1, 0, 0, 1], [2, 0, 2, 0], [2, 2], [0, 0, 0, 2, 0, 2], [0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 55) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 56 :=
  generated_of_packed 55 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 610 ⟨![[], [0], [1], [3, 5, 6], [3, 2, 0], [0, 2, 0, 1]], ![[1], [2], [1, 2, 5, 1], [2, 5, 3], [2, 2], [1, 4, 4, 1], [1, 2, 2, 3, 4], [1, 2, 2, 3, 4], [1, 2, 2, 3, 4], [1, 2, 2, 3, 4]]⟩, .core, .edge 612 ⟨![[], [2, 0, 4], [1], [3, 5, 6], [0], [0, 0, 1, 6]], ![[4], [2], [1, 1, 4, 1], [2, 5, 3], [2, 2], [1, 2, 1, 2], [1, 1, 2, 2], [1, 1, 2, 2], [1, 1, 2, 2], [1, 1, 2, 2]]⟩, .edge 608 ⟨![[0], [1], [], [0, 4, 5], [1, 4], [4]], ![[0], [1], [0, 0, 0, 1, 4, 0], [3, 0, 5], [5], [0, 1, 0, 4], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 611 ⟨![[], [1], [0, 0, 0, 4], [0, 0, 5], [3, 2, 1], [0]], ![[5], [1], [1, 5, 4, 2], [1, 2, 5, 4], [2, 5], [2, 2, 3], [1, 5, 1, 5], [1, 5, 1, 5], [1, 5, 1, 5], [1, 5, 1, 5]]⟩, .edge 609 ⟨![[0], [], [1, 1, 1], [0, 0, 0, 2], [1, 1], [1]], ![[0], [5], [0, 3], [2, 3, 5, 0], [2, 5], [0, 0, 3, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3]]⟩, .edge 613 ⟨![[], [0, 2, 1, 5], [0, 0, 0, 4], [0, 0, 5], [0, 1], [0]], ![[5], [1, 5], [1, 1, 4, 1], [1, 2, 4, 5], [2, 5], [2, 2, 3], [1, 1, 2, 5], [1, 1, 2, 5], [1, 1, 2, 5], [1, 1, 2, 5]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 56) : Classified H :=
  classify_of_checks 56 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node56

namespace Node57

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0, 1, 1, 2], [2, 0, 2, 0], [2, 2], [1, 0, 1, 0], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 56) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 57 :=
  generated_of_packed 56 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 616 ⟨![[], [0], [1, 2, 5], [3], [0, 2], [1, 2, 4, 5]], ![[1], [1, 1, 3, 2], [1, 1, 1, 4], [3], [2, 2, 2, 5], [1, 3, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 618 ⟨![[], [0, 2, 3], [1, 2, 5], [3], [0], [1, 2, 4, 5]], ![[4], [1, 3, 4, 2], [1, 1, 1, 3, 4], [3], [2, 2, 2, 5], [1, 1], [1, 1, 2, 5], [1, 1, 2, 5], [1, 1, 2, 5], [1, 1, 2, 5]]⟩, .edge 614 ⟨![[0], [1], [], [4, 0], [1, 5], [4, 5, 6]], ![[0], [1], [0, 0, 1, 4], [0, 0], [0, 0, 3, 0], [1, 0, 1, 0], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 617 ⟨![[], [1], [0, 1, 4, 1], [3], [1, 2], [0, 2, 5]], ![[1, 1, 5, 3], [1], [1, 1, 1, 4], [3], [1, 2, 3, 5, 4], [1, 3, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 615 ⟨![[0], [], [1, 3, 5], [0, 2, 6], [1, 4, 1], [1, 2, 5]], ![[0], [0, 0, 4, 5], [0, 2, 3, 5, 4], [0, 0], [2, 4, 2], [0, 4, 3], [0, 2, 0, 4, 5], [0, 2, 0, 4, 5], [0, 2, 0, 4, 5], [0, 2, 0, 4, 5]]⟩, .edge 619 ⟨![[], [0, 0, 1, 0], [0, 1, 1], [3], [0, 4, 1], [0, 2, 5]], ![[1, 4, 5, 3], [2, 1, 3], [1, 2, 2, 4], [3], [2, 1, 1, 5], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 57) : Classified H :=
  classify_of_checks 57 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node57

namespace Node58

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [1, 1], [1, 1, 2, 1, 1, 2], [1, 0, 1, 0], [0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 57) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 58 :=
  generated_of_packed 57 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 622 ⟨![[], [0], [1], [2], [0, 2, 3, 5], [2, 1]], ![[1], [2], [3], [1, 1], [1, 4, 2, 5], [1, 4, 3], [1, 2, 5, 4], [1, 2, 5, 4], [1, 2, 5, 4], [1, 2, 5, 4]]⟩, .core, .edge 624 ⟨![[], [0, 0, 3, 0], [1], [2], [0], [2, 1]], ![[4], [2], [3], [1, 4], [1, 2, 1, 3, 5], [1, 1, 4, 4], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 620 ⟨![[0], [1], [], [0, 2, 2, 2], [2, 1], []], ![[0], [1], [0, 0], [1, 1], [1, 1, 4, 4], [1, 0, 1, 0], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 623 ⟨![[], [1], [0], [2], [0, 2, 1, 0], [0]], ![[2], [1], [3], [1, 1], [1, 3, 3, 4, 3], [1, 4, 3], [1, 2, 3, 2, 4], [1, 2, 3, 2, 4], [1, 2, 3, 2, 4], [1, 2, 3, 2, 4]]⟩, .edge 621 ⟨![[0], [], [1, 1, 1], [0, 2, 3, 5], [3], [1]], ![[0], [5], [0, 0], [4], [0, 5, 3, 2], [3, 4, 0], [0, 2, 2, 0, 4], [0, 2, 2, 0, 4], [0, 2, 2, 0, 4], [0, 2, 2, 0, 4]]⟩, .noncentric 96] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 58) : Classified H :=
  classify_of_checks 58 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node58

namespace Node59

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [1, 1], [0, 0, 0, 2, 2, 0], [1, 0, 1, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 58) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 59 :=
  generated_of_packed 58 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 627 ⟨![[], [0], [1], [2], [0, 2, 3, 5], [1, 2, 4]], ![[1], [2], [3], [1, 1], [3, 3, 5, 5], [5, 5], [2, 5, 3], [2, 5, 3], [2, 5, 3], [2, 5, 3]]⟩, .core, .edge 629 ⟨![[], [0, 0, 3, 0], [1], [2], [0], [1, 2, 4]], ![[4], [2], [3], [1, 4], [3, 3, 5, 5], [5, 5], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 625 ⟨![[0], [1], [], [0, 2, 4], [2, 1, 5], [5, 6]], ![[0], [1], [0, 0], [1, 1], [1, 4, 4, 1], [0, 3], [0, 3, 5], [0, 3, 5], [0, 3, 5], [0, 3, 5]]⟩, .edge 628 ⟨![[], [1], [5, 0], [2], [1, 2, 3, 5], [0]], ![[5], [1], [3], [1, 1], [2, 1, 2, 1], [5, 2], [5, 5], [5, 5], [5, 5], [5, 5]]⟩, .edge 626 ⟨![[0], [], [0, 1, 5, 0], [0, 2, 3, 5], [3], [1]], ![[0], [5], [0, 0], [4], [2, 0, 2, 0], [5, 2], [0, 2, 3, 5], [0, 2, 3, 5], [0, 2, 3, 5], [0, 2, 3, 5]]⟩, .noncentric 96] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 59) : Classified H :=
  classify_of_checks 59 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node59

namespace Node60

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [0, 0, 1, 0, 0, 1], [0, 2, 1, 0, 2, 1], [0, 1, 0, 1], [0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 59) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 60 :=
  generated_of_packed 59 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 632 ⟨![[], [0], [1], [2], [0, 3, 2], [2, 1]], ![[1], [2], [3], [3, 1, 3, 1], [4, 2, 5, 1], [4, 3, 1], [1, 2, 4, 2], [1, 2, 4, 2], [1, 2, 4, 2], [1, 2, 4, 2]]⟩, .core, .edge 634 ⟨![[], [3, 0], [1], [2], [0], [2, 1]], ![[4], [2], [3], [1, 4, 4, 4], [3, 3, 4, 4], [4, 4], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 630 ⟨![[0], [1], [], [0, 2, 2, 2], [2, 5, 1], []], ![[0], [1], [0, 0], [3, 3, 4, 1], [0, 4, 3, 1], [0, 1, 0, 1], [0, 1, 3, 4], [0, 1, 3, 4], [0, 1, 3, 4], [0, 1, 3, 4]]⟩, .edge 633 ⟨![[], [1], [0], [2], [1, 3, 2], [0]], ![[2], [1], [3], [3, 1, 3, 1], [2, 1, 2, 1], [4, 3, 1], [2, 4, 2, 4], [2, 4, 2, 4], [2, 4, 2, 4], [2, 4, 2, 4]]⟩, .edge 631 ⟨![[0], [], [1, 1, 1], [0, 3, 2], [3, 5], [1]], ![[0], [5], [0, 0], [5, 4, 2], [0, 5, 3, 2], [0, 3, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .noncentric 96] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 60) : Classified H :=
  classify_of_checks 60 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node60

namespace Node61

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [1, 2, 2, 1], [0, 0, 0, 2, 2, 0], [0, 1, 0, 1], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 60) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 61 :=
  generated_of_packed 60 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 637 ⟨![[], [0], [1], [2], [0, 3, 2], [1, 2, 4]], ![[1], [2], [3], [1, 1, 5, 5], [1, 4, 2, 5], [5, 5], [2, 5, 3], [2, 5, 3], [2, 5, 3], [2, 5, 3]]⟩, .core, .edge 639 ⟨![[], [3, 0], [1], [2], [0], [1, 2, 4]], ![[4], [2], [3], [1, 4, 4, 4], [3, 3, 4, 4], [4, 4], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 635 ⟨![[0], [1], [], [0, 2, 4], [1, 2, 4], [5, 6]], ![[0], [1], [0, 0], [4, 4], [1, 0, 4, 3], [0, 3], [0, 3, 5], [0, 3, 5], [0, 3, 5], [0, 3, 5]]⟩, .edge 638 ⟨![[], [1], [5, 0], [2], [1, 3, 2], [0]], ![[5], [1], [3], [1, 1, 5, 2], [1, 2, 1, 5], [5, 2], [5, 5], [5, 5], [5, 5], [5, 5]]⟩, .edge 636 ⟨![[0], [], [0, 1, 0], [0, 3, 2], [3, 5], [1]], ![[0], [5], [0, 0], [4, 5, 2], [2, 0, 5, 3], [5, 2], [0, 2, 3, 5], [0, 2, 3, 5], [0, 2, 3, 5], [0, 2, 3, 5]]⟩, .noncentric 96] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 61) : Classified H :=
  classify_of_checks 61 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node61

namespace Node62

def gen : Fin 5 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [3], [4]],
   ![[0], [1], [2], [3], [4], [0, 0, 4, 4], [0, 2, 0, 2], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 61) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 62 :=
  generated_of_packed 61 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .core, .edge 647 ⟨![[0], [], [1], [2], [3], [0], [], [0, 0, 1], [2, 2, 2], [0, 0, 3]], ![[0], [2], [3], [4], [4, 9], [0, 2, 0, 2], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7]]⟩, .edge 662 ⟨![[], [0, 0, 0], [1], [2], [3], [0, 0], [0], [1, 6], [2, 4], [0, 3, 0]], ![[6], [2], [3], [4], [4, 4, 5], [3, 8], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 643 ⟨![[0], [1], [], [2], [3], [0, 6], [0, 0, 1], [], [2, 6], [3, 6]], ![[0], [1], [3], [4], [0, 0, 3, 8], [0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 658 ⟨![[], [1], [0, 5], [2], [3], [5, 6], [1], [0], [2, 4], [3, 4, 6]], ![[7], [1], [3], [4], [4, 4, 5], [2, 2], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 651 ⟨![[0], [], [0, 0, 1], [2], [3], [0], [], [1], [2, 2, 2], [0, 0, 3]], ![[0], [7], [3], [4], [4, 9], [0, 2, 0, 7], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 666 ⟨![[], [0, 1], [0, 5], [2], [3], [1, 1], [1, 0, 6], [0], [2, 4], [3, 4, 6]], ![[7], [1, 7], [3], [4], [4, 4, 5], [2, 2], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 641 ⟨![[0], [1], [2], [], [3], [0, 4], [1, 4, 5], [2, 6], [4, 5], [3, 6]], ![[0], [1], [2], [4], [0, 0, 0, 5], [0, 0, 2, 7], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 656 ⟨![[], [1], [2], [0, 3, 3], [3], [5, 6], [1], [2, 6], [0], [0, 3, 0]], ![[8], [1], [2], [4], [4, 4, 5], [4, 9], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 649 ⟨![[0], [], [2], [1, 4, 5], [3], [0], [], [0, 0, 2], [1], [0, 0, 3]], ![[0], [8], [2], [4], [4, 9], [0, 2, 0, 2], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7]]⟩, .edge 664 ⟨![[], [1, 0, 6], [2], [0, 3, 3], [3], [5, 6], [0, 1], [2, 6], [0], [0, 3, 0]], ![[8], [1, 8], [2], [4], [4, 4, 5], [4, 9], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 645 ⟨![[0], [1], [], [2, 6], [3], [0, 6], [0, 0, 1], [], [2], [3, 6]], ![[0], [1], [8], [4], [0, 0, 3, 3], [0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 660 ⟨![[], [1], [2, 0, 6], [0, 2, 2], [3], [5, 6], [1], [0, 2, 2, 2], [0], [0, 3, 0]], ![[8], [1], [2, 8], [4], [4, 4, 5], [2, 2], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 653 ⟨![[0], [], [2, 1], [1, 4, 5], [3], [0], [], [0, 0, 2, 1], [1], [0, 0, 3]], ![[0], [8], [2, 8], [4], [4, 9], [0, 2, 0, 7], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 668 ⟨![[], [1, 0, 6], [2, 0, 6], [0, 2, 2], [3], [5, 6], [0, 1], [0, 2, 2, 2], [0], [0, 3, 0]], ![[8], [1, 8], [2, 8], [4], [4, 4, 5], [2, 2], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 640 ⟨![[0], [1], [2], [3], [], [0, 4, 6], [0, 0, 1], [2, 6], [3, 6], [0, 0, 4]], ![[0], [1], [2], [3], [0, 0, 9], [0, 0, 2, 7], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 655 ⟨![[], [1], [2], [3], [0, 3, 3], [5, 6], [1], [2, 6], [3, 4], [0]], ![[9], [1], [2], [3], [4, 5, 9], [3, 8], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 648 ⟨![[0], [], [2], [3], [0, 0, 1], [0], [], [0, 0, 2], [3, 3, 3], [1]], ![[0], [9], [2], [3], [4, 4], [0, 2, 0, 2], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7]]⟩, .edge 663 ⟨![[], [1, 0, 6], [2], [3], [0, 3, 3], [5, 6], [0, 1, 4], [2, 6], [3, 4], [0]], ![[9], [1, 9], [2], [3], [4, 5, 9], [3, 8], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 644 ⟨![[0], [1], [], [3], [2, 6], [0, 6], [0, 0, 1], [], [3, 6], [2]], ![[0], [1], [9], [3], [0, 0, 3, 8], [0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 659 ⟨![[], [1], [0, 2, 4], [3], [0, 2, 2], [5, 6], [1], [0, 2, 2, 2], [3, 4], [0]], ![[9], [1], [2, 9], [3], [4, 5, 9], [2, 2], [4, 4], [4, 4], [4, 4], [4, 4]]⟩, .edge 652 ⟨![[0], [], [2, 1, 4], [3], [0, 0, 1], [0], [], [0, 1, 0, 2], [2, 2, 3], [1]], ![[0], [9], [2, 9], [3], [4, 4], [0, 2, 0, 7], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 667 ⟨![[], [1, 0, 6], [0, 2, 4], [3], [0, 2, 2], [5, 6], [0, 1, 4], [0, 2, 2, 2], [3, 4], [0]], ![[9], [1, 9], [2, 9], [3], [4, 5, 9], [2, 2], [4, 4], [4, 4], [4, 4], [4, 4]]⟩, .edge 642 ⟨![[0], [1], [2], [], [0, 0, 3, 4], [0, 4], [1, 4, 5], [2, 6], [4, 5], [3]], ![[0], [1], [2], [9], [0, 0, 0, 5], [0, 0, 2, 7], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 657 ⟨![[], [1], [2], [0, 3, 6], [0, 4, 5], [5, 6], [1], [2, 6], [0, 3, 4, 5], [0]], ![[9], [1], [2], [3, 9], [4, 5, 9], [2, 5, 7], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 650 ⟨![[0], [], [2], [1, 3], [0, 0, 1], [0], [], [0, 0, 2], [3, 1, 5], [1]], ![[0], [9], [2], [3, 9], [4, 4], [0, 2, 0, 2], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7]]⟩, .edge 665 ⟨![[], [1, 0, 6], [2], [0, 3, 6], [0, 4, 5], [5, 6], [0, 1, 4], [2, 6], [0, 3, 4, 5], [0]], ![[9], [1, 9], [2], [3, 9], [4, 5, 9], [2, 5, 7], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 646 ⟨![[0], [1], [], [0, 2, 0, 3], [2, 6], [0, 6], [0, 0, 1], [], [0, 2, 3, 0], [2]], ![[0], [1], [9], [3, 9], [0, 0, 3, 3], [0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 661 ⟨![[], [1], [0, 2, 4], [0, 3, 6], [0, 2, 2], [5, 6], [1], [0, 2, 2, 2], [0, 2, 2, 3], [0]], ![[9], [1], [2, 9], [3, 9], [4, 5, 9], [2, 2], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 654 ⟨![[0], [], [2, 1, 4], [1, 3], [0, 0, 1], [0], [], [0, 1, 0, 2], [3, 1, 5], [1]], ![[0], [9], [2, 9], [3, 9], [4, 4], [0, 2, 0, 7], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 669 ⟨![[], [1, 0, 6], [0, 2, 4], [0, 3, 6], [0, 2, 2], [5, 6], [0, 1, 4], [0, 2, 2, 2], [0, 2, 2, 3], [0]], ![[9], [1, 9], [2, 9], [3, 9], [4, 5, 9], [2, 2], [3, 3], [3, 3], [3, 3], [3, 3]]⟩] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 5 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 62) : Classified H :=
  classify_of_checks 62 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node62

namespace Node63

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 3, 1], [1, 0, 3, 1, 3, 0], [1, 0, 3, 1, 0, 3], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 62) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 63 :=
  generated_of_packed 62 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 672 ⟨![[], [0], [1], [3, 2, 5], [], [0, 3], [1, 6], [0, 2, 0, 4]], ![[1], [2], [1, 3, 1], [1, 1, 1, 5], [1, 3, 3, 5], [3, 5, 7, 1], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .core, .edge 674 ⟨![[], [0, 3], [1], [3, 2, 5], [], [0], [1, 6], [0, 3, 2, 0]], ![[5], [2], [1, 7, 5], [1, 1, 1, 5], [1, 1, 3, 3], [3, 5, 3, 5], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .noncentric 96, .noncentric 96, .noncentric 96, .noncentric 96, .edge 670 ⟨![[0], [1], [2], [], [0, 4, 6], [5, 1], [2, 6], [4, 6]], ![[0], [1], [2], [5, 5], [2, 6, 7], [0, 1, 0, 5], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 673 ⟨![[], [1], [2], [0, 3, 4, 5], [], [1, 3], [2, 6], [3, 0, 5]], ![[5, 7, 1], [1], [2], [1, 1, 1, 5], [1, 3, 7, 5], [3, 1, 3, 1], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 671 ⟨![[0], [], [2], [1, 6], [0, 3], [3, 6], [2, 6], [3, 1, 5]], ![[0], [2, 3, 6], [2], [0, 4], [2, 3, 6, 7], [0, 7, 0, 7], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 675 ⟨![[], [1, 0], [2], [0, 1, 1, 6], [], [1, 0, 3], [2, 6], [3, 0, 5]], ![[5, 3, 5], [3, 1], [2], [1, 1, 1, 5], [1, 1, 3, 7], [3, 1, 7, 5], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .noncentric 96, .noncentric 96, .noncentric 96, .noncentric 96] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 63) : Classified H :=
  classify_of_checks 63 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node63

namespace Node64

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0, 1, 2, 1], [0, 0, 1, 0, 1, 0], [2, 2], [1, 2, 1, 2, 2, 2], [0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 63) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 64 :=
  generated_of_packed 63 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 677 ⟨![[0], [], [0, 1, 0, 5], [0, 3], [], [1, 2]], ![[0], [0, 0, 5], [0, 0], [0, 0, 0, 3], [2, 2], [0, 0, 0, 2, 2, 2, 5, 0], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 680 ⟨![[], [0, 0, 0], [0, 1, 3, 0], [2], [0], [0, 1, 3, 0]], ![[4], [1, 2, 4, 3], [3], [1, 1, 3], [2, 2], [2, 2, 2, 4, 2, 1], [1, 3, 4, 3], [1, 3, 4, 3], [1, 3, 4, 3], [1, 3, 4, 3]]⟩, .edge 676 ⟨![[0], [1], [], [0], [1, 5, 6], [4]], ![[0], [1], [0, 0], [0, 0, 0, 1, 0, 1], [5], [0, 0, 0, 1, 4, 0], [0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 1]]⟩, .edge 679 ⟨![[], [1], [5, 0], [2], [1, 3, 6], [2, 5, 0]], ![[1, 5, 4, 3], [1], [3], [1, 3, 4, 3], [2, 5], [1, 2, 2, 2, 4, 2], [1, 3, 1, 3], [1, 3, 1, 3], [1, 3, 1, 3], [1, 3, 1, 3]]⟩, .edge 678 ⟨![[0], [], [1, 2], [0, 3], [], [2, 1, 5]], ![[0], [2, 0, 0], [0, 0], [0, 0, 0, 3], [2, 5], [0, 0, 0, 2, 2, 0, 2, 5], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 681 ⟨![[], [1, 0, 0, 0], [5, 0], [2], [0, 1, 1, 1], [2, 5, 0]], ![[1, 2, 1, 3], [2, 4, 3], [3], [1, 1, 3], [2, 5], [1, 2, 1, 2, 2, 5], [1, 3, 4, 3], [1, 3, 4, 3], [1, 3, 4, 3], [1, 3, 4, 3]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 64) : Classified H :=
  classify_of_checks 64 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node64

namespace Node65

def gen : Fin 5 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [3], [4]],
   ![[0], [1], [2], [3], [4], [2, 2], [0, 3, 0, 3], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 64) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 65 :=
  generated_of_packed 64 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .core, .edge 689 ⟨![[0], [], [1], [2], [3], [0], [], [1, 5], [0, 0, 2], [3]], ![[0], [2], [3], [4], [2, 2], [0, 3, 0, 3], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8]]⟩, .edge 704 ⟨![[], [0, 0, 0], [1], [2], [3], [0, 0], [0], [1], [0, 2, 0], [3, 5]], ![[6], [2], [3], [4], [2, 2], [4, 9], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 685 ⟨![[0], [1], [], [2], [3], [0], [1, 5], [4], [2], [3, 6]], ![[0], [1], [3], [4], [7], [1, 6], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 700 ⟨![[], [1], [0, 5, 6], [2], [3], [5, 6], [1], [0], [2, 4, 6], [3, 5]], ![[7], [1], [3], [4], [2, 7], [4, 9], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 693 ⟨![[0], [], [1, 5], [2], [3], [0], [], [1], [0, 0, 2], [3]], ![[0], [7], [3], [4], [2, 7], [0, 3, 0, 3], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8]]⟩, .edge 708 ⟨![[], [0, 0, 1, 0], [0, 5, 6], [2], [3], [5, 6], [1, 0, 4], [0], [1, 2, 1], [3, 5]], ![[7], [1, 7], [3], [4], [2, 7], [4, 9], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 683 ⟨![[0], [1], [2], [], [3], [0, 4, 6], [0, 0, 1], [2], [4], [3, 6]], ![[0], [1], [2], [4], [8], [0, 5, 8], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 698 ⟨![[], [1], [2], [0, 4, 5], [3], [5, 6], [1], [2], [0], [3, 5]], ![[8], [1], [2], [4], [2, 2], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 691 ⟨![[0], [], [2], [0, 0, 1], [3], [0], [], [2, 5], [1], [3]], ![[0], [8], [2], [4], [2, 2], [0, 3, 0, 8], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 706 ⟨![[], [0, 1, 4], [2], [0, 4, 5], [3], [5, 6], [1, 0, 6], [2], [0], [3, 5]], ![[8], [1, 8], [2], [4], [2, 2], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 687 ⟨![[0], [1], [], [2, 4], [3], [0], [1, 5], [4], [2], [3, 6]], ![[0], [1], [8], [4], [7], [1, 6], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 702 ⟨![[], [1], [2, 0, 5], [0, 4, 5], [3], [5, 6], [1], [0, 2, 4], [0], [3, 5]], ![[8], [1], [2, 8], [4], [2, 7], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 695 ⟨![[0], [], [0, 1, 0, 2], [0, 0, 1], [3], [0], [], [1, 2, 4], [1], [3]], ![[0], [8], [2, 8], [4], [2, 7], [0, 3, 0, 8], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 710 ⟨![[], [0, 1, 4], [2, 0, 5], [0, 4, 5], [3], [5, 6], [1, 0, 6], [0, 2, 4], [0], [3, 5]], ![[8], [1, 8], [2, 8], [4], [2, 7], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 682 ⟨![[0], [1], [2], [3], [], [0, 5], [1], [2, 6], [3, 6], []], ![[0], [1], [2], [3], [2, 2], [0, 0, 0, 5], [0, 5], [0, 5], [0, 5], [0, 5]]⟩, .edge 697 ⟨![[], [1], [2], [3], [0, 6], [5, 6], [1], [2], [0, 3, 0], [0]], ![[9], [1], [2], [3], [2, 2], [3, 5, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 690 ⟨![[0], [], [2], [3], [1], [0], [], [2, 5], [0, 0, 3], [1]], ![[0], [4], [2], [3], [2, 2], [0, 3, 0, 3], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8]]⟩, .edge 705 ⟨![[], [1, 0, 6], [2], [3], [0, 6], [5, 6], [0, 1], [2], [0, 3, 0], [0]], ![[9], [1, 9], [2], [3], [2, 2], [3, 5, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 686 ⟨![[0], [1], [], [3], [2, 2, 2], [0], [1, 5], [4], [3], [2]], ![[0], [1], [9], [3], [7], [1, 6], [4, 4, 7], [4, 4, 7], [4, 4, 7], [4, 4, 7]]⟩, .edge 701 ⟨![[], [1], [0, 2, 5], [3], [0, 6], [5, 6], [1], [0, 2, 6], [0, 3, 0], [0]], ![[9], [1], [2, 9], [3], [2, 7], [3, 5, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 694 ⟨![[0], [], [2, 1], [3], [1], [0], [], [1, 2, 6], [0, 0, 3], [1]], ![[0], [4], [2, 4], [3], [2, 7], [0, 3, 0, 3], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8]]⟩, .edge 709 ⟨![[], [1, 0, 6], [0, 2, 5], [3], [0, 6], [5, 6], [0, 1], [0, 2, 6], [0, 3, 0], [0]], ![[9], [1, 9], [2, 9], [3], [2, 7], [3, 5, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 684 ⟨![[0], [1], [2], [], [2, 3, 2], [0, 3, 3], [0, 0, 1], [2], [4], [3]], ![[0], [1], [2], [9], [8], [0, 5, 8], [4, 4, 8], [4, 4, 8], [4, 4, 8], [4, 4, 8]]⟩, .edge 699 ⟨![[], [1], [2], [3, 0, 6], [0, 6], [5, 6], [1], [2], [0, 3, 6], [0]], ![[9], [1], [2], [3, 9], [2, 2], [3, 3], [4, 4], [4, 4], [4, 4], [4, 4]]⟩, .edge 692 ⟨![[0], [], [2], [3, 1], [1], [0], [], [2, 5], [1, 3, 6], [1]], ![[0], [4], [2], [3, 4], [2, 2], [0, 3, 0, 8], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 707 ⟨![[], [1, 0, 6], [2], [3, 0, 6], [0, 6], [5, 6], [0, 1], [2], [0, 3, 6], [0]], ![[9], [1, 9], [2], [3, 9], [2, 2], [3, 3], [4, 4], [4, 4], [4, 4], [4, 4]]⟩, .edge 688 ⟨![[0], [1], [], [2, 2, 2, 3], [2, 2, 2], [0], [1, 5], [4], [2, 3, 6], [2]], ![[0], [1], [9], [3, 9], [7], [1, 6], [4, 4, 7], [4, 4, 7], [4, 4, 7], [4, 4, 7]]⟩, .edge 703 ⟨![[], [1], [0, 2, 5], [3, 0, 6], [0, 6], [5, 6], [1], [0, 2, 6], [0, 3, 6], [0]], ![[9], [1], [2, 9], [3, 9], [2, 7], [3, 3], [4, 4], [4, 4], [4, 4], [4, 4]]⟩, .edge 696 ⟨![[0], [], [2, 1], [3, 1], [1], [0], [], [1, 2, 6], [1, 3, 6], [1]], ![[0], [4], [2, 4], [3, 4], [2, 7], [0, 3, 0, 8], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 711 ⟨![[], [1, 0, 6], [0, 2, 5], [3, 0, 6], [0, 6], [5, 6], [0, 1], [0, 2, 6], [0, 3, 6], [0]], ![[9], [1, 9], [2, 9], [3, 9], [2, 7], [3, 3], [4, 4], [4, 4], [4, 4], [4, 4]]⟩] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 5 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 65) : Classified H :=
  classify_of_checks 65 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node65

namespace Node66

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0, 0, 1, 1, 2, 0, 2, 2], [2, 0, 2, 0], [2, 2], [0, 0, 0, 2, 0, 2], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 65) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 66 :=
  generated_of_packed 65 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 714 ⟨![[], [0], [0, 1, 0, 5], [3], [0, 2], [0, 1, 0, 1, 1]], ![[1], [1, 2, 2, 5, 1], [1, 1, 1, 4], [3], [2, 2, 2, 5], [2, 5], [1, 3, 4], [1, 3, 4], [1, 3, 4], [1, 3, 4]]⟩, .core, .edge 716 ⟨![[], [0, 2, 3], [1, 2, 3, 5], [3], [0], [1, 1, 1, 2, 3]], ![[4], [1, 1, 1, 2, 2, 2, 4], [1, 1, 1, 3, 4], [3], [2, 2, 2, 5], [2, 5], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 712 ⟨![[0], [1], [], [4, 0], [1], [4, 5]], ![[0], [1], [1, 1, 3, 3], [0, 0], [0, 0, 3, 0], [0, 0, 3, 0, 5], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 715 ⟨![[], [1], [2, 0, 4, 5], [3], [1, 2], [0, 0, 0, 2]], ![[1, 1, 2, 2, 5, 3], [1], [1, 1, 1, 4], [3], [2, 2, 2, 3, 5], [2, 3, 2], [1, 3, 4], [1, 3, 4], [1, 3, 4], [1, 3, 4]]⟩, .edge 713 ⟨![[0], [], [5, 1], [0, 2], [2, 3, 6], [1, 1, 1, 4]], ![[0], [2, 0, 2, 0, 2], [0, 0, 0, 3], [0, 0], [2, 0, 2, 0, 2, 5], [2, 0, 2, 0], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4]]⟩, .edge 717 ⟨![[], [0, 0, 1, 0], [0, 1, 3, 1], [3], [0, 4, 1, 5], [0, 0, 0, 2]], ![[1, 2, 1, 2, 2, 3], [2, 1, 2, 3, 2], [1, 1, 1, 3, 4], [3], [2, 2, 2, 3, 5], [2, 3, 2], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 66) : Classified H :=
  classify_of_checks 66 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node66

namespace Node67

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 1, 1, 1, 0, 1], [0, 1, 1, 0, 2, 1, 2, 1], [1, 1, 1, 1], [0, 1, 1, 0, 2, 1, 1, 2], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 66) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 67 :=
  generated_of_packed 66 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 720 ⟨![[], [0], [1], [], [0, 2], [1, 3, 5, 6]], ![[1], [2], [1, 5, 1, 2], [1, 1, 4, 2, 5, 4], [1, 1, 1, 1], [1, 1, 1, 1, 1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 722 ⟨![[], [0, 2], [1], [], [0], [1, 3, 5, 6]], ![[4], [2], [1, 2, 4, 2], [1, 1, 1, 5, 1, 2], [1, 4, 1, 4], [1, 1, 1, 4, 1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 718 ⟨![[0], [1], [], [3, 0, 5], [3, 1], []], ![[0], [1], [1, 0, 3, 4], [0, 1, 1, 0, 4, 1], [0, 4, 0, 4], [0, 1, 1, 0, 4, 4], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩, .edge 721 ⟨![[], [1], [0, 0, 0], [], [1, 2], [0]], ![[5], [1], [1, 5, 4, 5], [1, 1, 4, 2, 2, 4], [1, 1, 1, 1], [1, 1, 1, 1, 1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 719 ⟨![[0], [], [1, 3, 2, 4], [0, 2, 6], [2, 5], [1]], ![[0], [5], [5, 4, 2], [2, 4, 2], [4, 4], [0, 4, 3], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 723 ⟨![[], [0, 3, 1, 2], [0, 0, 0], [], [0, 3, 1], [0]], ![[5], [1, 5], [1, 2, 1, 5], [1, 1, 1, 5, 4, 5], [1, 4, 1, 4], [1, 1, 1, 4, 1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 67) : Classified H :=
  classify_of_checks 67 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node67

namespace Node68

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 1, 1, 1, 0, 1], [2, 0, 2, 0], [1, 1, 1, 1], [1, 1, 1, 1, 2, 2], [0, 1, 0, 1, 2, 2], [0, 1, 0, 1, 2, 2], [0, 1, 0, 1, 2, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 67) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 68 :=
  generated_of_packed 67 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 726 ⟨![[], [0], [1], [], [0, 2], [1, 1, 1, 3]], ![[1], [2], [4, 1, 4, 4], [2, 5], [1, 1, 1, 1], [1, 2, 4, 5], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 728 ⟨![[], [0, 2], [1], [], [0], [0, 0, 3, 1]], ![[4], [2], [4, 1, 4, 4], [2, 5], [1, 4, 1, 4], [1, 5, 1, 5], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 724 ⟨![[0], [1], [], [1, 0, 1, 3], [3, 1, 4], [4, 5]], ![[0], [1], [1, 0, 3, 4], [0, 5, 3], [0, 4, 0, 4], [0, 1, 3, 5, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 727 ⟨![[], [1], [0, 3, 4, 5], [], [1, 2], [0]], ![[5], [1], [4, 1, 4, 4], [2, 2], [1, 1, 1, 1], [1, 2, 1, 2], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 725 ⟨![[0], [], [1, 2, 3], [0, 2, 6], [2, 5], [1]], ![[0], [5], [0, 2, 3, 2], [4, 2, 2], [4, 4], [0, 4, 3], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 729 ⟨![[], [0, 1, 3, 2], [0, 2, 1, 1], [], [0, 1, 3], [0]], ![[5], [1, 5], [4, 1, 4, 4], [2, 2], [1, 4, 1, 4], [1, 5, 4, 2], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 68) : Classified H :=
  classify_of_checks 68 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node68

namespace Node69

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [1, 0, 1, 0, 1, 1], [0, 2, 1, 0, 1, 2], [1, 1, 1, 1], [1, 0, 1, 0], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 68) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 69 :=
  generated_of_packed 68 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 732 ⟨![[], [0], [1], [], [0, 2, 4], [1, 3, 5, 6]], ![[1], [2], [1, 1, 1, 4], [2, 4, 1, 5], [1, 1, 1, 1], [1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 734 ⟨![[], [0, 2, 4], [1], [], [0], [0, 0, 1, 3]], ![[4], [2], [1, 1, 1, 4], [2, 4, 4, 5], [1, 4, 1, 4], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 730 ⟨![[0], [1], [], [3, 0, 5], [1, 3, 6], []], ![[0], [1], [1, 4, 0, 3], [0, 4, 0, 1], [1, 1, 1, 1], [1, 0, 1, 0], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 733 ⟨![[], [1], [0, 0, 0], [], [1, 2, 4], [0]], ![[5], [1], [1, 1, 1, 4], [2, 1, 4, 2], [1, 1, 1, 1], [1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 731 ⟨![[0], [], [0, 1, 0, 5], [2, 0, 6], [2, 5], [1]], ![[0], [5], [5, 4, 2], [4, 2, 2], [4, 4], [3, 4, 0], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 735 ⟨![[], [3, 1, 0], [0, 0, 0], [], [0, 0, 0, 1], [0]], ![[5], [1, 5], [1, 1, 1, 4], [2, 1, 1, 2], [1, 4, 1, 4], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 69) : Classified H :=
  classify_of_checks 69 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node69

namespace Node70

def gen : Fin 5 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [3], [4]],
   ![[0], [1], [2], [3], [4], [3, 3], [0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 69) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 70 :=
  generated_of_packed 69 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .core, .edge 743 ⟨![[0], [], [1], [2], [3], [0], [], [1], [2, 4], [3]], ![[0], [2], [3], [4], [3, 3], [0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4]]⟩, .edge 758 ⟨![[], [0, 0, 0], [1], [2], [3], [0, 0], [0], [1], [2, 4], [3, 4, 6]], ![[6], [2], [3], [4], [3, 3], [4, 5, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 739 ⟨![[0], [1], [], [2], [3], [0], [1], [], [2, 5], [0, 0, 3]], ![[0], [1], [3], [4], [3, 3], [0, 4, 0, 4], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8]]⟩, .edge 754 ⟨![[], [1], [0, 0, 0], [2], [3], [0, 0], [1], [0], [2, 4], [0, 3, 0]], ![[7], [1], [3], [4], [3, 3], [4, 5, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 747 ⟨![[0], [], [1], [2], [3], [0], [], [1], [2, 4], [3]], ![[0], [2], [3], [4], [3, 3], [0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4]]⟩, .edge 762 ⟨![[], [0, 0, 0, 1], [0, 0, 0], [2], [3], [0, 0], [0, 1], [0], [2, 4], [0, 3, 0]], ![[7], [1, 7], [3], [4], [3, 3], [4, 5, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 737 ⟨![[0], [1], [2], [], [3], [0, 4], [1, 4], [2, 5], [4], [3]], ![[0], [1], [2], [4], [8], [2, 7], [0, 0, 2, 7], [0, 0, 2, 7], [0, 0, 2, 7], [0, 0, 2, 7]]⟩, .edge 752 ⟨![[], [1], [2], [0, 0, 0, 4], [3], [0, 0], [1], [2], [0], [3, 4, 6]], ![[8], [1], [2], [4], [3, 8], [4, 5, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 745 ⟨![[0], [], [2], [1, 4], [3], [0], [], [2], [1], [3]], ![[0], [8], [2], [4], [3, 8], [0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4]]⟩, .edge 760 ⟨![[], [0, 0, 0, 1], [2], [0, 0, 0, 4], [3], [0, 0], [0, 1], [2], [0], [3, 4, 6]], ![[8], [1, 8], [2], [4], [3, 8], [4, 5, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 741 ⟨![[0], [1], [], [2, 5], [3], [0], [1], [], [2], [0, 0, 3]], ![[0], [1], [8], [4], [3, 8], [0, 4, 0, 4], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 756 ⟨![[], [1], [0, 0, 2, 0], [0, 0, 0, 4], [3], [0, 0], [1], [2, 0], [0], [2, 3, 2]], ![[8], [1], [2, 8], [4], [3, 8], [4, 5, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 749 ⟨![[0], [], [2, 1], [1, 4], [3], [0], [], [2, 1], [1], [3]], ![[0], [8], [2, 8], [4], [3, 8], [0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4]]⟩, .edge 764 ⟨![[], [0, 0, 0, 1], [0, 0, 2, 0], [0, 0, 0, 4], [3], [0, 0], [0, 1], [2, 0], [0], [2, 3, 2]], ![[8], [1, 8], [2, 8], [4], [3, 8], [4, 5, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 736 ⟨![[0], [1], [2], [3], [], [0, 4, 6], [1], [0, 0, 2], [3], [4]], ![[0], [1], [2], [3], [9], [0, 5, 9], [0, 0, 0, 5, 9], [0, 0, 0, 5, 9], [0, 0, 0, 5, 9], [0, 0, 0, 5, 9]]⟩, .edge 751 ⟨![[], [1], [2], [3], [0, 4, 5], [5, 6], [1], [2], [3, 4], [0]], ![[9], [1], [2], [3], [3, 3], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩, .edge 744 ⟨![[0], [], [2], [3], [1], [0], [], [2], [3, 4], [1]], ![[0], [4], [2], [3], [3, 3], [0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4]]⟩, .edge 759 ⟨![[], [1, 0, 5], [2], [3], [0, 4, 5], [5, 6], [0, 1, 4], [2], [3, 4], [0]], ![[9], [1, 9], [2], [3], [3, 3], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩, .edge 740 ⟨![[0], [1], [], [3], [0, 0, 2], [0], [1], [], [3, 5], [2]], ![[0], [1], [9], [3], [3, 3], [0, 4, 0, 9], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8]]⟩, .edge 755 ⟨![[], [1], [0, 2, 4], [3], [0, 4, 5], [5, 6], [1], [2, 0, 6], [3, 4], [0]], ![[9], [1], [2, 9], [3], [3, 3], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩, .edge 748 ⟨![[0], [], [2, 1, 4], [3], [1], [0], [], [2, 1, 4], [3, 4], [1]], ![[0], [4], [2, 4], [3], [3, 3], [0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4]]⟩, .edge 763 ⟨![[], [1, 0, 5], [0, 2, 4], [3], [0, 4, 5], [5, 6], [0, 1, 4], [2, 0, 6], [3, 4], [0]], ![[9], [1, 9], [2, 9], [3], [3, 3], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩, .edge 738 ⟨![[0], [1], [2], [], [3, 4], [0, 4], [1, 4], [2, 5], [4], [3]], ![[0], [1], [2], [9], [8], [2, 7], [0, 0, 2, 7], [0, 0, 2, 7], [0, 0, 2, 7], [0, 0, 2, 7]]⟩, .edge 753 ⟨![[], [1], [2], [3, 0, 5], [0, 4, 5], [5, 6], [1], [2], [0, 3, 4], [0]], ![[9], [1], [2], [3, 9], [3, 8], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩, .edge 746 ⟨![[0], [], [2], [1, 3], [1], [0], [], [2], [3, 1], [1]], ![[0], [4], [2], [3, 4], [3, 8], [0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4]]⟩, .edge 761 ⟨![[], [1, 0, 5], [2], [3, 0, 5], [0, 4, 5], [5, 6], [0, 1, 4], [2], [0, 3, 4], [0]], ![[9], [1, 9], [2], [3, 9], [3, 8], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩, .edge 742 ⟨![[0], [1], [], [0, 2, 0, 3], [0, 0, 2], [0], [1], [], [2, 3, 4], [2]], ![[0], [1], [9], [3, 9], [3, 8], [0, 4, 0, 9], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 757 ⟨![[], [1], [0, 2, 4], [3, 0, 5], [0, 4, 5], [5, 6], [1], [2, 0, 6], [0, 3, 4], [0]], ![[9], [1], [2, 9], [3, 9], [3, 8], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩, .edge 750 ⟨![[0], [], [2, 1, 4], [1, 3], [1], [0], [], [2, 1, 4], [3, 1], [1]], ![[0], [4], [2, 4], [3, 4], [3, 8], [0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4]]⟩, .edge 765 ⟨![[], [1, 0, 5], [0, 2, 4], [3, 0, 5], [0, 4, 5], [5, 6], [0, 1, 4], [2, 0, 6], [0, 3, 4], [0]], ![[9], [1, 9], [2, 9], [3, 9], [3, 8], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 5 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 70) : Classified H :=
  classify_of_checks 70 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node70

namespace Node71

def gen : Fin 5 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [3], [4]],
   ![[0], [1], [2], [3], [4], [3, 3], [0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 70) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 71 :=
  generated_of_packed 70 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .core, .edge 773 ⟨![[0], [], [1], [2], [3], [0], [], [1], [2, 4], [0, 0, 3]], ![[0], [2], [3], [4], [3, 3], [0, 4, 0, 4], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9]]⟩, .edge 788 ⟨![[], [0, 0, 0], [1], [2], [3], [0, 0], [0], [1], [2, 4], [3, 6]], ![[6], [2], [3], [4], [3, 3], [4, 5, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 769 ⟨![[0], [1], [], [2], [3], [0], [1], [], [2, 5], [3]], ![[0], [1], [3], [4], [3, 3], [0, 4, 0, 4], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8]]⟩, .edge 784 ⟨![[], [1], [0, 0, 0], [2], [3], [0, 0], [1], [0], [2, 4], [3, 6]], ![[7], [1], [3], [4], [3, 3], [4, 5, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 777 ⟨![[0], [], [1], [2], [3], [0], [], [1], [2, 4], [0, 0, 3]], ![[0], [2], [3], [4], [3, 3], [0, 4, 0, 4], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9]]⟩, .edge 792 ⟨![[], [0, 0, 0, 1], [0, 0, 0], [2], [3], [0, 0], [0, 1], [0], [2, 4], [3, 6]], ![[7], [1, 7], [3], [4], [3, 3], [4, 5, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 767 ⟨![[0], [1], [2], [], [3], [0, 4], [1, 4], [2, 5], [4], [3, 6]], ![[0], [1], [2], [4], [8], [2, 7], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 782 ⟨![[], [1], [2], [0, 0, 0, 4], [3], [0, 0], [1], [2], [0], [3, 6]], ![[8], [1], [2], [4], [3, 8], [4, 5, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 775 ⟨![[0], [], [2], [1, 4], [3], [0], [], [2], [1], [0, 0, 3]], ![[0], [8], [2], [4], [3, 8], [0, 4, 0, 4], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9]]⟩, .edge 790 ⟨![[], [0, 0, 0, 1], [2], [0, 0, 0, 4], [3], [0, 0], [0, 1], [2], [0], [3, 6]], ![[8], [1, 8], [2], [4], [3, 8], [4, 5, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 771 ⟨![[0], [1], [], [2, 5], [3], [0], [1], [], [2], [3]], ![[0], [1], [8], [4], [3, 8], [0, 4, 0, 4], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 786 ⟨![[], [1], [0, 0, 2, 0], [0, 0, 0, 4], [3], [0, 0], [1], [2, 0], [0], [3, 6]], ![[8], [1], [2, 8], [4], [3, 8], [4, 5, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 779 ⟨![[0], [], [2, 1], [1, 4], [3], [0], [], [2, 1], [1], [0, 0, 3]], ![[0], [8], [2, 8], [4], [3, 8], [0, 4, 0, 4], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9]]⟩, .edge 794 ⟨![[], [0, 0, 0, 1], [0, 0, 2, 0], [0, 0, 0, 4], [3], [0, 0], [0, 1], [2, 0], [0], [3, 6]], ![[8], [1, 8], [2, 8], [4], [3, 8], [4, 5, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 766 ⟨![[0], [1], [2], [3], [], [0, 6], [0, 0, 1], [2], [3, 6], []], ![[0], [1], [2], [3], [3, 3], [0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 781 ⟨![[], [1], [2], [3], [0, 5], [5, 6], [1], [2], [3, 4], [0]], ![[9], [1], [2], [3], [3, 3], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩, .edge 774 ⟨![[0], [], [2], [3], [0, 0, 1], [0], [], [2], [3, 4], [1]], ![[0], [9], [2], [3], [3, 3], [0, 4, 0, 9], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 789 ⟨![[], [0, 1], [2], [3], [0, 5], [1, 1], [1, 0, 6], [2], [3, 4], [0]], ![[9], [1, 9], [2], [3], [3, 3], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩, .edge 770 ⟨![[0], [1], [], [3], [2], [0], [1], [], [3, 5], [2]], ![[0], [1], [4], [3], [3, 3], [0, 4, 0, 4], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8]]⟩, .edge 785 ⟨![[], [1], [2, 0, 5], [3], [0, 5], [5, 6], [1], [0, 2], [3, 4], [0]], ![[9], [1], [2, 9], [3], [3, 3], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩, .edge 778 ⟨![[0], [], [1, 2], [3], [0, 0, 1], [0], [], [1, 2], [3, 4], [1]], ![[0], [9], [2, 9], [3], [3, 3], [0, 4, 0, 9], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 793 ⟨![[], [0, 1], [2, 0, 5], [3], [0, 5], [1, 1], [1, 0, 6], [0, 2], [3, 4], [0]], ![[9], [1, 9], [2, 9], [3], [3, 3], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩, .edge 768 ⟨![[0], [1], [2], [], [3, 3, 3], [0, 4], [1, 4], [2, 5], [4], [3]], ![[0], [1], [2], [9], [8], [2, 7], [4, 4, 8], [4, 4, 8], [4, 4, 8], [4, 4, 8]]⟩, .edge 783 ⟨![[], [1], [2], [3, 0, 5], [0, 5], [5, 6], [1], [2], [0, 3, 6], [0]], ![[9], [1], [2], [3, 9], [3, 8], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩, .edge 776 ⟨![[0], [], [2], [0, 0, 3, 1], [0, 0, 1], [0], [], [2], [1, 3, 6], [1]], ![[0], [9], [2], [3, 9], [3, 8], [0, 4, 0, 9], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 791 ⟨![[], [0, 1], [2], [3, 0, 5], [0, 5], [1, 1], [1, 0, 6], [2], [0, 3, 6], [0]], ![[9], [1, 9], [2], [3, 9], [3, 8], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩, .edge 772 ⟨![[0], [1], [], [3, 2], [2], [0], [1], [], [2, 3, 6], [2]], ![[0], [1], [4], [3, 4], [3, 8], [0, 4, 0, 4], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 787 ⟨![[], [1], [2, 0, 5], [3, 0, 5], [0, 5], [5, 6], [1], [0, 2], [0, 3, 6], [0]], ![[9], [1], [2, 9], [3, 9], [3, 8], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩, .edge 780 ⟨![[0], [], [1, 2], [0, 0, 3, 1], [0, 0, 1], [0], [], [1, 2], [1, 3, 6], [1]], ![[0], [9], [2, 9], [3, 9], [3, 8], [0, 4, 0, 9], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 795 ⟨![[], [0, 1], [2, 0, 5], [3, 0, 5], [0, 5], [1, 1], [1, 0, 6], [0, 2], [0, 3, 6], [0]], ![[9], [1, 9], [2, 9], [3, 9], [3, 8], [4, 4], [4, 4, 5], [4, 4, 5], [4, 4, 5], [4, 4, 5]]⟩] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 5 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 71) : Classified H :=
  classify_of_checks 71 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node71

namespace Node72

def gen : Fin 5 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [3], [4]],
   ![[0], [1], [2], [3], [4], [3, 3], [0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 71) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 72 :=
  generated_of_packed 71 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .core, .edge 803 ⟨![[0], [], [1], [2], [3], [0], [], [1], [2], [0, 0, 3]], ![[0], [2], [3], [4], [3, 3], [0, 3, 0, 3], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9]]⟩, .edge 818 ⟨![[], [0, 0, 0], [1], [2], [3], [0, 0], [0], [1], [2, 4, 6], [3, 6]], ![[6], [2], [3], [4], [3, 3], [3, 5, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 799 ⟨![[0], [1], [], [2], [3], [0], [1], [], [0, 0, 2], [3]], ![[0], [1], [3], [4], [3, 3], [0, 3, 0, 3], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8]]⟩, .edge 814 ⟨![[], [1], [0, 0, 0], [2], [3], [0, 0], [1], [0], [0, 2, 0], [3, 6]], ![[7], [1], [3], [4], [3, 3], [3, 5, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 807 ⟨![[0], [], [1], [2], [3], [0], [], [1], [2], [0, 0, 3]], ![[0], [2], [3], [4], [3, 3], [0, 3, 0, 3], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9]]⟩, .edge 822 ⟨![[], [0, 0, 0, 1], [0, 0, 0], [2], [3], [0, 0], [0, 1], [0], [0, 2, 0], [3, 6]], ![[7], [1, 7], [3], [4], [3, 3], [3, 5, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 797 ⟨![[0], [1], [2], [], [3], [0, 4, 6], [1], [0, 0, 2], [4], [3, 6]], ![[0], [1], [2], [4], [8], [0, 5, 8], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 812 ⟨![[], [1], [2], [0, 4, 5], [3], [5, 6], [1], [2], [0], [3, 6]], ![[8], [1], [2], [4], [3, 8], [3, 3], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 805 ⟨![[0], [], [2], [1], [3], [0], [], [2], [1], [0, 0, 3]], ![[0], [3], [2], [4], [3, 3], [0, 3, 0, 3], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9]]⟩, .edge 820 ⟨![[], [1, 0, 5], [2], [0, 4, 5], [3], [5, 6], [0, 1, 4], [2], [0], [3, 6]], ![[8], [1, 8], [2], [4], [3, 8], [3, 3], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 801 ⟨![[0], [1], [], [0, 0, 2], [3], [0], [1], [], [2], [3]], ![[0], [1], [8], [4], [3, 8], [0, 3, 0, 8], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 816 ⟨![[], [1], [0, 2, 4], [0, 4, 5], [3], [5, 6], [1], [2, 0, 6], [0], [3, 6]], ![[8], [1], [2, 8], [4], [3, 8], [3, 3], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 809 ⟨![[0], [], [2, 1, 4], [1], [3], [0], [], [2, 1, 4], [1], [0, 0, 3]], ![[0], [3], [2, 3], [4], [3, 3], [0, 3, 0, 3], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9]]⟩, .edge 824 ⟨![[], [1, 0, 5], [0, 2, 4], [0, 4, 5], [3], [5, 6], [0, 1, 4], [2, 0, 6], [0], [3, 6]], ![[8], [1, 8], [2, 8], [4], [3, 8], [3, 3], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 796 ⟨![[0], [1], [2], [3], [], [0, 6], [0, 0, 1], [2], [3, 6], []], ![[0], [1], [2], [3], [3, 3], [0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 811 ⟨![[], [1], [2], [3], [0, 5], [5, 6], [1], [2], [3, 4, 6], [0]], ![[9], [1], [2], [3], [3, 3], [4, 4], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 804 ⟨![[0], [], [2], [3], [0, 0, 1], [0], [], [2], [3], [1]], ![[0], [9], [2], [3], [3, 3], [0, 3, 0, 3], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 819 ⟨![[], [0, 1], [2], [3], [0, 5], [1, 1], [1, 0, 6], [2], [3, 4, 6], [0]], ![[9], [1, 9], [2], [3], [3, 3], [4, 4], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 800 ⟨![[0], [1], [], [3], [2], [0], [1], [], [0, 0, 3], [2]], ![[0], [1], [4], [3], [3, 3], [0, 3, 0, 3], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8]]⟩, .edge 815 ⟨![[], [1], [2, 0, 5], [3], [0, 5], [5, 6], [1], [0, 2], [3, 4, 6], [0]], ![[9], [1], [2, 9], [3], [3, 3], [4, 4], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 808 ⟨![[0], [], [1, 2], [3], [0, 0, 1], [0], [], [1, 2], [3], [1]], ![[0], [9], [2, 9], [3], [3, 3], [0, 3, 0, 3], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 823 ⟨![[], [0, 1], [2, 0, 5], [3], [0, 5], [1, 1], [1, 0, 6], [0, 2], [3, 4, 6], [0]], ![[9], [1, 9], [2, 9], [3], [3, 3], [4, 4], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 798 ⟨![[0], [1], [2], [], [3, 3, 3], [0, 3, 3], [1], [0, 0, 2], [4], [3]], ![[0], [1], [2], [9], [8], [0, 5, 8], [4, 4, 8], [4, 4, 8], [4, 4, 8], [4, 4, 8]]⟩, .edge 813 ⟨![[], [1], [2], [3, 0, 5], [0, 5], [5, 6], [1], [2], [0, 3, 6], [0]], ![[9], [1], [2], [3, 9], [3, 8], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 806 ⟨![[0], [], [2], [1, 3, 6], [0, 0, 1], [0], [], [2], [1, 3, 6], [1]], ![[0], [9], [2], [3, 9], [3, 3], [0, 3, 0, 3], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 821 ⟨![[], [0, 1], [2], [3, 0, 5], [0, 5], [1, 1], [1, 0, 6], [2], [0, 3, 6], [0]], ![[9], [1, 9], [2], [3, 9], [3, 8], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 802 ⟨![[0], [1], [], [3, 2], [2], [0], [1], [], [2, 3, 6], [2]], ![[0], [1], [4], [3, 4], [3, 8], [0, 3, 0, 8], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 817 ⟨![[], [1], [2, 0, 5], [3, 0, 5], [0, 5], [5, 6], [1], [0, 2], [0, 3, 6], [0]], ![[9], [1], [2, 9], [3, 9], [3, 8], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 810 ⟨![[0], [], [1, 2], [1, 3, 6], [0, 0, 1], [0], [], [1, 2], [1, 3, 6], [1]], ![[0], [9], [2, 9], [3, 9], [3, 3], [0, 3, 0, 3], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 825 ⟨![[], [0, 1], [2, 0, 5], [3, 0, 5], [0, 5], [1, 1], [1, 0, 6], [0, 2], [0, 3, 6], [0]], ![[9], [1, 9], [2, 9], [3, 9], [3, 8], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 5 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 72) : Classified H :=
  classify_of_checks 72 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node72

namespace Node73

def gen : Fin 5 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [3], [4]],
   ![[0], [1], [2], [3], [4], [1, 3, 1, 3], [0, 3, 0, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 72) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 73 :=
  generated_of_packed 72 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .core, .edge 833 ⟨![[0], [], [1], [2], [3], [0], [], [1], [2, 4], [0, 0, 3]], ![[0], [2], [3], [4], [3, 8], [0, 3, 0, 3], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9]]⟩, .edge 848 ⟨![[], [0, 0, 0], [1], [2], [3], [0, 0], [0], [1], [2, 6], [3, 6]], ![[6], [2], [3], [4], [1, 3, 6, 8], [3, 5, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 829 ⟨![[0], [1], [], [2], [3], [0], [1], [], [2, 6], [3]], ![[0], [1], [3], [4], [1, 3, 1, 3], [0, 0, 3, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 844 ⟨![[], [1], [0, 0, 0], [2], [3], [0, 0], [1], [0], [2, 6], [3, 6]], ![[7], [1], [3], [4], [1, 3, 1, 3], [3, 5, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 837 ⟨![[0], [], [1], [2], [3], [0], [], [1], [2, 4], [0, 0, 3]], ![[0], [2], [3], [4], [3, 8], [0, 3, 0, 3], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9]]⟩, .edge 852 ⟨![[], [0, 0, 0, 1], [0, 0, 0], [2], [3], [0, 0], [0, 1], [0], [2, 6], [3, 6]], ![[7], [1, 7], [3], [4], [1, 3, 6, 8], [3, 5, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 827 ⟨![[0], [1], [2], [], [3], [0, 6], [1, 4], [2, 6], [], [3]], ![[0], [1], [2], [4], [1, 6], [0, 5], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 842 ⟨![[], [1], [2], [0, 5], [3], [5, 6], [1], [2], [0], [3, 6]], ![[8], [1], [2], [4], [1, 3, 1, 8], [3, 3], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 835 ⟨![[0], [], [2], [1, 4], [3], [0], [], [2], [1], [0, 0, 3]], ![[0], [8], [2], [4], [3, 3], [0, 3, 0, 8], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9]]⟩, .edge 850 ⟨![[], [1, 0, 5], [2], [0, 5], [3], [5, 6], [0, 1, 4], [2], [0], [3, 6]], ![[8], [1, 8], [2], [4], [1, 3, 1, 3], [3, 3], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 831 ⟨![[0], [1], [], [2, 6], [3], [0], [1], [], [2], [3]], ![[0], [1], [8], [4], [1, 3, 1, 8], [0, 0, 3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 846 ⟨![[], [1], [0, 2, 5], [0, 5], [3], [5, 6], [1], [0, 2, 6], [0], [3, 6]], ![[8], [1], [2, 8], [4], [1, 3, 1, 8], [3, 3], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 839 ⟨![[0], [], [1, 2, 6], [1, 4], [3], [0], [], [1, 2, 6], [1], [0, 0, 3]], ![[0], [8], [2, 8], [4], [3, 3], [0, 3, 0, 8], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9], [0, 4, 0, 9]]⟩, .edge 854 ⟨![[], [1, 0, 5], [0, 2, 5], [0, 5], [3], [5, 6], [0, 1, 4], [0, 2, 6], [0], [3, 6]], ![[8], [1, 8], [2, 8], [4], [1, 3, 1, 3], [3, 3], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 826 ⟨![[0], [1], [2], [3], [], [0, 6], [0, 0, 1], [2], [3], []], ![[0], [1], [2], [3], [1, 3, 1, 3], [0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 841 ⟨![[], [1], [2], [3], [0, 5], [5, 6], [1], [2], [3, 6], [0]], ![[9], [1], [2], [3], [1, 3, 1, 3], [4, 4], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 834 ⟨![[0], [], [2], [3], [0, 0, 1], [0], [], [2], [3, 4], [1]], ![[0], [9], [2], [3], [3, 8], [0, 3, 0, 3], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 849 ⟨![[], [0, 1], [2], [3], [0, 5], [1, 1], [1, 0, 6], [2], [3, 6], [0]], ![[9], [1, 9], [2], [3], [1, 3, 6, 8], [4, 4], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 830 ⟨![[0], [1], [], [3], [2], [0], [1], [], [3, 6], [2]], ![[0], [1], [4], [3], [1, 3, 1, 3], [0, 0, 3, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 845 ⟨![[], [1], [2, 0, 5], [3], [0, 5], [5, 6], [1], [0, 2], [3, 6], [0]], ![[9], [1], [2, 9], [3], [1, 3, 1, 3], [4, 4], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 838 ⟨![[0], [], [1, 2], [3], [0, 0, 1], [0], [], [1, 2], [3, 4], [1]], ![[0], [9], [2, 9], [3], [3, 8], [0, 3, 0, 3], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 853 ⟨![[], [0, 1], [2, 0, 5], [3], [0, 5], [1, 1], [1, 0, 6], [0, 2], [3, 6], [0]], ![[9], [1, 9], [2, 9], [3], [1, 3, 6, 8], [4, 4], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 828 ⟨![[0], [1], [2], [], [3], [0, 6], [1, 4], [2, 6], [], [3]], ![[0], [1], [2], [4], [1, 6], [0, 5], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 843 ⟨![[], [1], [2], [0, 3, 5], [0, 5], [5, 6], [1], [2], [0, 3], [0]], ![[9], [1], [2], [3, 9], [1, 3, 1, 8], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 836 ⟨![[0], [], [2], [1, 3, 4], [0, 0, 1], [0], [], [2], [1, 3], [1]], ![[0], [9], [2], [3, 9], [3, 3], [0, 3, 0, 8], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 851 ⟨![[], [0, 1], [2], [0, 3, 5], [0, 5], [1, 1], [1, 0, 6], [2], [0, 3], [0]], ![[9], [1, 9], [2], [3, 9], [1, 3, 1, 3], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 832 ⟨![[0], [1], [], [3, 2], [2], [0], [1], [], [2, 3], [2]], ![[0], [1], [4], [3, 4], [1, 3, 1, 8], [0, 0, 3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 847 ⟨![[], [1], [2, 0, 5], [0, 3, 5], [0, 5], [5, 6], [1], [0, 2], [0, 3], [0]], ![[9], [1], [2, 9], [3, 9], [1, 3, 1, 8], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 840 ⟨![[0], [], [1, 2], [1, 3, 4], [0, 0, 1], [0], [], [1, 2], [1, 3], [1]], ![[0], [9], [2, 9], [3, 9], [3, 3], [0, 3, 0, 8], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 855 ⟨![[], [0, 1], [2, 0, 5], [0, 3, 5], [0, 5], [1, 1], [1, 0, 6], [0, 2], [0, 3], [0]], ![[9], [1, 9], [2, 9], [3, 9], [1, 3, 1, 3], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 5 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 73) : Classified H :=
  classify_of_checks 73 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node73

namespace Node74

def gen : Fin 5 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [3], [4]],
   ![[0], [1], [2], [3], [4], [3, 3], [0, 4, 0, 4], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 73) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 74 :=
  generated_of_packed 73 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .core, .edge 863 ⟨![[0], [], [1], [2], [3], [0], [], [1], [2, 4], [0, 0, 3]], ![[0], [2], [3], [4], [3, 3], [0, 4, 0, 4], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 878 ⟨![[], [0, 0, 0], [1], [2], [3], [0, 0], [0], [1, 4, 6], [2, 4], [3, 6]], ![[6], [2], [3], [4], [3, 3], [2, 7], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 859 ⟨![[0], [1], [], [2], [3], [0, 4, 6], [1], [0, 0, 4], [2, 5], [3, 6]], ![[0], [1], [3], [4], [3, 3], [0, 0, 4, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 874 ⟨![[], [1], [0, 4, 5], [2], [3], [5, 6], [1], [0], [2, 4], [3, 6]], ![[7], [1], [3], [4], [3, 3], [2, 2, 5], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 867 ⟨![[0], [], [1], [2], [3], [0], [], [1], [2, 4], [0, 0, 3]], ![[0], [2], [3], [4], [3, 3], [0, 4, 0, 4], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 882 ⟨![[], [0, 1, 4], [0, 4, 5], [2], [3], [5, 6], [1, 0, 5], [0], [2, 4], [3, 6]], ![[7], [1, 7], [3], [4], [3, 3], [2, 2, 5], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 857 ⟨![[0], [1], [2], [], [3], [0, 4], [1, 4], [2, 5], [4], [3, 6]], ![[0], [1], [2], [4], [8], [0, 0, 4, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 872 ⟨![[], [1], [2], [0, 2, 2], [3], [0, 0], [1], [2, 4, 6], [0], [3, 6]], ![[8], [1], [2], [4], [3, 8], [2, 7], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 865 ⟨![[0], [], [2], [1, 4], [3], [0], [], [2], [1], [0, 0, 3]], ![[0], [8], [2], [4], [3, 8], [0, 4, 0, 4], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 880 ⟨![[], [0, 0, 0, 1], [2], [0, 2, 2], [3], [0, 0], [0, 1], [2, 4, 6], [0], [3, 6]], ![[8], [1, 8], [2], [4], [3, 8], [2, 7], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 861 ⟨![[0], [1], [], [2, 4, 6], [3], [0, 4, 6], [1], [0, 0, 4], [2], [3, 6]], ![[0], [1], [8], [4], [3, 8], [0, 0, 3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 876 ⟨![[], [1], [0, 2], [0, 0, 0, 4], [3], [0, 0], [1], [0, 2, 4, 5], [0], [3, 6]], ![[8], [1], [2, 8], [4], [3, 8], [2, 2, 5], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 869 ⟨![[0], [], [2, 1], [1, 4], [3], [0], [], [2, 1], [1], [0, 0, 3]], ![[0], [8], [2, 8], [4], [3, 8], [0, 4, 0, 4], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 884 ⟨![[], [0, 0, 0, 1], [0, 2], [0, 0, 0, 4], [3], [0, 0], [0, 1], [0, 1, 2, 1], [0], [3, 6]], ![[8], [1, 8], [2, 8], [4], [3, 8], [2, 2, 5], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 856 ⟨![[0], [1], [2], [3], [], [0, 6], [0, 0, 1], [2, 6], [3, 6], []], ![[0], [1], [2], [3], [3, 3], [0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 871 ⟨![[], [1], [2], [3], [0, 5], [5, 6], [1], [2, 4, 6], [3, 4], [0]], ![[9], [1], [2], [3], [3, 3], [2, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7]]⟩, .edge 864 ⟨![[0], [], [2], [3], [0, 0, 1], [0], [], [2], [3, 4], [1]], ![[0], [9], [2], [3], [3, 3], [0, 4, 0, 9], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 879 ⟨![[], [0, 1], [2], [3], [0, 5], [1, 1], [1, 0, 6], [2, 4, 6], [3, 4], [0]], ![[9], [1, 9], [2], [3], [3, 3], [2, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7]]⟩, .edge 860 ⟨![[0], [1], [], [3], [2, 2, 2], [0, 4, 6], [1], [0, 0, 4], [3, 5], [2]], ![[0], [1], [9], [3], [3, 3], [0, 3, 3, 5], [0, 5, 7], [0, 5, 7], [0, 5, 7], [0, 5, 7]]⟩, .edge 875 ⟨![[], [1], [2, 0, 5], [3], [0, 5], [5, 6], [1], [0, 2, 6], [3, 4], [0]], ![[9], [1], [2, 9], [3], [3, 3], [4, 4], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 868 ⟨![[0], [], [1, 2, 6], [3], [0, 0, 1], [0], [], [1, 2, 6], [3, 4], [1]], ![[0], [9], [2, 9], [3], [3, 3], [0, 4, 0, 9], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 883 ⟨![[], [0, 1], [2, 0, 5], [3], [0, 5], [1, 1], [1, 0, 6], [0, 2, 6], [3, 4], [0]], ![[9], [1, 9], [2, 9], [3], [3, 3], [4, 4], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 858 ⟨![[0], [1], [2], [], [3, 3, 3], [0, 4], [1, 4], [2, 5], [4], [3]], ![[0], [1], [2], [9], [8], [0, 2, 7, 5], [2, 7, 8], [2, 7, 8], [2, 7, 8], [2, 7, 8]]⟩, .edge 873 ⟨![[], [1], [2], [3, 0, 5], [0, 5], [5, 6], [1], [2, 3, 3], [0, 3, 6], [0]], ![[9], [1], [2], [3, 9], [3, 8], [2, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7]]⟩, .edge 866 ⟨![[0], [], [2], [0, 0, 3, 1], [0, 0, 1], [0], [], [2], [1, 3, 6], [1]], ![[0], [9], [2], [3, 9], [3, 8], [0, 4, 0, 9], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 881 ⟨![[], [0, 1], [2], [3, 0, 5], [0, 5], [1, 1], [1, 0, 6], [2, 3, 3], [0, 3, 6], [0]], ![[9], [1, 9], [2], [3, 9], [3, 8], [2, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7]]⟩, .edge 862 ⟨![[0], [1], [], [2, 3, 4], [2, 2, 2], [0, 3, 3], [1], [0, 0, 4], [2, 3, 6], [2]], ![[0], [1], [9], [3, 9], [3, 8], [0, 0, 3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 877 ⟨![[], [1], [2, 0, 5], [3, 0, 5], [0, 5], [5, 6], [1], [0, 2, 6], [0, 3, 6], [0]], ![[9], [1], [2, 9], [3, 9], [3, 8], [4, 4], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 870 ⟨![[0], [], [1, 2, 6], [0, 0, 3, 1], [0, 0, 1], [0], [], [1, 2, 6], [1, 3, 6], [1]], ![[0], [9], [2, 9], [3, 9], [3, 8], [0, 4, 0, 9], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 885 ⟨![[], [0, 1], [2, 0, 5], [3, 0, 5], [0, 5], [1, 1], [1, 0, 6], [0, 2, 6], [0, 3, 6], [0]], ![[9], [1, 9], [2, 9], [3, 9], [3, 8], [4, 4], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 5 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 74) : Classified H :=
  classify_of_checks 74 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node74

end ReeTwo.SylowModel.SmallEvenMaximalLower
