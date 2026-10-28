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

namespace Node0

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 11 :=
  ⟨![[1, 0], [0, 1, 4], [0], [1, 2, 4, 1, 8]],
   ![[2], [0, 2], [0, 0, 0, 1, 1, 1, 3], [0, 3, 1, 3, 1, 1], [0, 1], [3, 3, 2, 3, 2, 3], [0, 1, 0, 1, 3, 3], [0, 0, 1, 1, 3, 3], [0, 0, 0, 1, 1, 0, 1, 1], [0, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen parityGenerators := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 0 :=
  (generation_checked.sound generationWords gen parityGenerators).trans parityGenerators_generate

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 6 ⟨![[], [0], [1], [2], [3], [3, 0, 4], [3, 1], [2, 2, 5, 2]], ![[1], [2], [3], [4], [7, 2, 6, 7], [1, 3, 5, 3, 4], [6, 3, 6, 7], [1, 4, 5], [1, 5, 4], [1, 1, 5, 5]]⟩, .core, .edge 10 ⟨![[], [0, 4], [1], [2], [3], [0], [3, 1], [2, 2, 5, 2]], ![[5], [2], [3], [4], [5, 1, 5, 5], [1, 7, 3, 1], [6, 3, 6, 7], [1, 1, 4, 4], [1, 1], [1, 1, 5, 5]]⟩, .edge 1 ⟨![[0], [1], [], [2], [0, 3, 3, 3], [3, 1], [], [2, 5, 9]], ![[0], [1], [3], [0, 0], [0, 1, 1, 1, 0, 1], [3, 7, 3, 3], [3, 3, 5, 1], [1, 0, 5, 4], [1, 0, 1, 0], [3, 7, 3, 7]]⟩, .edge 8 ⟨![[], [1], [0], [2], [3], [3, 1, 4], [0], [2, 2, 5, 2]], ![[2], [1], [3], [4], [1, 1, 1, 4, 5], [1, 3, 5, 3, 4], [1, 1, 4, 3, 3], [1, 4, 5], [1, 5, 4], [1, 1, 5, 5]]⟩, .edge 4 ⟨![[0], [], [1, 1, 1], [2], [0, 1, 7, 1], [4, 7], [1], [2, 5, 3, 4]], ![[0], [6], [3], [0, 0], [0, 5, 4, 5], [2, 3, 7, 6], [2, 7, 6, 7], [0, 5, 4], [4, 5, 0], [2, 3, 6, 3]]⟩, .edge 12 ⟨![[], [1, 0], [0], [2], [3], [0, 1, 3], [0], [2, 2, 5, 2]], ![[2], [1, 2], [3], [4], [5, 1, 5, 5], [1, 7, 3, 1], [1, 3, 5, 3, 4], [1, 1, 4, 4], [1, 1], [1, 1, 5, 5]]⟩, .edge 0 ⟨![[0], [1], [2], [], [4, 0, 5, 3], [4, 5, 1, 3], [2, 4, 5, 4], [0, 6, 4, 0]], ![[0], [1], [2], [0, 0], [7, 4, 4], [1, 1, 0, 4], [0, 0, 1, 1, 7], [4, 0, 4, 0], [0, 1, 4, 5], [0, 2, 7, 0, 2, 7]]⟩, .edge 7 ⟨![[], [1], [2], [0, 4, 5, 8], [3], [3, 1, 4], [3, 2], [0]], ![[7], [1], [2], [4], [7, 2, 6, 3], [1, 3, 3, 5], [6, 3, 6, 3], [1, 4, 5], [1, 5, 4], [1, 1, 5, 5]]⟩, .edge 3 ⟨![[0], [], [2], [0, 1, 8, 0], [3, 4, 0, 9], [4, 7], [2, 3], [1]], ![[0], [7], [2], [0, 0], [0, 5, 4, 5], [7, 7, 0, 4], [0, 0, 5, 3, 7], [0, 5, 4], [4, 5, 0], [2, 3, 6, 3, 5]]⟩, .edge 11 ⟨![[], [0, 0, 1, 0], [2], [0, 4, 5, 8], [3], [0, 1, 5], [3, 2], [0]], ![[7], [1, 7], [2], [4], [5, 1, 5, 5], [3, 5, 4, 5, 3], [6, 3, 6, 3], [1, 1, 4, 4], [1, 1], [1, 1, 5, 5]]⟩, .edge 2 ⟨![[0], [1], [], [2, 5, 9], [0, 3, 3, 3], [3, 1], [], [2]], ![[0], [1], [7], [0, 0], [0, 1, 1, 1, 0, 1], [3, 3, 3, 7], [3, 7, 5, 1], [1, 0, 5, 4], [1, 0, 1, 0], [3, 3, 3, 3]]⟩, .edge 9 ⟨![[], [1], [0, 2, 2, 2, 9], [0, 4, 5, 8], [3], [3, 1, 4], [0, 2, 2, 2, 9], [0]], ![[7], [1], [2, 7], [4], [1, 1, 1, 4, 5], [1, 3, 3, 5], [1, 1, 4, 3, 7], [1, 4, 5], [1, 5, 4], [1, 1, 5, 5]]⟩, .edge 5 ⟨![[0], [], [1, 6, 2, 5], [0, 1, 8, 0], [2, 0, 4, 2], [4, 7], [2, 5, 3, 1], [1]], ![[0], [7], [2, 7], [0, 0], [0, 5, 4, 5], [7, 6, 7, 2], [0, 0, 5, 3, 7], [0, 5, 4], [4, 5, 0], [0, 2, 2, 0, 5]]⟩, .edge 13 ⟨![[], [0, 0, 1, 0], [0, 2, 2, 2, 9], [0, 4, 5, 8], [3], [0, 1, 5], [0, 2, 2, 2, 9], [0]], ![[7], [1, 7], [2, 7], [4], [5, 1, 5, 5], [3, 5, 4, 5, 3], [1, 5, 4, 3, 7], [1, 1, 4, 4], [1, 1], [1, 1, 5, 5]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 0) : Classified H :=
  classify_of_checks 0 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node0

namespace Node1

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [5]],
   ![[0], [1], [2], [0, 0], [0, 1, 1, 1, 0, 1], [3], [0, 3, 0, 0, 0, 3], [0, 0, 3, 0, 0, 3], [1, 0, 1, 0], [0, 0, 1, 0, 1, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 0) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 1 :=
  generated_of_packed 0 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 20 ⟨![[], [0], [1], [2], [3], [0, 3, 4], [3, 1], [1, 2, 5, 1]], ![[1], [2], [3], [4], [1, 7, 1, 3], [2, 3, 7, 2], [4, 4], [1, 5, 4], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .core, .edge 24 ⟨![[], [0, 4, 6], [1], [2], [3], [0], [3, 1], [0, 0, 2, 5]], ![[5], [2], [3], [4], [1, 1, 1, 5], [2, 3, 7, 2], [4, 4], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 15 ⟨![[0], [1], [], [2], [0, 3, 6], [3, 1], [], [2]], ![[0], [1], [3], [0, 0], [0, 1, 1, 5, 4, 1], [3, 4, 3, 0], [0, 0, 0, 0], [1, 0, 1, 0], [0, 1, 1, 0, 1, 5], [0, 1, 1, 0, 1, 5]]⟩, .edge 22 ⟨![[], [1], [0], [2], [3], [1, 3, 4], [0], [0, 2, 0]], ![[2], [1], [3], [4], [1, 7, 1, 3], [1, 3, 5, 3, 4], [4, 4], [1, 5, 4], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 18 ⟨![[0], [], [1, 1, 1], [2], [0, 3, 4, 8], [4, 7], [1], [2, 5]], ![[0], [6], [3], [0, 0], [7, 5, 7], [3, 7], [5, 5], [4, 5, 0], [2, 3, 6, 7], [2, 3, 6, 7]]⟩, .edge 26 ⟨![[], [1, 0], [0], [2], [3], [0, 1, 3], [0], [0, 2, 0]], ![[2], [1, 2], [3], [4], [1, 1, 1, 5], [3, 5, 5, 7], [4, 4], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 14 ⟨![[0], [1], [2], [], [0, 5], [5, 1], [2], []], ![[0], [1], [2], [0, 0], [0, 0, 0, 5, 1, 4], [0, 5, 0, 1], [0, 0, 0, 0], [0, 5, 0, 5], [0, 5, 2, 0, 5, 2], [0, 5, 2, 0, 5, 2]]⟩, .edge 21 ⟨![[], [1], [2], [0, 5, 3, 6], [3], [1, 3, 4], [3, 2], [0]], ![[7], [1], [2], [4], [7, 5, 5, 3], [3, 3, 4], [4, 4], [1, 5, 4], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 17 ⟨![[0], [], [2], [0, 1, 0, 7], [0, 3, 4, 8], [4, 7], [2, 3], [1]], ![[0], [7], [2], [0, 0], [7, 5, 3], [3, 5, 3], [5, 5], [4, 5, 0], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 25 ⟨![[], [3, 1, 0, 5], [2], [0, 5, 3, 6], [3], [0, 5, 1], [3, 2], [0]], ![[7], [1, 7], [2], [4], [1, 1, 1, 5], [3, 3, 4], [4, 4], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 16 ⟨![[0], [1], [], [2], [0, 3, 6], [3, 1], [], [2]], ![[0], [1], [3], [0, 0], [0, 1, 1, 5, 4, 1], [3, 0, 3, 0], [0, 0, 0, 0], [1, 0, 1, 0], [0, 1, 1, 0, 1, 5], [0, 1, 1, 0, 1, 5]]⟩, .edge 23 ⟨![[], [1], [0, 2], [2, 0, 2], [3], [1, 3, 4], [0, 2], [0]], ![[7], [1], [2, 7], [4], [7, 5, 5, 3], [3, 3, 4], [4, 4], [1, 5, 4], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 19 ⟨![[0], [], [1, 3, 2, 4], [0, 1, 0, 7], [0, 3, 4, 8], [4, 7], [1, 2], [1]], ![[0], [7], [2, 7], [0, 0], [7, 5, 3], [3, 5, 3], [5, 5], [4, 5, 0], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 27 ⟨![[], [1, 2, 0, 2], [0, 2], [2, 0, 2], [3], [0, 5, 1], [0, 2], [0]], ![[7], [1, 7], [2, 7], [4], [1, 1, 1, 5], [3, 3, 4], [4, 4], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 1) : Classified H :=
  classify_of_checks 1 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node1

namespace Node2

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [0, 1, 1, 1, 0, 1], [1, 1, 0, 2, 0, 2, 2, 2], [0, 0, 1, 1, 2, 2], [0, 0, 0, 0, 1, 0, 1, 0], [1, 0, 1, 0], [0, 0, 1, 0, 1, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 1) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 2 :=
  generated_of_packed 1 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 30 ⟨![[], [0], [1], [2], [2, 0, 3], [1, 1, 4, 1]], ![[1], [2], [3], [1, 1, 1, 3, 4], [1, 2, 4, 2, 3], [1, 1, 3, 2, 2], [1, 3, 4], [1, 4, 3], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 32 ⟨![[], [0, 3], [1], [2], [0], [1, 1, 4, 1]], ![[4], [2], [3], [4, 1, 4, 4], [1, 5, 2, 1], [1, 2, 4, 2, 3], [1, 1, 3, 3], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 28 ⟨![[0], [1], [], [3, 0, 4, 2], [3, 4, 1, 2], [0, 5, 3, 0]], ![[0], [1], [0, 0], [5, 3, 3], [1, 1, 0, 3], [0, 0, 1, 1, 5], [3, 0, 3, 0], [0, 1, 3, 4], [1, 4, 1, 5, 4, 5], [1, 4, 1, 5, 4, 5]]⟩, .edge 31 ⟨![[], [1], [0, 3, 4, 7], [2], [2, 1, 3], [0]], ![[5], [1], [3], [1, 1, 1, 3, 4], [1, 2, 2, 4], [1, 1, 3, 2, 5], [1, 3, 4], [1, 4, 3], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 29 ⟨![[0], [], [0, 1, 7, 0], [2, 3, 0, 8], [3, 6], [1]], ![[0], [5], [0, 0], [0, 4, 3, 4], [5, 5, 0, 3], [0, 0, 4, 2, 5], [0, 4, 3], [3, 4, 0], [0, 0, 2, 3, 0, 5], [0, 0, 2, 3, 0, 5]]⟩, .edge 33 ⟨![[], [0, 0, 1, 0], [0, 3, 4, 7], [2], [0, 1, 4], [0]], ![[5], [1, 5], [3], [4, 1, 4, 4], [2, 4, 3, 4, 2], [1, 4, 3, 2, 5], [1, 1, 3, 3], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 2) : Classified H :=
  classify_of_checks 2 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node2

namespace Node3

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [0, 1, 1, 1, 0, 1], [0, 2, 2, 1, 1, 0], [0, 0, 1, 2, 0, 1, 0, 2], [0, 0, 0, 0, 1, 0, 1, 0], [1, 0, 1, 0], [2, 2, 2, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 2) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 3 :=
  generated_of_packed 2 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 36 ⟨![[], [0], [1], [2], [2, 0, 3], [1, 3, 4, 7]], ![[1], [2], [3], [1, 1, 1, 3, 4], [1, 3, 1, 5, 5], [3, 2, 5], [1, 3, 4], [1, 4, 3], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 38 ⟨![[], [0, 3], [1], [2], [0], [1, 3, 4, 7]], ![[4], [2], [3], [4, 1, 4, 4], [1, 3, 4, 5, 5], [3, 2, 5], [1, 1, 3, 3], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 34 ⟨![[0], [1], [], [0, 3, 4, 7], [1, 3, 4, 5], [1, 4, 1, 2]], ![[0], [1], [0, 0], [1, 0, 5, 0, 4], [0, 3, 1, 4, 5], [0, 0, 3, 3], [0, 4, 3, 1], [0, 1, 3, 4], [5, 5], [5, 5]]⟩, .edge 37 ⟨![[], [1], [1, 0, 6, 1], [2], [2, 1, 3], [0]], ![[5], [1], [3], [1, 1, 1, 3, 4], [2, 1, 2, 4], [3, 2, 3, 2], [1, 3, 4], [1, 4, 3], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 35 ⟨![[0], [], [7, 1, 4], [0, 1, 1, 6], [3, 6], [1]], ![[0], [5], [0, 0], [0, 4, 3, 4], [0, 2, 5, 4, 0], [2, 2, 5, 5], [0, 4, 3], [3, 4, 0], [2, 5, 2, 5], [2, 5, 2, 5]]⟩, .edge 39 ⟨![[], [0, 0, 1, 0], [1, 1, 4, 0], [2], [1, 3, 0], [0]], ![[5], [1, 5], [3], [4, 1, 4, 4], [2, 1, 5, 1], [3, 2, 3, 2], [1, 1, 3, 3], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 3) : Classified H :=
  classify_of_checks 3 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node3

namespace Node4

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [0, 1, 0, 0, 1, 1, 1, 1, 0, 1], [0, 1, 0, 1, 0, 1, 1, 0], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 0, 1, 1, 1, 1, 0], [0, 0, 1, 1, 0, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 3) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 4 :=
  generated_of_packed 3 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 42 ⟨![[], [0], [1], [2], [4, 0, 6], [2, 1]], ![[1], [2], [3], [1, 1, 1, 1, 3, 3, 4, 1], [1, 4, 4, 4], [1, 4, 3, 3, 4, 1], [4, 4, 4, 4], [1, 1, 1, 3, 3, 1], [1, 1, 3, 1, 1, 3], [1, 1, 3, 1, 1, 3]]⟩, .core, .edge 44 ⟨![[], [0, 2, 4, 6], [1], [2], [0], [2, 1]], ![[4], [2], [3], [1, 1, 3, 4, 1, 4, 1], [1, 3, 1, 4, 1], [1, 1, 1, 5, 4, 2], [4, 1, 4, 1], [1, 3, 3, 4, 1, 4], [1, 1, 1, 2, 4, 5], [1, 1, 1, 2, 4, 5]]⟩, .edge 40 ⟨![[0], [1], [], [0, 2, 2, 2], [0, 1, 0, 8], []], ![[0], [1], [0, 0], [1, 1, 0, 1, 1, 4, 3, 4], [0, 1, 1, 0, 4, 1], [0, 4, 1, 4, 0, 4], [0, 1, 0, 1, 1, 4], [0, 0, 0, 1, 1, 1, 1, 0], [0, 1, 0, 1, 4, 1], [0, 1, 0, 1, 4, 1]]⟩, .edge 43 ⟨![[], [1], [0], [2], [4, 1, 6], [0]], ![[2], [1], [3], [1, 1, 1, 1, 3, 3, 4, 1], [1, 4, 4, 4], [1, 4, 3, 3, 4, 1], [4, 4, 4, 4], [1, 1, 1, 3, 3, 1], [1, 1, 3, 1, 1, 3], [1, 1, 3, 1, 1, 3]]⟩, .edge 41 ⟨![[0], [], [1, 1, 1], [0, 4, 5], [3, 4, 6], [1]], ![[0], [5], [0, 0], [0, 0, 0, 4, 3], [0, 0, 3, 0], [0, 0, 3, 3], [3, 0, 3, 0], [0, 0, 0, 4, 4, 0], [0, 2, 2, 3, 4], [0, 2, 2, 3, 4]]⟩, .edge 45 ⟨![[], [1, 0], [0], [2], [1, 0, 2, 4], [0]], ![[2], [1, 2], [3], [1, 1, 3, 4, 1, 4, 1], [1, 3, 1, 4, 1], [1, 1, 1, 2, 1, 2], [4, 1, 4, 1], [1, 3, 3, 4, 1, 4], [1, 1, 2, 1, 1, 2], [1, 1, 2, 1, 1, 2]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 4) : Classified H :=
  classify_of_checks 4 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node4

namespace Node5

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [0, 0, 0, 1, 1, 1, 0, 1], [0, 0, 0, 2, 0, 1, 2, 1], [0, 0, 0, 0, 1, 1, 2, 2], [0, 0, 0, 0, 1, 0, 1, 0], [1, 0, 1, 0], [1, 1, 1, 2, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 4) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 5 :=
  generated_of_packed 4 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 48 ⟨![[], [0], [1], [2], [0, 3], [1, 1, 4, 1]], ![[1], [2], [3], [1, 1, 1, 4], [3, 5, 2, 4, 1], [2, 4, 4, 2], [2, 5, 5, 2], [1, 3, 4], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2]]⟩, .core, .edge 50 ⟨![[], [2, 3, 0, 8], [1], [2], [0], [1, 1, 4, 1]], ![[4], [2], [3], [1, 1, 1, 3, 4], [1, 2, 5, 1], [2, 4, 1, 2], [1, 1], [1, 1, 3, 3], [1, 1, 1, 2, 1, 5], [1, 1, 1, 2, 1, 5]]⟩, .edge 46 ⟨![[0], [1], [], [3, 0, 4, 2], [0, 1, 4, 0, 4], [0, 5, 3, 0]], ![[0], [1], [0, 0], [5, 3, 3], [3, 3, 0, 5, 3], [0, 0, 1, 4, 0, 0], [3, 0, 3, 0], [1, 0, 1, 0], [1, 1, 1, 4, 5], [1, 1, 1, 4, 5]]⟩, .edge 49 ⟨![[], [1], [0, 3, 4, 7], [2], [1, 3], [0]], ![[5], [1], [3], [1, 1, 1, 4], [2, 4, 1, 2], [2, 1, 1, 5], [1, 3, 3, 3, 4], [1, 3, 4], [1, 1, 1, 2, 4, 5], [1, 1, 1, 2, 4, 5]]⟩, .edge 47 ⟨![[0], [], [1, 2, 5, 2], [0, 3, 8], [1, 1, 8], [1]], ![[0], [5], [0, 0], [5, 0, 0, 2], [0, 4, 5, 0, 2], [0, 2, 5, 3], [0, 4, 3], [3, 4, 0], [2, 2, 4], [2, 2, 4]]⟩, .edge 51 ⟨![[], [2, 3, 0, 1], [0, 3, 4, 7], [2], [0, 1, 8], [0]], ![[5], [1, 5], [3], [1, 1, 1, 3, 4], [1, 2, 3, 2, 1], [2, 1, 4, 5], [1, 1], [1, 1, 3, 3], [1, 1, 1, 2, 4, 2], [1, 1, 1, 2, 4, 2]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 5) : Classified H :=
  classify_of_checks 5 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node5

namespace Node6

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [0, 1, 1, 2, 2, 1, 0, 1], [0, 1, 0, 1, 0, 1, 1, 0], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 1, 0, 1, 1, 0, 1], [0, 1, 2, 2, 1, 0], [2, 2, 2, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 5) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 6 :=
  generated_of_packed 5 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 54 ⟨![[], [0], [1], [2], [4, 0, 6], [0, 3, 1, 0]], ![[1], [2], [3], [1, 3, 2, 5, 4], [1, 4, 4, 4], [3, 2, 5], [4, 4, 4, 4], [1, 3, 1, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2]]⟩, .core, .edge 56 ⟨![[], [0, 2, 4, 6], [1], [2], [0], [1, 3, 4, 7]], ![[4], [2], [3], [4, 3, 2, 1, 5], [1, 1, 5, 5], [3, 2, 5], [4, 1, 4, 1], [1, 2, 1, 2], [2, 2, 2, 2], [2, 2, 2, 2]]⟩, .edge 52 ⟨![[0], [1], [], [0, 3, 4, 7], [1, 2, 2, 3], [1, 2, 7, 1]], ![[0], [1], [0, 0], [1, 4, 1, 1], [0, 3, 1, 5, 4], [0, 0, 3, 3], [4, 4, 4, 4], [0, 0, 5, 4, 4], [5, 5], [5, 5]]⟩, .edge 55 ⟨![[], [1], [2, 4, 3, 0], [2], [4, 1, 6], [0]], ![[5], [1], [3], [5, 5, 1, 4], [1, 4, 4, 4], [3, 2, 3, 2], [4, 4, 4, 4], [2, 1, 2, 1], [2, 5, 2, 5], [2, 5, 2, 5]]⟩, .edge 53 ⟨![[0], [], [1, 4, 5, 7], [0, 4, 5], [3, 4, 6], [1]], ![[0], [5], [0, 0], [0, 5, 2, 3], [0, 0, 3, 0], [0, 0, 3, 3], [0, 2, 0, 2], [0, 4, 2, 2, 3], [2, 5, 2, 5], [2, 5, 2, 5]]⟩, .edge 57 ⟨![[], [0, 1, 5, 6], [1, 0, 1, 4], [2], [0, 4, 2, 1], [0]], ![[5], [1, 5], [3], [1, 3, 5, 5, 1], [1, 1, 5, 2], [3, 2, 3, 2], [4, 1, 4, 1], [1, 3, 4, 2, 5], [2, 5, 2, 5], [2, 5, 2, 5]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 6) : Classified H :=
  classify_of_checks 6 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node6

namespace Node7

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0, 0, 1, 0, 1], [2, 2, 0, 2, 2, 0], [2, 1, 2, 1, 2, 2], [1, 0, 1, 0, 2, 2], [2, 1, 2, 2, 1, 2], [0, 0, 2, 2, 0, 2, 2, 0], [1, 2, 1, 2, 1, 2, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 6) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 7 :=
  generated_of_packed 6 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 59 ⟨![[0], [], [1], [2, 0], [], [1, 4, 8]], ![[0], [2], [0, 0, 0, 3], [0, 0, 2, 5, 5, 2], [2, 5, 2, 2], [2, 2, 3, 0], [2, 5, 5, 2], [0, 2, 2, 2, 3, 5], [2, 5, 2, 5], [2, 5, 2, 5]]⟩, .edge 62 ⟨![[], [0, 0, 0], [1], [3, 6], [0], [1, 4, 2, 3]], ![[4], [2], [1, 1, 3], [1, 2, 3, 2, 1], [1, 2, 5, 4], [1, 5, 4, 5], [2, 2, 5, 5], [1, 2, 3, 2, 1, 3], [1, 2, 4, 2], [1, 2, 4, 2]]⟩, .edge 58 ⟨![[0], [1], [], [3, 4, 0, 2], [1, 3, 4, 3], [0, 0, 2, 5]], ![[0], [1], [3, 0, 1, 4], [5, 0, 5, 0], [4, 5, 1, 5], [1, 0, 1, 0, 5], [3, 0, 3, 0], [3, 1, 0, 4], [0, 3, 0, 5, 3, 5], [0, 3, 0, 5, 3, 5]]⟩, .edge 61 ⟨![[], [1], [1, 0, 1, 7], [3, 6], [1, 2], [0]], ![[5], [1], [1, 4], [5, 1, 4, 2], [2, 3, 4, 5, 4], [1, 2, 3, 4, 2], [2, 2, 5, 5], [1, 5, 3, 2, 4], [1, 2, 4, 2, 3], [1, 2, 4, 2, 3]]⟩, .edge 60 ⟨![[0], [], [1, 4, 8], [2, 0], [], [1]], ![[0], [5], [0, 0, 0, 3], [0, 0, 2, 2, 5, 5], [2, 2, 2, 5], [2, 5, 3, 0], [2, 2, 5, 5], [0, 2, 0, 5, 5, 5], [2, 2, 2, 2], [2, 2, 2, 2]]⟩, .edge 63 ⟨![[], [0, 5, 1, 4], [0, 3, 1, 1], [3, 6], [1, 4, 2, 0], [0]], ![[5], [1, 5], [1, 1, 3], [1, 2, 3, 5, 1], [5, 4, 5, 1], [1, 5, 1, 3, 2], [2, 2, 5, 5], [1, 2, 3, 5, 1, 3], [1, 2, 1, 3, 5], [1, 2, 1, 3, 5]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 7) : Classified H :=
  classify_of_checks 7 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node7

namespace Node8

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 1, 0, 1, 2, 1, 1, 2], [1, 0, 1, 0, 1, 1], [2, 0, 1, 0, 2, 1], [1, 0, 1, 1, 2, 0, 2, 1], [1, 0, 1, 0], [1, 0, 1, 0, 1, 1, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 7) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 8 :=
  generated_of_packed 7 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 66 ⟨![[], [0], [1], [], [0, 0, 0, 7], [0, 0, 1, 5, 2]], ![[1], [2], [1, 2, 2, 1, 5, 2], [1, 1, 1, 4], [2, 4, 2, 1], [1, 1, 4, 2, 5, 4], [1, 4], [1, 1, 1, 1, 1, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 68 ⟨![[], [3, 0, 8], [1], [], [0], [1, 1, 1, 5, 7]], ![[4], [2], [1, 1, 5, 1, 4, 5], [1, 1, 1, 4], [2, 4, 5, 4], [1, 1, 1, 2, 5, 1], [1, 1], [1, 1, 1, 4, 1, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 64 ⟨![[0], [1], [], [2, 0, 3, 8], [3, 4, 1, 2], [1, 1, 2, 5]], ![[0], [1], [4, 0, 5, 0, 4], [5, 1, 5, 1], [1, 0, 4, 3], [0, 5, 1, 3, 1], [1, 0, 1, 0], [0, 4, 0, 4], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 67 ⟨![[], [1], [4, 1, 0, 1], [], [1, 0, 3, 0], [0]], ![[5], [1], [1, 2, 1, 1, 5, 4], [1, 1, 1, 4], [2, 1, 5, 1], [1, 1, 4, 2, 2, 4], [1, 4], [1, 1, 1, 1, 1, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 65 ⟨![[0], [], [2, 7, 1, 4], [3, 0, 8], [3, 6], [1]], ![[0], [5], [2, 3, 0, 5], [3, 4, 0, 4], [5, 5, 3, 0], [3, 5, 0, 2], [3, 4, 0], [0, 4, 3], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 69 ⟨![[], [1, 0, 0, 0], [0, 0, 3, 0, 2], [], [0, 1, 4], [0]], ![[5], [1, 5], [1, 1, 5, 4, 1, 2], [1, 1, 1, 4], [2, 1, 2, 4], [1, 1, 1, 2, 2, 1], [1, 1], [1, 1, 1, 4, 1, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 8) : Classified H :=
  classify_of_checks 8 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node8

namespace Node9

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 0, 2, 0, 3, 2], [2, 1, 2, 1, 2, 2], [0, 2, 2, 2, 3, 0, 2, 3], [2, 1, 2, 2, 1, 2], [0, 2, 0, 2, 2, 2], [0, 0, 0, 2, 0, 2, 2, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 8) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 9 :=
  generated_of_packed 8 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 73 ⟨![[0], [], [1], [1, 2, 1], [0], [], [1, 4], [1, 2, 1, 2, 2]], ![[0], [2], [2, 7, 2, 3, 3], [2, 2], [2, 2, 2, 6], [2, 2, 2, 3, 2, 7], [0, 0, 3, 3], [0, 0], [2, 6, 2, 6], [2, 6, 2, 6]]⟩, .edge 80 ⟨![[], [0, 7], [1], [1, 2, 1], [7], [0], [1, 8], [0, 3, 0, 2, 5]], ![[5], [2], [2, 3, 6], [2, 2], [1, 2, 2, 2, 5, 6], [2, 2, 2, 3, 2, 7], [3, 3, 4], [4], [2, 2, 2, 6], [2, 2, 2, 6]]⟩, .edge 71 ⟨![[0], [1], [], [3, 2, 5], [0, 8], [1, 4, 6, 8], [3], [3, 2]], ![[0], [1], [6, 7], [6], [1, 6, 5, 6], [1, 3, 1, 7], [0, 0, 3, 3], [0, 0], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 78 ⟨![[], [1], [0, 7, 8], [3, 2, 5], [7], [1], [0], [0, 0, 5, 2, 6]], ![[6], [1], [2, 4, 7, 2], [2, 6], [1, 2, 2, 2, 1, 2], [2, 2, 2, 7, 2, 7], [3, 3, 4], [4], [2, 2, 2, 4, 6], [2, 2, 2, 4, 6]]⟩, .edge 75 ⟨![[0], [], [1, 4], [3, 2, 5], [0], [], [1], [1, 2, 1, 4]], ![[0], [6], [2, 3, 6, 3, 3], [2, 6], [2, 6, 2, 2], [2, 2, 3, 2, 3, 2], [0, 0, 3, 3], [0, 0], [2, 2, 2, 2], [2, 2, 2, 2]]⟩, .edge 82 ⟨![[], [1, 0, 0, 0], [0, 7, 8], [3, 2, 5], [7], [0, 3, 1, 4], [0], [1, 2, 1, 4]], ![[6], [1, 6], [2, 4, 7, 2], [2, 6], [1, 2, 2, 2, 1, 6], [2, 2, 2, 7, 2, 7], [3, 3, 4], [4], [2, 2, 2, 4, 6], [2, 2, 2, 4, 6]]⟩, .edge 70 ⟨![[0], [1], [2], [], [0, 6, 7], [1, 6, 7], [2, 5], [6, 7]], ![[0], [1], [2], [2, 2], [1, 2, 2, 2, 1, 2], [2, 2, 2, 6], [0, 4], [0, 0], [2, 2, 6, 6], [2, 2, 6, 6]]⟩, .edge 77 ⟨![[], [1], [2], [2, 0, 6, 2], [7], [1], [2, 8], [3, 0, 5]], ![[2, 7, 2], [1], [2], [2, 2], [1, 2, 2, 2, 1, 2], [2, 2, 2, 3, 4, 6, 3], [3, 4, 7], [4], [2, 2, 2, 6], [2, 2, 2, 6]]⟩, .edge 74 ⟨![[0], [], [2], [2, 1, 2, 4], [0], [], [2, 4], [1, 2, 5, 2]], ![[0], [2, 7, 6, 3, 7], [2], [2, 2], [2, 2, 2, 6], [2, 2, 2, 3, 6, 3], [0, 0, 3, 7], [0, 0], [2, 6, 2, 6], [2, 6, 2, 6]]⟩, .edge 81 ⟨![[], [0, 1, 6], [2], [2, 0, 6, 2], [7], [1, 0, 8], [2, 8], [3, 0, 5]], ![[2, 7, 2], [1, 2, 7, 2], [2], [2, 2], [1, 2, 2, 2, 5, 6], [2, 2, 2, 3, 4, 6, 3], [3, 4, 7], [4], [2, 2, 2, 6], [2, 2, 2, 6]]⟩, .edge 72 ⟨![[0], [1], [], [2], [0, 8], [1, 4, 6, 8], [3], [3, 2, 5]], ![[0], [1], [3], [6], [1, 6, 5, 6], [1, 3, 5, 6, 3], [0, 0, 3, 7], [0, 0], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 79 ⟨![[], [1], [0, 0, 2, 0], [0, 2, 2, 7], [7], [1], [2, 0], [3, 0, 5]], ![[2, 3, 4, 6], [1], [3, 2, 2, 2], [2, 6], [1, 2, 2, 2, 1, 2], [2, 2, 2, 3, 2, 7], [3, 4, 7], [4], [2, 2, 2, 4, 6], [2, 2, 2, 4, 6]]⟩, .edge 76 ⟨![[0], [], [2, 1, 1, 1], [1, 2, 2], [0], [], [2, 4, 1, 6], [2, 2, 1]], ![[0], [2, 3, 2, 3, 7], [3, 6, 2, 6], [2, 6], [2, 6, 2, 2], [2, 2, 3, 2, 3, 6], [0, 0, 3, 7], [0, 0], [2, 2, 2, 2], [2, 2, 2, 2]]⟩, .edge 83 ⟨![[], [0, 1, 6], [0, 0, 2, 0], [0, 2, 2, 7], [7], [1, 0, 8], [2, 0], [3, 0, 5]], ![[2, 3, 4, 6], [2, 7, 6, 1], [3, 2, 2, 2], [2, 6], [1, 2, 2, 2, 1, 6], [2, 2, 2, 3, 2, 7], [3, 4, 7], [4], [2, 2, 2, 4, 6], [2, 2, 2, 4, 6]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 9) : Classified H :=
  classify_of_checks 9 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node9

namespace Node10

def gen : Fin 5 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [3], [5]],
   ![[0], [1], [2], [3], [0, 1, 1, 1, 3, 0, 1], [4], [0, 2, 1, 0, 1, 2], [3, 4, 3, 4], [1, 0, 1, 0], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 9) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 10 :=
  generated_of_packed 9 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .edge 98 ⟨![[], [0], [1], [1, 2, 1], [3], [], [0, 4], [1, 4, 6], [2, 4], [0, 3, 4, 0]], ![[1], [2], [7, 3, 7], [4], [1, 1, 1, 6], [2, 3, 3, 7], [3, 3], [1, 6], [1, 1, 6, 6], [1, 1, 6, 6]]⟩, .core, .edge 106 ⟨![[], [0, 4], [1], [1, 2, 1], [3], [], [0], [1, 4, 6], [2, 4], [0, 0, 3, 5]], ![[6], [2], [7, 3, 7], [4], [1, 1, 1, 6], [2, 3, 3, 7], [3, 3], [1, 1], [1, 1, 6, 6], [1, 1, 6, 6]]⟩, .edge 87 ⟨![[0], [1], [], [2, 4, 6], [3], [0, 4, 6, 8], [1, 4, 5], [4, 5, 8], [2, 4, 5], [3, 6, 7]], ![[0], [1], [7, 8], [4], [3, 7, 8], [3, 8], [3, 3], [0, 6, 0, 6], [0, 7, 0, 7], [0, 7, 0, 7]]⟩, .edge 102 ⟨![[], [1], [0, 4, 6], [2, 4, 6], [3], [], [1, 4], [0], [2, 4], [1, 3, 4, 1]], ![[7], [1], [7, 8, 2], [4], [1, 1, 1, 6], [2, 3, 3, 2], [3, 3], [1, 6], [1, 1, 6, 6], [1, 1, 6, 6]]⟩, .edge 94 ⟨![[0], [], [1, 5, 7], [2, 4, 6], [3], [0, 4, 8], [4, 7], [1], [2, 4, 6], [3, 5]], ![[0], [7], [7, 3, 2], [4], [0, 6, 5, 6], [4, 9], [3, 3], [0, 6, 5], [2, 2, 6], [2, 2, 6]]⟩, .edge 110 ⟨![[], [0, 4, 1], [0, 4, 6], [2, 4, 6], [3], [], [0, 1, 8], [0], [2, 4], [3, 5, 7, 8]], ![[7], [1, 7], [7, 8, 2], [4], [1, 1, 1, 6], [2, 3, 3, 2], [3, 3], [1, 1], [1, 1, 6, 6], [1, 1, 6, 6]]⟩, .edge 85 ⟨![[0], [1], [2], [], [3], [0, 6], [1], [2, 5, 6], [6], [3, 7]], ![[0], [1], [2], [4], [2, 8, 7], [0, 9, 0, 4], [8], [4, 9], [2, 2, 7, 7], [2, 2, 7, 7]]⟩, .edge 100 ⟨![[], [1], [2], [0, 4], [3], [], [1, 4], [2, 4, 6], [0, 4, 6], [0, 3, 0, 7]], ![[2, 8, 7], [1], [2], [4], [1, 1, 1, 6], [2, 3, 8, 7], [3, 8], [1, 6], [1, 1, 6, 6], [1, 1, 6, 6]]⟩, .edge 92 ⟨![[0], [], [2], [1, 6, 7], [3], [0, 4, 8], [4, 7], [2, 4, 5], [0, 1, 0], [3, 5]], ![[0], [0, 8, 0], [2], [4], [0, 2, 7, 5], [4, 9], [3, 8], [0, 6, 5], [2, 7], [2, 7]]⟩, .edge 108 ⟨![[], [1, 0], [2], [0, 4], [3], [], [1, 0, 4], [2, 4, 6], [0, 4, 6], [0, 3, 0, 7]], ![[2, 8, 7], [6, 3], [2], [4], [1, 1, 1, 6], [2, 3, 8, 7], [3, 8], [1, 1], [1, 1, 6, 6], [1, 1, 6, 6]]⟩, .edge 89 ⟨![[0], [1], [], [2], [3], [0, 2, 6, 2], [1, 4, 5], [2, 5, 2], [2, 4, 6], [3, 6, 7]], ![[0], [1], [3], [4], [3, 3], [3, 7, 3], [3, 8], [0, 6, 0, 6], [0, 7, 0, 7], [0, 7, 0, 7]]⟩, .edge 104 ⟨![[], [1], [2, 0], [0, 4], [3], [], [1, 4], [0, 5, 2], [0, 4, 6], [0, 3, 0, 7]], ![[2, 3, 2], [1], [7, 8], [4], [1, 1, 1, 6], [2, 3, 8, 2], [3, 8], [1, 6], [1, 1, 6, 6], [1, 1, 6, 6]]⟩, .edge 96 ⟨![[0], [], [7, 1, 2], [1, 6, 7], [3], [0, 4, 8], [4, 7], [1, 5, 2], [0, 1, 0], [3, 5]], ![[0], [0, 8, 0], [0, 2, 5, 8], [4], [0, 3, 0, 8], [4, 9], [3, 8], [0, 6, 5], [2, 2, 6], [2, 2, 6]]⟩, .edge 112 ⟨![[], [1, 0], [2, 0], [0, 4], [3], [], [1, 0, 4], [0, 5, 2], [0, 4, 6], [0, 3, 0, 7]], ![[2, 3, 2], [6, 3], [7, 8], [4], [1, 1, 1, 6], [2, 3, 8, 2], [3, 8], [1, 1], [1, 1, 6, 6], [1, 1, 6, 6]]⟩, .edge 84 ⟨![[0], [1], [2], [2, 3, 2], [], [5, 0, 7], [5, 1], [6, 2, 7], [1, 1, 3, 6], []], ![[0], [1], [2], [7, 3, 7], [0, 1, 6, 5], [0, 1, 5, 1], [3, 3], [0, 3, 0, 8], [0, 1, 5, 6], [0, 1, 5, 6]]⟩, .edge 99 ⟨![[], [1], [2], [2, 3, 2], [0, 0, 0], [], [1, 4], [2, 4, 6], [3, 4], [0]], ![[9], [1], [2], [7, 3, 7], [1, 1, 1, 6], [2, 3, 3, 7], [3, 3], [1, 6], [1, 1, 6, 6], [1, 1, 6, 6]]⟩, .edge 91 ⟨![[0], [], [2], [2, 3, 2], [1, 1, 1], [0, 4, 8], [4, 7], [2, 4, 5], [2, 3, 2], [1]], ![[0], [9], [2], [7, 3, 7], [0, 2, 7, 5], [4, 6, 4], [3, 3], [0, 6, 5], [2, 7], [2, 7]]⟩, .edge 107 ⟨![[], [0, 0, 1, 0], [2], [2, 3, 2], [0, 0, 0], [], [0, 5, 1], [2, 4, 6], [3, 4], [0]], ![[9], [1, 9], [2], [7, 3, 7], [1, 1, 1, 6], [2, 3, 3, 7], [3, 3], [1, 1], [1, 1, 6, 6], [1, 1, 6, 6]]⟩, .edge 88 ⟨![[0], [1], [], [3, 4, 6], [0, 2, 0], [0, 4, 6, 8], [1, 4, 5], [4, 5, 8], [3, 4, 5], [2]], ![[0], [1], [9], [7, 8], [3, 7, 8], [3, 8], [3, 3], [0, 6, 0, 6], [0, 7, 0, 7], [0, 7, 0, 7]]⟩, .edge 103 ⟨![[], [1], [0, 0, 2, 0], [3, 4, 6], [0, 0, 0], [], [1, 4], [0, 6, 2, 7], [3, 4], [0]], ![[9], [1], [2, 9], [7, 8, 2], [1, 1, 1, 6], [2, 3, 3, 2], [3, 3], [1, 6], [1, 1, 6, 6], [1, 1, 6, 6]]⟩, .edge 95 ⟨![[0], [], [1, 5, 6, 2], [3, 4, 6], [1, 1, 1], [0, 4, 8], [4, 7], [4, 2, 1], [3, 4, 6], [1]], ![[0], [9], [2, 9], [7, 3, 2], [0, 4, 5, 4], [4, 6, 4], [3, 3], [0, 6, 5], [2, 2, 6], [2, 2, 6]]⟩, .edge 111 ⟨![[], [0, 0, 1, 0], [0, 0, 2, 0], [3, 4, 6], [0, 0, 0], [], [0, 5, 1], [0, 6, 2, 7], [3, 4], [0]], ![[9], [1, 9], [2, 9], [7, 8, 2], [1, 1, 1, 6], [2, 3, 3, 2], [3, 3], [1, 1], [1, 1, 6, 6], [1, 1, 6, 6]]⟩, .edge 86 ⟨![[0], [1], [2], [], [1, 1, 3], [0, 6], [1], [2, 5, 6], [6], [4, 3, 6]], ![[0], [1], [2], [1, 1, 4], [2, 8, 7], [0, 9, 0, 9], [8], [4, 4, 8], [2, 2, 7, 7], [2, 2, 7, 7]]⟩, .edge 101 ⟨![[], [1], [2], [0, 1, 1, 3], [0, 0, 0], [], [1, 4], [2, 4, 6], [0, 0, 3, 4, 0], [0]], ![[9], [1], [2], [1, 1, 4, 3], [1, 1, 1, 6], [2, 3, 8, 7], [3, 8], [1, 6], [1, 1, 6, 6], [1, 1, 6, 6]]⟩, .edge 93 ⟨![[0], [], [2], [1, 3, 6, 8], [1, 1, 1], [0, 4, 8], [4, 7], [2, 4, 5], [0, 1, 3, 0, 7], [1]], ![[0], [9], [2], [0, 3, 0, 9], [0, 2, 7, 5], [4, 6, 4], [3, 8], [0, 6, 5], [2, 7], [2, 7]]⟩, .edge 109 ⟨![[], [0, 0, 1, 0], [2], [0, 4, 3, 7], [0, 0, 0], [], [0, 5, 1], [2, 4, 6], [3, 0, 1, 1], [0]], ![[9], [1, 9], [2], [1, 3, 9, 6], [1, 1, 1, 6], [2, 3, 8, 7], [3, 8], [1, 1], [1, 1, 6, 6], [1, 1, 6, 6]]⟩, .edge 90 ⟨![[0], [1], [], [1, 2, 1, 3], [0, 2, 0], [0, 4, 6, 8], [1, 4, 5], [4, 5, 8], [0, 2, 0, 5, 3], [2]], ![[0], [1], [9], [1, 6, 3, 4], [3, 3], [3, 7, 3], [3, 8], [0, 6, 0, 6], [0, 7, 0, 7], [0, 7, 0, 7]]⟩, .edge 105 ⟨![[], [1], [0, 0, 2, 0], [0, 1, 1, 3], [0, 0, 0], [], [1, 4], [0, 2, 3, 3], [0, 0, 3, 4, 0], [0]], ![[9], [1], [2, 9], [1, 1, 4, 3], [1, 1, 1, 6], [2, 3, 8, 2], [3, 8], [1, 6], [1, 1, 6, 6], [1, 1, 6, 6]]⟩, .edge 97 ⟨![[0], [], [1, 5, 6, 2], [1, 3, 6, 8], [1, 1, 1], [0, 4, 8], [4, 7], [4, 2, 1], [0, 1, 3, 0, 7], [1]], ![[0], [9], [2, 9], [0, 3, 0, 9], [0, 3, 0, 8], [4, 6, 4], [3, 8], [0, 6, 5], [2, 2, 6], [2, 2, 6]]⟩, .edge 113 ⟨![[], [0, 0, 1, 0], [0, 0, 2, 0], [0, 4, 3, 7], [0, 0, 0], [], [0, 5, 1], [0, 2, 3, 3], [3, 0, 1, 1], [0]], ![[9], [1, 9], [2, 9], [1, 3, 9, 6], [1, 1, 1, 6], [2, 3, 8, 2], [3, 8], [1, 1], [1, 1, 6, 6], [1, 1, 6, 6]]⟩] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 5 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 10) : Classified H :=
  classify_of_checks 10 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node10

namespace Node11

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [5]],
   ![[0], [1], [2], [0, 0], [1, 3, 1, 3], [3], [0, 0, 0, 0], [1, 0, 1, 0], [0, 1, 0, 3, 1, 3], [0, 1, 0, 3, 1, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 10) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 11 :=
  generated_of_packed 10 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 120 ⟨![[], [0], [1], [2], [3], [0, 3, 4], [3, 1], [1, 2, 1]], ![[1], [2], [3], [4], [1, 3, 1, 3], [1, 5, 4], [4, 4], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .core, .edge 124 ⟨![[], [0, 4, 6], [1], [2], [3], [0], [3, 1], [0, 0, 2]], ![[5], [2], [3], [4], [1, 1, 1, 5], [1, 1], [4, 4], [1, 1, 3, 7], [1, 1, 3, 7], [1, 1, 3, 7]]⟩, .edge 115 ⟨![[0], [1], [], [2], [0, 3, 6], [3, 1], [], [2, 5, 7]], ![[0], [1], [3], [0, 0], [1, 3, 1, 3], [0, 3, 7, 4], [0, 0, 0, 0], [0, 7, 4, 3], [0, 7, 4, 3], [0, 7, 4, 3]]⟩, .edge 122 ⟨![[], [1], [0], [2], [3], [1, 3, 4], [0], [2, 5, 7]], ![[2], [1], [3], [4], [1, 3, 1, 3], [1, 5, 4], [4, 4], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 118 ⟨![[0], [], [1, 1, 1], [2], [0, 3, 4, 7], [4, 5], [1], [2, 5, 7]], ![[0], [6], [3], [0, 0], [3, 5, 7], [4, 5, 0], [5, 5], [2, 3, 6, 3], [2, 3, 6, 3], [2, 3, 6, 3]]⟩, .edge 126 ⟨![[], [1, 0], [0], [2], [3], [0, 1, 3], [0], [2, 5, 7]], ![[2], [1, 2], [3], [4], [1, 1, 1, 5], [1, 1], [4, 4], [1, 1, 3, 7], [1, 1, 3, 7], [1, 1, 3, 7]]⟩, .edge 114 ⟨![[0], [1], [2], [], [0, 5], [1, 5], [2, 5, 7], []], ![[0], [1], [2], [0, 0], [1, 5], [0, 1, 4, 5], [0, 0, 0, 0], [0, 1, 0, 5], [0, 1, 0, 5], [0, 1, 0, 5]]⟩, .edge 121 ⟨![[], [1], [2], [2, 0, 2], [3], [1, 3, 4], [3, 2], [0]], ![[7], [1], [2], [4], [1, 3, 5, 7], [1, 5, 4], [4, 4], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 117 ⟨![[0], [], [2], [1, 4, 6], [0, 3, 4, 7], [4, 5], [2, 3], [1]], ![[0], [7], [2], [0, 0], [7, 7], [3, 3, 5], [5, 5], [0, 3, 3, 4], [0, 3, 3, 4], [0, 3, 3, 4]]⟩, .edge 125 ⟨![[], [0, 0, 1, 0], [2], [2, 0, 2], [3], [0, 1, 5], [3, 2], [0]], ![[7], [1, 7], [2], [4], [1, 1, 1, 5], [1, 1], [4, 4], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 116 ⟨![[0], [1], [], [2, 2, 2], [0, 3, 6], [3, 1], [], [2]], ![[0], [1], [7], [0, 0], [1, 3, 3, 1], [0, 3, 3, 4], [0, 0, 0, 0], [0, 7, 0, 7], [0, 7, 0, 7], [0, 7, 0, 7]]⟩, .edge 123 ⟨![[], [1], [5, 0, 2], [0, 0, 0, 6], [3], [1, 3, 4], [5, 0, 2], [0]], ![[7], [1], [2, 7], [4], [1, 3, 5, 7], [1, 5, 4], [4, 4], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 119 ⟨![[0], [], [0, 1, 2, 0], [1, 4, 6], [0, 3, 4, 7], [4, 5], [5, 1, 2], [1]], ![[0], [7], [2, 7], [0, 0], [7, 7], [3, 3, 5], [5, 5], [0, 3, 3, 4], [0, 3, 3, 4], [0, 3, 3, 4]]⟩, .edge 127 ⟨![[], [0, 0, 1, 0], [5, 0, 2], [0, 0, 0, 6], [3], [0, 1, 5], [5, 0, 2], [0]], ![[7], [1, 7], [2, 7], [4], [1, 1, 1, 5], [1, 1], [4, 4], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 11) : Classified H :=
  classify_of_checks 11 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node11

namespace Node12

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [1, 0, 1, 0, 1, 1], [0, 2, 1, 0, 1, 2], [0, 0, 0, 0], [1, 0, 1, 0], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 11) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 12 :=
  generated_of_packed 11 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 130 ⟨![[], [0], [1], [2], [0, 2, 3], [1, 4, 6, 7]], ![[1], [2], [3], [1, 5, 1, 2], [1, 2, 4, 2, 3], [3, 3], [1, 4, 3], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 132 ⟨![[], [0, 3, 5], [1], [2], [0], [0, 0, 1, 4]], ![[4], [2], [3], [1, 1, 1, 4], [2, 4, 4, 5], [3, 3], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 128 ⟨![[0], [1], [], [0, 4], [4, 1], []], ![[0], [1], [0, 0], [0, 0, 0, 4, 1, 3], [0, 4, 0, 1], [0, 0, 0, 0], [0, 4, 0, 4], [0, 0, 0, 0, 0, 3, 0, 3], [0, 0, 0, 0, 0, 3, 0, 3], [0, 0, 0, 0, 0, 3, 0, 3]]⟩, .edge 131 ⟨![[], [1], [0, 4, 2, 5], [2], [1, 2, 3], [0]], ![[5], [1], [3], [5, 4, 4, 2], [2, 2, 3], [3, 3], [1, 4, 3], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 129 ⟨![[0], [], [0, 1, 0, 6], [0, 2, 3, 7], [3, 6], [1]], ![[0], [5], [0, 0], [5, 4, 2], [2, 4, 2], [4, 4], [3, 4, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 133 ⟨![[], [2, 1, 0, 4], [0, 4, 2, 5], [2], [0, 4, 1], [0]], ![[5], [1, 5], [3], [1, 1, 1, 4], [2, 2, 3], [3, 3], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 12) : Classified H :=
  classify_of_checks 12 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node12

namespace Node13

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [1, 0, 1, 0, 1, 1], [2, 0, 2, 0], [0, 0, 0, 0], [1, 0, 1, 0], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 12) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 13 :=
  generated_of_packed 12 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 136 ⟨![[], [0], [1], [2], [0, 2, 3], [2, 4, 1]], ![[1], [2], [3], [5, 1, 1, 5], [2, 5, 3], [3, 3], [1, 4, 3], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 138 ⟨![[], [0, 3, 5], [1], [2], [0], [2, 4, 1]], ![[4], [2], [3], [1, 1, 1, 4], [2, 5, 3], [3, 3], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 134 ⟨![[0], [1], [], [1, 0, 1, 4], [0, 4, 0, 1], []], ![[0], [1], [0, 0], [0, 0, 0, 3, 1, 4], [3, 0], [0, 0, 0, 0], [0, 0, 3, 3], [0, 0, 0, 1, 0, 1, 3, 3], [0, 0, 0, 1, 0, 1, 3, 3], [0, 0, 0, 1, 0, 1, 3, 3]]⟩, .edge 137 ⟨![[], [1], [0, 0, 0], [2], [1, 2, 3], [0]], ![[5], [1], [3], [5, 4, 4, 2], [2, 3, 2, 3], [3, 3], [1, 4, 3], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 135 ⟨![[0], [], [1, 1, 1], [0, 2, 3, 7], [3, 6], [1]], ![[0], [5], [0, 0], [5, 4, 2], [2, 3, 5, 0], [4, 4], [3, 4, 0], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩, .edge 139 ⟨![[], [0, 0, 1, 0], [0, 0, 0], [2], [0, 1, 2, 4], [0]], ![[5], [1, 5], [3], [1, 1, 1, 4], [2, 1, 1, 2], [3, 3], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 13) : Classified H :=
  classify_of_checks 13 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node13

namespace Node14

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [4]],
   ![[0], [1], [2], [0, 0], [3], [3, 1, 1, 3, 3], [3, 3], [1, 0, 1, 0], [0, 1, 3, 0, 1, 3], [0, 1, 3, 0, 1, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 13) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 14 :=
  generated_of_packed 13 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 146 ⟨![[], [0], [1], [4, 2], [3], [0, 3, 4, 6], [3, 1], [0, 2, 0, 5]], ![[1], [2], [7, 1, 1], [4], [1, 1], [1, 5, 2, 6], [1, 5, 4], [1, 2, 6, 5], [1, 2, 6, 5], [1, 2, 6, 5]]⟩, .core, .edge 150 ⟨![[], [0, 0, 4, 0], [1], [4, 2], [3], [0], [3, 1], [0, 2, 4, 0]], ![[5], [2], [7, 1, 5], [4], [1, 5], [1, 3, 1, 7], [1, 1, 5, 5], [1, 1], [1, 1], [1, 1]]⟩, .edge 141 ⟨![[0], [1], [], [4, 2], [0, 3, 3, 3], [3, 1], [], [4, 2]], ![[0], [1], [0, 0, 3, 5, 1], [0, 0], [1, 1], [1, 1, 5, 5], [1, 0, 1, 0], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 148 ⟨![[], [1], [0], [4, 2], [3], [0, 3, 1, 0], [0], [0, 4, 2, 0]], ![[2], [1], [7, 1, 1], [4], [1, 1], [1, 3, 3, 5, 4], [1, 5, 4], [1, 2, 4, 2, 5], [1, 2, 4, 2, 5], [1, 2, 4, 2, 5]]⟩, .edge 144 ⟨![[0], [], [1, 1, 1], [4, 2], [0, 3, 4, 6], [4], [1], [2, 4, 6]], ![[0], [6], [0, 4, 7], [0, 0], [5], [0, 6, 4, 2], [4, 5, 0], [3, 3, 5, 5], [3, 3, 5, 5], [3, 3, 5, 5]]⟩, .edge 152 ⟨![[], [1, 0], [0], [4, 2], [3], [0, 3, 1], [0], [0, 4, 2, 0]], ![[2], [1, 2], [7, 1, 5], [4], [1, 5], [1, 3, 1, 7], [1, 1, 5, 5], [1, 1], [1, 1], [1, 1]]⟩, .edge 140 ⟨![[0], [1], [2], [], [0, 3, 3], [1, 6], [2], [3, 3]], ![[0], [1], [2], [0, 0], [1, 1], [1, 0, 1, 4], [1, 0, 1, 0], [0, 1, 0, 5], [0, 1, 0, 5], [0, 1, 0, 5]]⟩, .edge 147 ⟨![[], [1], [2], [0, 3, 4], [3], [1, 0, 0, 4], [3, 2], [0, 4, 7]], ![[1, 4, 1, 3], [1], [2], [4], [1, 1], [1, 5, 2, 6], [1, 5, 4], [1, 2, 6, 5], [1, 2, 6, 5], [1, 2, 6, 5]]⟩, .edge 143 ⟨![[0], [], [2], [6, 1], [0, 3, 1, 1], [4], [2, 3], [4, 1]], ![[0], [6, 3, 2], [2], [0, 0], [5], [3, 3, 5], [4, 5, 0], [0, 7, 0, 7], [0, 7, 0, 7], [0, 7, 0, 7]]⟩, .edge 151 ⟨![[], [0, 1, 4, 5], [2], [0, 3, 4], [3], [0, 1, 6], [3, 2], [0, 4, 7]], ![[1, 4, 5, 3], [5, 5, 3, 1], [2], [4], [1, 5], [1, 3, 5, 3], [1, 1, 5, 5], [1, 1], [1, 1], [1, 1]]⟩, .edge 142 ⟨![[0], [1], [], [2, 4, 7], [0, 3, 3, 3], [3, 1], [], [2, 4, 7]], ![[0], [1], [0, 0, 5, 3, 5], [0, 0], [1, 1], [1, 1, 5, 5], [1, 0, 1, 0], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 149 ⟨![[], [1], [6, 0, 2], [0, 3, 4], [3], [1, 0, 0, 4], [6, 0, 2], [0, 4, 7]], ![[1, 4, 1, 3], [1], [1, 2, 5, 3], [4], [1, 1], [1, 5, 3, 3], [1, 5, 4], [1, 3, 3, 5], [1, 3, 3, 5], [1, 3, 3, 5]]⟩, .edge 145 ⟨![[0], [], [0, 1, 2, 0], [6, 1], [0, 3, 1, 1], [4], [6, 1, 2], [4, 1]], ![[0], [0, 4, 3, 5], [0, 2, 3, 0], [0, 0], [5], [3, 3, 5], [4, 5, 0], [0, 7, 0, 7], [0, 7, 0, 7], [0, 7, 0, 7]]⟩, .edge 153 ⟨![[], [0, 1, 4, 5], [6, 0, 2], [0, 3, 4], [3], [0, 1, 6], [6, 0, 2], [0, 4, 7]], ![[1, 4, 5, 3], [5, 5, 3, 1], [1, 2, 1, 3], [4], [1, 5], [1, 3, 5, 3], [1, 1, 5, 5], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 14) : Classified H :=
  classify_of_checks 14 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node14

namespace Node15

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [1, 1, 2, 0, 0, 2], [0, 2, 1, 0, 1, 2], [0, 0, 0, 0], [1, 0, 1, 0], [0, 2, 1, 0, 2, 1], [0, 2, 1, 0, 2, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 14) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 15 :=
  generated_of_packed 14 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 156 ⟨![[], [0], [1], [2], [0, 3, 5], [1, 4, 6, 7]], ![[1], [2], [3], [4, 1, 4, 4], [1, 2, 4, 2, 3], [3, 3], [1, 3, 4], [1, 2, 3, 2, 4], [1, 2, 3, 2, 4], [1, 2, 3, 2, 4]]⟩, .core, .edge 158 ⟨![[], [0, 2, 3], [1], [2], [0], [0, 0, 1, 4]], ![[4], [2], [3], [1, 2, 3, 2, 4], [2, 4, 4, 5], [3, 3], [1, 1, 3, 3], [4, 5, 4, 5], [4, 5, 4, 5], [4, 5, 4, 5]]⟩, .edge 154 ⟨![[0], [1], [], [0, 4], [4, 1], []], ![[0], [1], [0, 0], [1, 1, 3, 3], [0, 4, 0, 1], [0, 0, 0, 0], [1, 0, 1, 0], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 157 ⟨![[], [1], [0, 4, 2, 5], [2], [1, 3, 5], [0]], ![[5], [1], [3], [4, 1, 4, 4], [2, 2, 3], [3, 3], [1, 3, 4], [1, 5, 1, 5], [1, 5, 1, 5], [1, 5, 1, 5]]⟩, .edge 155 ⟨![[0], [], [1, 1, 1], [3, 0, 7], [1, 4, 1], [1]], ![[0], [5], [0, 0], [2, 0, 2, 3], [2, 4, 2], [0, 0, 0, 0], [3, 4, 0], [2, 4, 5, 4], [2, 4, 5, 4], [2, 4, 5, 4]]⟩, .edge 159 ⟨![[], [0, 1, 0, 0, 3], [0, 4, 2, 5], [2], [0, 4, 1], [0]], ![[5], [1, 5], [3], [1, 2, 3, 5, 4], [2, 2, 3], [3, 3], [1, 1, 3, 3], [1, 2, 4, 5, 3], [1, 2, 4, 5, 3], [1, 2, 4, 5, 3]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 15) : Classified H :=
  classify_of_checks 15 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node15

namespace Node16

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [1, 0, 2, 0, 2, 1], [2, 0, 2, 0], [0, 0, 0, 0], [1, 0, 1, 0], [0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 15) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 16 :=
  generated_of_packed 15 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 162 ⟨![[], [0], [1], [2], [3, 0, 2, 4], [2, 4, 1]], ![[1], [2], [3], [1, 1, 2, 5, 3], [2, 5, 3], [3, 3], [1, 4, 3], [1, 3, 3, 3, 4], [1, 3, 3, 3, 4], [1, 3, 3, 3, 4]]⟩, .core, .edge 164 ⟨![[], [0, 3, 4, 5], [1], [2], [0], [2, 4, 1]], ![[4], [2], [3], [1, 2, 4, 5, 3], [2, 5, 3], [3, 3], [1, 1, 4, 4], [1, 1], [1, 1], [1, 1]]⟩, .edge 160 ⟨![[0], [1], [], [1, 0, 1, 4], [0, 4, 0, 1], []], ![[0], [1], [0, 0], [1, 0, 3, 1], [3, 0], [0, 0, 0, 0], [0, 0, 3, 3], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 163 ⟨![[], [1], [0, 0, 0], [2], [3, 1, 2, 4], [0]], ![[5], [1], [3], [1, 2, 2, 1], [2, 3, 2, 3], [3, 3], [1, 4, 3], [2, 4, 2, 4], [2, 4, 2, 4], [2, 4, 2, 4]]⟩, .edge 161 ⟨![[0], [], [1, 1, 1], [4, 0, 2, 3], [3, 4], [1]], ![[0], [5], [0, 0], [3, 2, 2, 3], [2, 3, 5, 0], [0, 4, 3], [3, 4, 0], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩, .edge 165 ⟨![[], [0, 0, 1, 0], [0, 0, 0], [2], [1, 3, 0, 5], [0]], ![[5], [1, 5], [3], [4, 2, 4, 3, 2], [2, 2, 4, 4], [3, 3], [1, 1, 4, 4], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 16) : Classified H :=
  classify_of_checks 16 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node16

namespace Node17

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 0, 1, 2, 0, 1, 0, 1, 2], [0, 1, 0, 1, 2, 0, 1, 0, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 16) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 17 :=
  generated_of_packed 16 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 167 ⟨![[0], [], [1], [2, 0], [], [1]], ![[0], [2], [0, 0, 0, 3], [0, 2, 0, 0, 2, 3, 0, 3], [0, 2, 3, 0, 3, 2], [0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 2, 3, 0, 2, 3], [0, 2, 3, 0, 2, 3], [0, 2, 3, 0, 2, 3]]⟩, .edge 170 ⟨![[], [0, 0, 0], [1], [3, 6], [0], [1, 4]], ![[4], [2], [1, 1, 3], [5, 3, 5], [2, 5], [3, 3], [3, 3, 3, 5, 3, 5], [1, 2, 4, 5], [1, 2, 4, 5], [1, 2, 4, 5]]⟩, .edge 166 ⟨![[0], [1], [], [4, 0], [1], []], ![[0], [1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 0, 3, 3, 0], [0, 0, 0, 0, 0, 3, 3, 3], [0, 0, 0, 0], [0, 0, 0, 0, 0, 3, 3, 0], [0, 0, 0, 0, 0, 3, 0, 3], [0, 0, 0, 0, 0, 3, 0, 3], [0, 0, 0, 0, 0, 3, 0, 3]]⟩, .edge 169 ⟨![[], [1], [0, 4, 3, 5], [3, 6], [1, 2], [0]], ![[5], [1], [1, 4], [5, 3, 2], [2, 3, 2], [3, 3], [2, 1, 5, 4], [2, 2, 2, 2, 3, 3], [2, 2, 2, 2, 3, 3], [2, 2, 2, 2, 3, 3]]⟩, .edge 168 ⟨![[0], [], [1], [2, 0], [], [1]], ![[0], [2], [0, 0, 0, 3], [0, 2, 0, 0, 2, 3, 0, 3], [0, 2, 0, 3, 0, 2], [0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 2, 0, 3, 2, 3], [0, 2, 0, 3, 2, 3], [0, 2, 0, 3, 2, 3]]⟩, .edge 171 ⟨![[], [0, 2, 1, 3], [0, 4, 3, 5], [3, 6], [0, 1], [0]], ![[5], [1, 5], [1, 1, 3], [5, 3, 2], [2, 3, 2], [3, 3], [2, 1, 3, 2, 1, 3], [1, 2, 1, 2, 3, 3], [1, 2, 1, 2, 3, 3], [1, 2, 1, 2, 3, 3]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 17) : Classified H :=
  classify_of_checks 17 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node17

namespace Node18

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 1, 1, 1, 0, 1], [0, 3, 2, 0, 3, 2], [3, 3], [0, 3, 0, 2, 3, 2], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 17) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 18 :=
  generated_of_packed 17 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 178 ⟨![[], [0], [1], [2], [], [0, 3], [1, 4, 6, 7], [2, 5]], ![[1], [2], [3], [1, 6, 1, 2], [2, 3, 6, 7], [3, 3], [1, 3, 3, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .core, .edge 182 ⟨![[], [0, 3], [1], [2], [], [0], [1, 4, 6, 7], [2, 5]], ![[5], [2], [3], [1, 2, 5, 2], [2, 3, 6, 7], [3, 3], [1, 1, 3, 3], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 173 ⟨![[0], [1], [], [2], [4, 0, 6], [4, 1], [], [2, 6]], ![[0], [1], [3], [1, 0, 4, 5], [0, 3, 4, 7], [3, 3], [0, 3, 0, 7], [0, 7, 0, 7], [0, 7, 0, 7], [0, 7, 0, 7]]⟩, .edge 180 ⟨![[], [1], [0, 0, 0], [2], [], [1, 3], [0], [2, 5]], ![[6], [1], [3], [1, 6, 5, 6], [2, 3, 2, 3], [3, 3], [1, 3, 3, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 176 ⟨![[0], [], [1, 4, 3, 5], [2], [0, 3, 7], [3, 6], [1], [2, 5]], ![[0], [6], [3], [6, 5, 2], [2, 5, 2], [3, 3], [0, 5, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 184 ⟨![[], [0, 4, 1, 3], [0, 0, 0], [2], [], [0, 4, 1], [0], [2, 5]], ![[6], [1, 6], [3], [1, 2, 1, 6], [2, 3, 2, 3], [3, 3], [1, 1, 3, 3], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 172 ⟨![[0], [1], [2], [], [0, 5], [1, 5], [2, 6], [5]], ![[0], [1], [2], [1, 1, 2, 6], [0, 6, 0, 2], [7], [2, 6], [0, 1, 0, 5, 2, 6], [0, 1, 0, 5, 2, 6], [0, 1, 0, 5, 2, 6]]⟩, .edge 179 ⟨![[], [1], [2], [0, 5], [], [1, 3], [0, 2, 6, 0], [0]], ![[7], [1], [2], [1, 6, 1, 2], [2, 3, 2, 3], [3, 7], [1, 3, 1, 3], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 175 ⟨![[0], [], [2], [1, 1, 1], [0, 3, 7], [1, 1], [2, 4], [1]], ![[0], [7], [2], [6, 5, 6], [2, 6], [3, 7], [0, 5, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 183 ⟨![[], [1, 0], [2], [0, 5], [], [0, 1], [0, 2, 6, 0], [0]], ![[7], [1, 7], [2], [1, 2, 5, 2], [2, 3, 2, 3], [3, 7], [1, 1, 3, 7], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 174 ⟨![[0], [1], [], [2, 6], [4, 0, 6], [4, 1], [], [2]], ![[0], [1], [7], [1, 0, 4, 5], [0, 3, 0, 3], [3, 7], [0, 3, 4, 3], [0, 7, 4, 3], [0, 7, 4, 3], [0, 7, 4, 3]]⟩, .edge 181 ⟨![[], [1], [2, 0], [0, 5], [], [1, 3], [0, 2, 2, 2], [0]], ![[7], [1], [2, 7], [1, 6, 5, 6], [2, 3, 6, 7], [3, 7], [1, 3, 1, 3], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 177 ⟨![[0], [], [1, 3, 2, 4], [1, 1, 1], [0, 3, 7], [1, 1], [4, 2, 1], [1]], ![[0], [7], [2, 7], [6, 5, 2], [2, 5, 2], [3, 7], [0, 5, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 185 ⟨![[], [1, 0], [2, 0], [0, 5], [], [0, 1], [0, 2, 2, 2], [0]], ![[7], [1, 7], [2, 7], [1, 2, 1, 6], [2, 3, 6, 7], [3, 7], [1, 1, 3, 7], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 18) : Classified H :=
  classify_of_checks 18 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node18

namespace Node19

def gen : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 6 10 :=
  ⟨![[0], [1], [2], [3], [4], [5]],
   ![[0], [1], [2], [3], [4], [5], [3, 3], [0, 4, 0, 4], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 0, 4]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 18) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 19 :=
  generated_of_packed 18 gen generationWords generation_checked

def pivot (σ : Fin 6 → Bool) : Fin 6 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 64, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 6 → Bool) : BranchData 6 :=
  ![.core, .core, .edge 201 ⟨![[0], [], [1], [2], [3], [4], [0], [], [1], [2, 5], [3], [0, 0, 4]], ![[0], [2], [3], [4], [5], [3, 3], [0, 4, 0, 4], [0, 5, 0, 11], [0, 5, 0, 11], [0, 5, 0, 11]]⟩, .edge 232 ⟨![[], [0, 0, 0], [1], [2], [3], [4], [0, 0], [0], [1], [2, 5], [3, 5, 7], [4, 7]], ![[7], [2], [3], [4], [5], [3, 3], [4, 6, 10], [4, 10], [4, 10], [4, 10]]⟩, .edge 193 ⟨![[0], [1], [], [2], [3], [4], [0], [1], [], [2, 6], [0, 0, 3], [4]], ![[0], [1], [3], [4], [5], [3, 3], [0, 4, 0, 4], [0, 3, 0, 9], [0, 3, 0, 9], [0, 3, 0, 9]]⟩, .edge 224 ⟨![[], [1], [0, 0, 0], [2], [3], [4], [0, 0], [1], [0], [2, 5], [0, 3, 0], [4, 7]], ![[8], [1], [3], [4], [5], [3, 3], [4, 6, 10], [4, 10], [4, 10], [4, 10]]⟩, .edge 209 ⟨![[0], [], [1], [2], [3], [4], [0], [], [1], [2, 5], [3], [0, 0, 4]], ![[0], [2], [3], [4], [5], [3, 3], [0, 4, 0, 4], [0, 5, 0, 11], [0, 5, 0, 11], [0, 5, 0, 11]]⟩, .edge 240 ⟨![[], [0, 0, 0, 1], [0, 0, 0], [2], [3], [4], [0, 0], [0, 1], [0], [2, 5], [0, 3, 0], [4, 7]], ![[8], [1, 8], [3], [4], [5], [3, 3], [4, 6, 10], [4, 10], [4, 10], [4, 10]]⟩, .edge 189 ⟨![[0], [1], [2], [], [3], [4], [0, 5], [1, 5], [2, 6], [5], [3], [4, 7]], ![[0], [1], [2], [4], [5], [9], [2, 8], [5, 11], [5, 11], [5, 11]]⟩, .edge 220 ⟨![[], [1], [2], [0, 0, 0, 5], [3], [4], [0, 0], [1], [2], [0], [3, 5, 7], [4, 7]], ![[9], [1], [2], [4], [5], [3, 9], [4, 6, 10], [4, 10], [4, 10], [4, 10]]⟩, .edge 205 ⟨![[0], [], [2], [1, 5], [3], [4], [0], [], [2], [1], [3], [0, 0, 4]], ![[0], [9], [2], [4], [5], [3, 9], [0, 4, 0, 4], [0, 5, 0, 11], [0, 5, 0, 11], [0, 5, 0, 11]]⟩, .edge 236 ⟨![[], [0, 0, 0, 1], [2], [0, 0, 0, 5], [3], [4], [0, 0], [0, 1], [2], [0], [3, 5, 7], [4, 7]], ![[9], [1, 9], [2], [4], [5], [3, 9], [4, 6, 10], [4, 10], [4, 10], [4, 10]]⟩, .edge 197 ⟨![[0], [1], [], [2, 6], [3], [4], [0], [1], [], [2], [0, 0, 3], [4]], ![[0], [1], [9], [4], [5], [3, 9], [0, 4, 0, 4], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 228 ⟨![[], [1], [0, 0, 2, 0], [0, 0, 0, 5], [3], [4], [0, 0], [1], [2, 0], [0], [2, 3, 2], [4, 7]], ![[9], [1], [2, 9], [4], [5], [3, 9], [4, 6, 10], [4, 10], [4, 10], [4, 10]]⟩, .edge 213 ⟨![[0], [], [2, 1], [1, 5], [3], [4], [0], [], [2, 1], [1], [3], [0, 0, 4]], ![[0], [9], [2, 9], [4], [5], [3, 9], [0, 4, 0, 4], [0, 5, 0, 11], [0, 5, 0, 11], [0, 5, 0, 11]]⟩, .edge 244 ⟨![[], [0, 0, 0, 1], [0, 0, 2, 0], [0, 0, 0, 5], [3], [4], [0, 0], [0, 1], [2, 0], [0], [2, 3, 2], [4, 7]], ![[9], [1, 9], [2, 9], [4], [5], [3, 9], [4, 6, 10], [4, 10], [4, 10], [4, 10]]⟩, .edge 187 ⟨![[0], [1], [2], [3], [], [4], [0, 5, 7], [1], [0, 0, 2], [3], [5], [4, 7]], ![[0], [1], [2], [3], [5], [10], [0, 6, 10], [5, 11], [5, 11], [5, 11]]⟩, .edge 218 ⟨![[], [1], [2], [3], [0, 5, 6], [4], [6, 7], [1], [2], [3, 5], [0], [4, 7]], ![[10], [1], [2], [3], [5], [3, 3], [4, 4], [5, 11], [5, 11], [5, 11]]⟩, .edge 203 ⟨![[0], [], [2], [3], [1], [4], [0], [], [2], [3, 5], [1], [0, 0, 4]], ![[0], [4], [2], [3], [5], [3, 3], [0, 4, 0, 4], [0, 5, 0, 11], [0, 5, 0, 11], [0, 5, 0, 11]]⟩, .edge 234 ⟨![[], [1, 0, 6], [2], [3], [0, 5, 6], [4], [6, 7], [0, 1, 5], [2], [3, 5], [0], [4, 7]], ![[10], [1, 10], [2], [3], [5], [3, 3], [4, 4], [5, 11], [5, 11], [5, 11]]⟩, .edge 195 ⟨![[0], [1], [], [3], [0, 0, 2], [4], [0], [1], [], [3, 6], [2], [4]], ![[0], [1], [10], [3], [5], [3, 3], [0, 4, 0, 10], [0, 3, 0, 9], [0, 3, 0, 9], [0, 3, 0, 9]]⟩, .edge 226 ⟨![[], [1], [0, 2, 5], [3], [0, 5, 6], [4], [6, 7], [1], [2, 0, 7], [3, 5], [0], [4, 7]], ![[10], [1], [2, 10], [3], [5], [3, 3], [4, 4], [5, 11], [5, 11], [5, 11]]⟩, .edge 211 ⟨![[0], [], [2, 1, 5], [3], [1], [4], [0], [], [2, 1, 5], [3, 5], [1], [0, 0, 4]], ![[0], [4], [2, 4], [3], [5], [3, 3], [0, 4, 0, 4], [0, 5, 0, 11], [0, 5, 0, 11], [0, 5, 0, 11]]⟩, .edge 242 ⟨![[], [1, 0, 6], [0, 2, 5], [3], [0, 5, 6], [4], [6, 7], [0, 1, 5], [2, 0, 7], [3, 5], [0], [4, 7]], ![[10], [1, 10], [2, 10], [3], [5], [3, 3], [4, 4], [5, 11], [5, 11], [5, 11]]⟩, .edge 191 ⟨![[0], [1], [2], [], [3, 5], [4], [0, 5], [1, 5], [2, 6], [5], [3], [4, 7]], ![[0], [1], [2], [10], [5], [9], [2, 8], [5, 11], [5, 11], [5, 11]]⟩, .edge 222 ⟨![[], [1], [2], [3, 0, 6], [0, 5, 6], [4], [6, 7], [1], [2], [0, 3, 5], [0], [4, 7]], ![[10], [1], [2], [3, 10], [5], [3, 9], [4, 4], [5, 11], [5, 11], [5, 11]]⟩, .edge 207 ⟨![[0], [], [2], [1, 3], [1], [4], [0], [], [2], [3, 1], [1], [0, 0, 4]], ![[0], [4], [2], [3, 4], [5], [3, 9], [0, 4, 0, 4], [0, 5, 0, 11], [0, 5, 0, 11], [0, 5, 0, 11]]⟩, .edge 238 ⟨![[], [1, 0, 6], [2], [3, 0, 6], [0, 5, 6], [4], [6, 7], [0, 1, 5], [2], [0, 3, 5], [0], [4, 7]], ![[10], [1, 10], [2], [3, 10], [5], [3, 9], [4, 4], [5, 11], [5, 11], [5, 11]]⟩, .edge 199 ⟨![[0], [1], [], [0, 2, 0, 3], [0, 0, 2], [4], [0], [1], [], [2, 3, 5], [2], [4]], ![[0], [1], [10], [3, 10], [5], [3, 9], [0, 4, 0, 10], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 230 ⟨![[], [1], [0, 2, 5], [3, 0, 6], [0, 5, 6], [4], [6, 7], [1], [2, 0, 7], [0, 3, 5], [0], [4, 7]], ![[10], [1], [2, 10], [3, 10], [5], [3, 9], [4, 4], [5, 11], [5, 11], [5, 11]]⟩, .edge 215 ⟨![[0], [], [2, 1, 5], [1, 3], [1], [4], [0], [], [2, 1, 5], [3, 1], [1], [0, 0, 4]], ![[0], [4], [2, 4], [3, 4], [5], [3, 9], [0, 4, 0, 4], [0, 5, 0, 11], [0, 5, 0, 11], [0, 5, 0, 11]]⟩, .edge 246 ⟨![[], [1, 0, 6], [0, 2, 5], [3, 0, 6], [0, 5, 6], [4], [6, 7], [0, 1, 5], [2, 0, 7], [0, 3, 5], [0], [4, 7]], ![[10], [1, 10], [2, 10], [3, 10], [5], [3, 9], [4, 4], [5, 11], [5, 11], [5, 11]]⟩, .edge 186 ⟨![[0], [1], [2], [3], [4], [], [0, 7], [0, 0, 1], [2], [3, 7], [4, 7], []], ![[0], [1], [2], [3], [4], [3, 3], [0, 6], [0, 0, 0, 6], [0, 0, 0, 6], [0, 0, 0, 6]]⟩, .edge 217 ⟨![[], [1], [2], [3], [4], [0, 6], [6, 7], [1], [2], [3, 5], [4, 5, 7], [0]], ![[11], [1], [2], [3], [4], [3, 3], [5, 5], [4, 10], [4, 10], [4, 10]]⟩, .edge 202 ⟨![[0], [], [2], [3], [4], [0, 0, 1], [0], [], [2], [3, 5], [4], [1]], ![[0], [11], [2], [3], [4], [3, 3], [0, 4, 0, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 233 ⟨![[], [0, 1], [2], [3], [4], [0, 6], [1, 1], [1, 0, 7], [2], [3, 5], [4, 5, 7], [0]], ![[11], [1, 11], [2], [3], [4], [3, 3], [5, 5], [4, 10], [4, 10], [4, 10]]⟩, .edge 194 ⟨![[0], [1], [], [3], [4], [2], [0], [1], [], [3, 6], [0, 0, 4], [2]], ![[0], [1], [5], [3], [4], [3, 3], [0, 4, 0, 4], [0, 3, 0, 9], [0, 3, 0, 9], [0, 3, 0, 9]]⟩, .edge 225 ⟨![[], [1], [2, 0, 6], [3], [4], [0, 6], [6, 7], [1], [0, 2], [3, 5], [4, 5, 7], [0]], ![[11], [1], [2, 11], [3], [4], [3, 3], [5, 5], [4, 10], [4, 10], [4, 10]]⟩, .edge 210 ⟨![[0], [], [1, 2], [3], [4], [0, 0, 1], [0], [], [1, 2], [3, 5], [4], [1]], ![[0], [11], [2, 11], [3], [4], [3, 3], [0, 4, 0, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 241 ⟨![[], [0, 1], [2, 0, 6], [3], [4], [0, 6], [1, 1], [1, 0, 7], [0, 2], [3, 5], [4, 5, 7], [0]], ![[11], [1, 11], [2, 11], [3], [4], [3, 3], [5, 5], [4, 10], [4, 10], [4, 10]]⟩, .edge 190 ⟨![[0], [1], [2], [], [4], [3, 3, 3], [0, 5], [1, 5], [2, 6], [5], [4], [3]], ![[0], [1], [2], [11], [4], [9], [2, 8], [5, 5, 9], [5, 5, 9], [5, 5, 9]]⟩, .edge 221 ⟨![[], [1], [2], [3, 0, 6], [4], [0, 6], [6, 7], [1], [2], [0, 3, 7], [3, 3, 4], [0]], ![[11], [1], [2], [3, 11], [4], [3, 9], [5, 5], [4, 10], [4, 10], [4, 10]]⟩, .edge 206 ⟨![[0], [], [2], [0, 0, 3, 1], [4], [0, 0, 1], [0], [], [2], [1, 3, 7], [4], [1]], ![[0], [11], [2], [3, 11], [4], [3, 9], [0, 4, 0, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 237 ⟨![[], [0, 1], [2], [3, 0, 6], [4], [0, 6], [1, 1], [1, 0, 7], [2], [0, 3, 7], [3, 3, 4], [0]], ![[11], [1, 11], [2], [3, 11], [4], [3, 9], [5, 5], [4, 10], [4, 10], [4, 10]]⟩, .edge 198 ⟨![[0], [1], [], [3, 2], [4], [2], [0], [1], [], [2, 3, 7], [0, 0, 4], [2]], ![[0], [1], [5], [3, 5], [4], [3, 9], [0, 4, 0, 4], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 229 ⟨![[], [1], [2, 0, 6], [3, 0, 6], [4], [0, 6], [6, 7], [1], [0, 2], [0, 3, 7], [3, 3, 4], [0]], ![[11], [1], [2, 11], [3, 11], [4], [3, 9], [5, 5], [4, 10], [4, 10], [4, 10]]⟩, .edge 214 ⟨![[0], [], [1, 2], [0, 0, 3, 1], [4], [0, 0, 1], [0], [], [1, 2], [1, 3, 7], [4], [1]], ![[0], [11], [2, 11], [3, 11], [4], [3, 9], [0, 4, 0, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 245 ⟨![[], [0, 1], [2, 0, 6], [3, 0, 6], [4], [0, 6], [1, 1], [1, 0, 7], [0, 2], [0, 3, 7], [3, 3, 4], [0]], ![[11], [1, 11], [2, 11], [3, 11], [4], [3, 9], [5, 5], [4, 10], [4, 10], [4, 10]]⟩, .edge 188 ⟨![[0], [1], [2], [3], [], [3, 4, 3], [0, 4, 4], [1], [0, 0, 2], [3], [5], [4]], ![[0], [1], [2], [3], [11], [10], [0, 6, 10], [5, 5, 10], [5, 5, 10], [5, 5, 10]]⟩, .edge 219 ⟨![[], [1], [2], [3], [4, 0, 6], [0, 6], [6, 7], [1], [2], [3, 5], [0, 4, 7], [0]], ![[11], [1], [2], [3], [4, 11], [3, 3], [4, 4], [4, 4, 6], [4, 4, 6], [4, 4, 6]]⟩, .edge 204 ⟨![[0], [], [2], [3], [1, 4, 7], [0, 0, 1], [0], [], [2], [3, 5], [1, 4, 7], [1]], ![[0], [11], [2], [3], [4, 11], [3, 3], [0, 4, 0, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 235 ⟨![[], [0, 1], [2], [3], [4, 0, 6], [0, 6], [1, 1], [1, 0, 7], [2], [3, 5], [0, 4, 7], [0]], ![[11], [1, 11], [2], [3], [4, 11], [3, 3], [4, 4], [4, 4, 6], [4, 4, 6], [4, 4, 6]]⟩, .edge 196 ⟨![[0], [1], [], [3], [4, 2], [2], [0], [1], [], [3, 6], [2, 4, 7], [2]], ![[0], [1], [5], [3], [4, 5], [3, 3], [0, 4, 0, 10], [0, 3, 0, 9], [0, 3, 0, 9], [0, 3, 0, 9]]⟩, .edge 227 ⟨![[], [1], [2, 0, 6], [3], [4, 0, 6], [0, 6], [6, 7], [1], [0, 2], [3, 5], [0, 4, 7], [0]], ![[11], [1], [2, 11], [3], [4, 11], [3, 3], [4, 4], [4, 4, 6], [4, 4, 6], [4, 4, 6]]⟩, .edge 212 ⟨![[0], [], [1, 2], [3], [1, 4, 7], [0, 0, 1], [0], [], [1, 2], [3, 5], [1, 4, 7], [1]], ![[0], [11], [2, 11], [3], [4, 11], [3, 3], [0, 4, 0, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 243 ⟨![[], [0, 1], [2, 0, 6], [3], [4, 0, 6], [0, 6], [1, 1], [1, 0, 7], [0, 2], [3, 5], [0, 4, 7], [0]], ![[11], [1, 11], [2, 11], [3], [4, 11], [3, 3], [4, 4], [4, 4, 6], [4, 4, 6], [4, 4, 6]]⟩, .edge 192 ⟨![[0], [1], [2], [], [3, 3, 3, 4], [3, 3, 3], [0, 5], [1, 5], [2, 6], [5], [3, 4, 7], [3]], ![[0], [1], [2], [11], [4, 11], [9], [2, 8], [5, 5, 9], [5, 5, 9], [5, 5, 9]]⟩, .edge 223 ⟨![[], [1], [2], [3, 0, 6], [4, 0, 6], [0, 6], [6, 7], [1], [2], [0, 3, 7], [0, 4, 7], [0]], ![[11], [1], [2], [3, 11], [4, 11], [3, 9], [4, 4], [4, 4, 6], [4, 4, 6], [4, 4, 6]]⟩, .edge 208 ⟨![[0], [], [2], [0, 0, 3, 1], [1, 4, 7], [0, 0, 1], [0], [], [2], [1, 3, 7], [1, 4, 7], [1]], ![[0], [11], [2], [3, 11], [4, 11], [3, 9], [0, 4, 0, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 239 ⟨![[], [0, 1], [2], [3, 0, 6], [4, 0, 6], [0, 6], [1, 1], [1, 0, 7], [2], [0, 3, 7], [0, 4, 7], [0]], ![[11], [1, 11], [2], [3, 11], [4, 11], [3, 9], [4, 4], [4, 4, 6], [4, 4, 6], [4, 4, 6]]⟩, .edge 200 ⟨![[0], [1], [], [3, 2], [4, 2], [2], [0], [1], [], [2, 3, 7], [2, 4, 7], [2]], ![[0], [1], [5], [3, 5], [4, 5], [3, 9], [0, 4, 0, 10], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 231 ⟨![[], [1], [2, 0, 6], [3, 0, 6], [4, 0, 6], [0, 6], [6, 7], [1], [0, 2], [0, 3, 7], [0, 4, 7], [0]], ![[11], [1], [2, 11], [3, 11], [4, 11], [3, 9], [4, 4], [4, 4, 6], [4, 4, 6], [4, 4, 6]]⟩, .edge 216 ⟨![[0], [], [1, 2], [0, 0, 3, 1], [1, 4, 7], [0, 0, 1], [0], [], [1, 2], [1, 3, 7], [1, 4, 7], [1]], ![[0], [11], [2, 11], [3, 11], [4, 11], [3, 9], [0, 4, 0, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 247 ⟨![[], [0, 1], [2, 0, 6], [3, 0, 6], [4, 0, 6], [0, 6], [1, 1], [1, 0, 7], [0, 2], [0, 3, 7], [0, 4, 7], [0]], ![[11], [1, 11], [2, 11], [3, 11], [4, 11], [3, 9], [4, 4], [4, 4, 6], [4, 4, 6], [4, 4, 6]]⟩] ⟨signatureIndex σ % 64, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 6 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 6 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 6 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 6 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 19) : Classified H :=
  classify_of_checks 19 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node19

namespace Node20

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 1, 2, 3, 2], [0, 1, 2, 0, 2, 1], [3, 3], [1, 0, 1, 0], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 19) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 20 :=
  generated_of_packed 19 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 254 ⟨![[], [0], [1], [2, 3], [], [0, 3], [1, 4], [2, 3, 5]], ![[1], [2], [1, 1, 1, 3, 5], [1, 1, 1, 5], [2, 6], [3, 3], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .core, .edge 258 ⟨![[], [0, 3], [1], [2, 3], [], [0], [1, 4], [2, 3, 5]], ![[5], [2], [1, 1, 1, 5, 3], [1, 1, 1, 5], [2, 6], [3, 3], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 249 ⟨![[0], [1], [], [2, 3], [0, 4], [1, 4, 6], [], [1, 1, 2]], ![[0], [1], [1, 1, 7], [0, 1, 5, 4], [0, 4], [3, 3], [0, 3, 0, 7], [0, 1, 4, 5], [0, 1, 4, 5], [0, 1, 4, 5]]⟩, .edge 256 ⟨![[], [1], [0, 4], [2, 3], [], [1, 3], [0], [2, 3, 5]], ![[6], [1], [1, 1, 1, 3, 5], [1, 1, 1, 5], [2, 2], [3, 3], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 252 ⟨![[0], [], [1, 1, 1], [2, 3], [0, 3, 7], [3, 6], [1], [2, 3]], ![[0], [6], [2, 3, 6, 5], [0, 2, 4, 2], [0, 2, 4, 6], [3, 3], [0, 5, 4], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 260 ⟨![[], [1, 0, 4], [0, 4], [2, 3], [], [0, 1, 4, 6], [0], [2, 3, 5]], ![[6], [1, 6], [1, 1, 1, 5, 3], [1, 1, 1, 5], [2, 2], [3, 3], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 248 ⟨![[0], [1], [2], [], [0, 5], [1], [2, 6], [5]], ![[0], [1], [2], [1, 1, 2, 6], [0, 2, 0, 2], [7], [2, 6], [0, 1, 0, 1, 2, 6], [0, 1, 0, 1, 2, 6], [0, 1, 0, 1, 2, 6]]⟩, .edge 255 ⟨![[], [1], [2], [0, 3, 5], [], [1, 3], [2, 4], [0, 3]], ![[1, 1, 1, 5, 7], [1], [2], [1, 1, 1, 5], [2, 6], [3, 7], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 251 ⟨![[0], [], [2], [1, 6], [0, 3, 7], [3, 6], [0, 2, 6, 0], [1, 3]], ![[0], [0, 4, 7], [2], [0, 3, 0, 7], [0, 2, 0, 2], [3, 7], [0, 5, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 259 ⟨![[], [1, 0], [2], [0, 3, 5], [], [1, 0, 3], [2, 4], [0, 3]], ![[1, 1, 1, 3, 1], [3, 1], [2], [1, 1, 1, 5], [2, 6], [3, 7], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 250 ⟨![[0], [1], [], [2, 1, 1], [0, 4], [1, 4, 6], [], [2, 3]], ![[0], [1], [3, 1, 1], [0, 1, 5, 4], [0, 4], [3, 7], [0, 3, 4, 3], [0, 1, 4, 5], [0, 1, 4, 5], [0, 1, 4, 5]]⟩, .edge 257 ⟨![[], [1], [2, 0], [0, 3, 5], [], [1, 3], [2, 0, 4], [0, 3]], ![[1, 1, 1, 5, 7], [1], [3, 1, 1, 6], [1, 1, 1, 5], [2, 2], [3, 7], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 253 ⟨![[0], [], [2, 1, 1, 1], [1, 6], [0, 3, 7], [3, 6], [1, 2, 2, 2], [1, 3]], ![[0], [0, 4, 7], [3, 6, 5], [0, 2, 4, 2], [0, 2, 4, 6], [3, 7], [0, 5, 4], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 261 ⟨![[], [1, 0], [2, 0], [0, 3, 5], [], [1, 0, 3], [2, 0, 4], [0, 3]], ![[1, 1, 1, 3, 1], [3, 1], [3, 1, 5, 6], [1, 1, 1, 5], [2, 2], [3, 7], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 20) : Classified H :=
  classify_of_checks 20 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node20

namespace Node21

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [0, 1, 0, 0, 1, 1, 1, 1, 0, 1], [0, 1, 0, 1, 0, 1, 1, 0], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 0, 1, 1, 1, 1, 0], [0, 0, 1, 1, 0, 0, 1, 1], [0, 0, 1, 1, 0, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 20) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 21 :=
  generated_of_packed 20 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .edge 262 ⟨![[], [0], [1], [3, 0, 5]], ![[1], [2], [1, 1, 1, 1, 2, 2, 3, 1], [1, 3, 3, 3], [1, 3, 2, 2, 3, 1], [3, 3, 3, 3], [1, 1, 1, 2, 2, 1], [1, 1, 2, 1, 1, 2], [1, 1, 2, 1, 1, 2], [1, 1, 2, 1, 1, 2]]⟩, .core, .edge 263 ⟨![[], [0, 1, 3, 5], [1], [0]], ![[3], [2], [1, 1, 2, 3, 1, 3, 1], [1, 2, 1, 3, 1], [1, 1, 2, 1, 2, 1], [3, 1, 3, 1], [1, 2, 2, 3, 1, 3], [1, 2, 3, 1, 2, 3], [1, 2, 3, 1, 2, 3], [1, 2, 3, 1, 2, 3]]⟩] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 2 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 21) : Classified H :=
  classify_of_checks 21 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node21

namespace Node22

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [1, 1, 1, 0, 1, 1, 0, 1], [1, 1, 0, 1, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 1], [1, 0, 0, 1, 0, 1, 1, 0], [1, 0, 1, 0, 1, 0, 1, 0], [0, 0, 1, 1, 0, 1, 1, 0], [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 21) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 22 :=
  generated_of_packed 21 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .core, .edge 264 ⟨![[0], [], [2, 3, 0, 1], [0, 0, 1, 4]], ![[0], [3, 2, 3, 2, 3], [3, 0, 3, 0], [2, 0, 2, 3, 2], [0, 0, 3, 2, 3, 2], [2, 0, 2, 0], [0, 0, 3, 0, 3, 0], [0, 2, 0, 3, 2, 3], [0, 2, 0, 3, 2, 3], [0, 2, 0, 3, 2, 3]]⟩, .edge 265 ⟨![[], [1, 6, 0, 3], [2, 5], [0]], ![[3], [1, 1, 1, 1, 1, 2, 3], [1, 1, 3, 3, 2], [2, 1, 2, 2, 1], [1, 2, 1, 3, 3, 2], [1, 1, 3, 3], [1, 1, 1, 2, 2, 1], [1, 1, 2, 3, 3, 2], [1, 1, 2, 3, 3, 2], [1, 1, 2, 3, 3, 2]]⟩] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 2 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 22) : Classified H :=
  classify_of_checks 22 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node22

namespace Node23

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [4]],
   ![[0], [1], [2], [0, 0, 0, 1, 0, 2, 1], [3], [0, 1, 1, 1, 2, 0, 1, 2], [2, 3, 2, 3], [0, 1, 0, 1, 1, 1], [0, 2, 0, 3, 2, 3], [0, 2, 0, 3, 2, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 22) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 23 :=
  generated_of_packed 22 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 269 ⟨![[0], [], [3, 1, 4], [2], [0, 7], [3], [3, 1], [2, 5, 6]], ![[0], [5, 6], [3], [5], [2, 2, 2, 6], [6, 6], [0, 0], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 276 ⟨![[], [0, 6, 7], [3, 1, 4], [2], [6], [0], [1, 3, 4, 5], [2]], ![[5], [1, 4, 6, 1], [3], [1, 5], [1, 1, 1, 6, 1, 6], [2, 3, 2, 3, 4], [4], [1, 1, 1, 4, 5], [1, 1, 1, 4, 5], [1, 1, 1, 4, 5]]⟩, .edge 267 ⟨![[0], [1], [], [2], [0, 5, 7], [1, 4], [5, 7], [2, 6, 7]], ![[0], [1], [3], [1, 1], [1, 1, 1, 5], [0, 3, 4, 7], [0, 0], [0, 0, 3, 7], [0, 0, 3, 7], [0, 0, 3, 7]]⟩, .edge 274 ⟨![[], [1], [0, 3, 4, 5, 6], [2], [6], [1, 7], [3, 0, 4], [2]], ![[1, 6, 1], [1], [3], [1, 1], [1, 1, 1, 2, 4, 5, 2], [2, 3, 4, 6, 3], [4], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5]]⟩, .edge 271 ⟨![[0], [], [1], [2], [0, 7], [3], [3, 1, 4], [2, 5, 6]], ![[0], [2], [3], [5], [2, 2, 2, 5, 6], [6, 2], [0, 0], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 278 ⟨![[], [0, 0, 1, 0], [0, 1, 1, 6], [2], [6], [1, 0], [3, 0, 4], [2]], ![[1, 2, 4, 5], [2, 1, 1, 1], [3], [1, 5], [1, 1, 1, 2, 1, 6], [2, 3, 4, 6, 3], [4], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩, .edge 266 ⟨![[0], [1], [1, 2, 1], [], [0], [5, 1, 6], [2, 3, 4, 6], []], ![[0], [1], [5, 2, 5], [1, 1], [1, 1, 2, 5, 6, 1], [0, 0, 2, 6], [0, 0], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 273 ⟨![[], [1], [1, 2, 1], [0, 6], [6], [1, 7], [1, 2, 5, 1], [0]], ![[7], [1], [1, 2, 5], [1, 1], [1, 1, 1, 2, 1, 6], [2, 3, 6, 3], [4], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5]]⟩, .edge 270 ⟨![[0], [], [3, 2, 4], [1, 1, 1], [0, 7], [3], [3, 2], [1]], ![[0], [7], [5, 6], [5], [2, 2, 2, 6], [6, 6], [0, 0], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 277 ⟨![[], [0, 1, 5], [3, 2, 4], [0, 6], [6], [1, 0, 7], [1, 2, 1], [0]], ![[7], [1, 7], [1, 4, 6, 1], [1, 5], [1, 1, 1, 6, 1, 6], [2, 3, 6, 3], [4], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩, .edge 268 ⟨![[0], [1], [], [1, 2, 1, 7], [0, 5, 7], [1, 4], [5, 7], [2, 3, 4]], ![[0], [1], [5, 1, 7], [1, 1], [1, 1, 1, 5], [0, 0, 3, 3], [0, 0], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 275 ⟨![[], [1], [0, 2, 3, 4, 5], [0, 6], [6], [1, 7], [0, 1, 2, 1, 5], [0]], ![[7], [1], [1, 2, 1, 7], [1, 1], [1, 1, 1, 2, 4, 5, 2], [2, 3, 2, 7], [4], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5]]⟩, .edge 272 ⟨![[0], [], [1, 2, 6], [1, 1, 1], [0, 7], [3], [0, 2, 0, 3, 1], [1]], ![[0], [7], [0, 0, 3, 2], [5], [2, 3, 6, 7], [6, 2], [0, 0], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 279 ⟨![[], [0, 1, 5], [1, 2, 1, 0], [0, 6], [6], [1, 0, 7], [0, 1, 2, 1, 7], [0]], ![[7], [1, 7], [1, 2, 3, 5], [1, 5], [1, 1, 1, 2, 1, 6], [2, 3, 2, 7], [4], [2, 3, 6, 3], [2, 3, 6, 3], [2, 3, 6, 3]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 23) : Classified H :=
  classify_of_checks 23 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node23

namespace Node24

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1], [1, 1, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0, 1, 0], [0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 23) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 24 :=
  generated_of_packed 23 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .edge 280 ⟨![[], [0], [1], [0, 1, 3, 5]], ![[1], [2], [1, 1, 1, 3, 1, 3, 2], [1, 1, 1, 3, 2], [1, 1, 2, 3, 2, 3], [1, 1, 1, 3, 1, 1, 1, 3], [1, 2, 2, 3, 1, 3], [1, 1, 2, 2, 3, 3], [1, 1, 2, 2, 3, 3], [1, 1, 2, 2, 3, 3]]⟩, .core, .edge 281 ⟨![[], [3, 4, 0], [1], [0]], ![[3], [2], [1, 1, 2, 1, 1, 3, 1], [1, 2, 3, 1, 1, 2], [1, 2, 1, 2, 3, 3], [1, 1, 2, 1, 1, 2], [1, 1, 2, 1, 1, 2, 2, 2], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 2 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 24) : Classified H :=
  classify_of_checks 24 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node24

end ReeTwo.SylowModel.SmallEvenMaximalLower
