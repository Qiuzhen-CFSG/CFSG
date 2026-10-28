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

namespace Node275

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [1, 1], [1, 1, 2, 1, 2, 1], [0, 0], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 274) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 275 :=
  generated_of_packed 274 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 2815 ⟨![[0], [], [1], [0, 5], [2], [1, 3]], ![[0], [2], [4], [2, 5], [0, 0], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]⟩, .noncentric 168, .edge 2814 ⟨![[0], [1], [], [0, 5], [3, 1], []], ![[0], [1], [1, 1], [1, 1, 4, 1], [0, 0], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]⟩, .noncentric 168, .edge 2816 ⟨![[0], [], [1, 1, 1], [0, 5], [2], [1]], ![[0], [5], [4], [2, 4, 2], [0, 0], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]⟩, .noncentric 168] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 275) : Classified H :=
  classify_of_checks 275 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node275

namespace Node276

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [3], [4]],
   ![[0], [1], [1, 1], [2], [3], [0, 1, 0, 1, 1, 2, 1, 3], [0, 0], [0, 0], [0, 0], [0, 0]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 275) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 276 :=
  generated_of_packed 275 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2818 ⟨![[0], [], [1, 2, 4], [1], [0, 4], [3], [1, 2, 4, 5], [1, 5]], ![[0], [3], [0, 2, 4, 7], [5], [0, 0, 0, 4], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]⟩, .edge 2821 ⟨![[], [0, 4, 5], [1, 2, 4], [1], [5], [0], [1, 2, 4], [1]], ![[5], [3], [1, 1, 1, 2, 5, 3], [1, 5], [1, 1, 1, 4, 5], [4], [4], [4], [4], [4]]⟩, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 32, .edge 2817 ⟨![[0], [1], [], [2, 4], [0], [1, 5], [], [2, 4]], ![[0], [1], [0, 1, 0, 1, 1, 3, 5], [1, 1], [0, 1, 0, 1, 1, 5], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]⟩, .edge 2820 ⟨![[], [1], [0, 2, 4, 5], [0, 5], [5], [1, 4], [0, 2, 4], [0]], ![[7], [1], [1, 1, 1, 2, 1, 3], [1, 1], [1, 1, 1, 5], [4], [4], [4], [4], [4]]⟩, .edge 2819 ⟨![[0], [], [0, 1, 0, 2, 3], [1, 1, 1], [0, 4], [3], [1, 2, 4], [1]], ![[0], [7], [0, 2, 0, 3, 5], [5], [0, 0, 0, 4], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]⟩, .edge 2822 ⟨![[], [0, 1, 4], [0, 2, 4, 5], [0, 5], [5], [0, 1, 5], [0, 2, 4], [0]], ![[7], [1, 7], [1, 1, 1, 2, 1, 3], [1, 5], [1, 1, 1, 4, 5], [4], [4], [4], [4], [4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 276) : Classified H :=
  classify_of_checks 276 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node276

namespace Node277

def gen : Fin 2 → SylowModel :=
  ![⟨⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [0, 0, 0, 1, 0, 1, 1, 1], [1, 1], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 276) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 277 :=
  generated_of_packed 276 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .core, .edge 2823 ⟨![[0], [], [0, 2, 5], [3]], ![[0], [0, 0], [0, 0, 0, 2], [3], [0, 0, 2, 3, 2, 3], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]⟩, .edge 2824 ⟨![[], [1, 2, 0], [1], [0]], ![[3], [2], [1, 1, 1, 3, 2], [1, 3], [1, 1, 1, 2, 1, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 2 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 277) : Classified H :=
  classify_of_checks 277 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node277

namespace Node278

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [3]],
   ![[0], [1], [0, 0], [2], [0, 0, 0, 1, 2, 0, 1, 2], [0, 0, 1, 0, 2, 0, 1, 2], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 277) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 278 :=
  generated_of_packed 277 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 2825 ⟨![[0], [], [1], [0, 3], [], [1]], ![[0], [2], [0, 0], [0, 0, 3, 0], [0, 0, 2, 3, 2, 3], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]⟩, .edge 2826 ⟨![[], [2, 0, 3], [1], [2], [0], [1, 4]], ![[4], [2], [3], [1, 1, 3], [2, 5], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .noncentric 136, .noncentric 8, .noncentric 184, .noncentric 56] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 278) : Classified H :=
  classify_of_checks 278 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node278

namespace Node279

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [3], [4]],
   ![[0], [1], [1, 1], [2], [3], [0, 2, 0, 2], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 278) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 279 :=
  generated_of_packed 278 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2830 ⟨![[0], [], [1], [2], [0, 5], [3], [0, 1, 0], [2, 5]], ![[0], [2], [3], [5], [0, 0], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2837 ⟨![[], [0, 4, 5], [1], [2], [4], [0], [1, 5], [2]], ![[5], [2], [3], [1, 5], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2828 ⟨![[0], [1], [], [2], [0, 5], [0, 1, 0], [], [2]], ![[0], [1], [3], [1, 1], [0, 0], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2835 ⟨![[], [1], [0, 0, 0], [2], [4], [1, 5], [0], [2]], ![[6], [1], [3], [1, 1], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2832 ⟨![[0], [], [1, 3, 4], [2], [0, 5], [3], [1], [2, 5]], ![[0], [6], [3], [5], [0, 0], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2839 ⟨![[], [0, 1], [0, 0, 0], [2], [4], [1, 0], [0], [2]], ![[6], [1, 6], [3], [1, 5], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2827 ⟨![[0], [1], [2], [], [0], [1, 5], [2], []], ![[0], [1], [2], [1, 1], [0, 0], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩, .edge 2834 ⟨![[], [1], [2], [0, 4], [4], [1, 5], [2, 5], [0]], ![[7], [1], [2], [1, 1], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2831 ⟨![[0], [], [2], [1, 3], [0, 5], [3], [0, 2, 0], [1]], ![[0], [7], [2], [5], [0, 0], [5, 5], [5, 5], [5, 5], [5, 5], [5, 5]]⟩, .edge 2838 ⟨![[], [0, 1, 4], [2], [0, 4], [4], [0, 1, 5], [2, 5], [0]], ![[7], [1, 7], [2], [1, 5], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2829 ⟨![[0], [1], [], [2], [0, 5], [0, 1, 0], [], [2]], ![[0], [1], [3], [1, 1], [0, 0], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2836 ⟨![[], [1], [2, 0, 4], [0, 4], [4], [1, 5], [0, 2], [0]], ![[7], [1], [2, 7], [1, 1], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2833 ⟨![[0], [], [2, 1, 3], [1, 3], [0, 5], [3], [1, 2], [1]], ![[0], [7], [2, 7], [5], [0, 0], [5, 5], [5, 5], [5, 5], [5, 5], [5, 5]]⟩, .edge 2840 ⟨![[], [0, 1, 4], [2, 0, 4], [0, 4], [4], [0, 1, 5], [0, 2], [0]], ![[7], [1, 7], [2, 7], [1, 5], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 279) : Classified H :=
  classify_of_checks 279 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node279

namespace Node280

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 1, 0, 2, 1], [0, 0, 0, 1, 1, 1, 0, 1], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 279) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 280 :=
  generated_of_packed 279 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 2841 ⟨![[0], [], [1, 2, 3, 5], [0, 3, 5], [2], [1, 2, 3, 4]], ![[0], [0, 3, 4, 5], [4], [0, 0, 0, 2, 2, 3], [0, 0], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2842 ⟨![[], [0, 3, 4], [0, 0, 1, 4], [4], [0], [0, 0, 1, 4]], ![[4], [4, 2, 4], [1, 4], [1, 1, 3, 4, 1], [3], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .noncentric 152, .noncentric 104, .noncentric 24, .noncentric 232] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 280) : Classified H :=
  classify_of_checks 280 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node280

namespace Node281

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [4]],
   ![[0], [1], [1, 1], [0, 1, 0, 1, 1, 1], [2], [0, 0], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 280) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 281 :=
  generated_of_packed 280 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 2844 ⟨![[0], [], [1], [0, 3, 4], [2], [1, 5]], ![[0], [2], [4], [0, 3], [0, 0], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .edge 2847 ⟨![[], [3, 0], [1], [4], [0], [1]], ![[4], [2], [1, 4], [1, 1, 2, 4, 2, 1], [3], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩, .edge 2843 ⟨![[0], [1], [], [0], [1, 5], []], ![[0], [1], [1, 1], [0, 1, 0, 1, 1, 4], [0, 0], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩, .edge 2846 ⟨![[], [1], [0, 4], [4], [1, 3], [0]], ![[5], [1], [1, 1], [1, 1, 1, 2, 1, 5], [3], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩, .edge 2845 ⟨![[0], [], [1, 2], [0, 3, 4], [2], [1]], ![[0], [5], [4], [0, 3], [0, 0], [4, 4], [4, 4], [4, 4], [4, 4], [4, 4]]⟩, .edge 2848 ⟨![[], [1, 0, 4], [0, 4], [4], [0, 1, 5], [0]], ![[5], [1, 5], [1, 4], [1, 1, 1, 2, 1, 5], [3], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 281) : Classified H :=
  classify_of_checks 281 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node281

namespace Node282

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [1, 1], [1, 1, 2, 1, 2, 1], [0, 0], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 281) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 282 :=
  generated_of_packed 281 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 2850 ⟨![[0], [], [1], [0, 5], [2], [1, 3, 5]], ![[0], [2], [4], [2, 4, 4, 5], [0, 0], [4, 4], [4, 4], [4, 4], [4, 4], [4, 4]]⟩, .noncentric 136, .edge 2849 ⟨![[0], [1], [], [0], [1, 3], []], ![[0], [1], [1, 1], [1, 1, 4, 1], [0, 0], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩, .noncentric 136, .edge 2851 ⟨![[0], [], [2, 1, 3], [0, 5], [2], [1]], ![[0], [5], [4], [2, 2, 4], [0, 0], [4, 4], [4, 4], [4, 4], [4, 4], [4, 4]]⟩, .noncentric 136] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 282) : Classified H :=
  classify_of_checks 282 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node282

namespace Node283

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [1, 1], [1, 1, 2, 1, 2, 1], [0, 0, 1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 282) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 283 :=
  generated_of_packed 282 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 2853 ⟨![[0], [], [1], [0, 4], [2], [1, 3, 5]], ![[0], [2], [4], [0, 2, 3, 5], [0, 0, 0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3]]⟩, .noncentric 8, .edge 2852 ⟨![[0], [1], [], [0], [1, 3], []], ![[0], [1], [1, 1], [1, 1, 4, 1], [0, 0, 1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩, .noncentric 184, .edge 2854 ⟨![[0], [], [2, 1, 3], [0, 4], [2], [1]], ![[0], [5], [4], [2, 2, 4], [0, 0, 0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3]]⟩, .noncentric 56] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 283) : Classified H :=
  classify_of_checks 283 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node283

namespace Node284

def gen : Fin 2 → SylowModel :=
  ![⟨⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [0, 1, 0, 1, 0, 0, 1, 1], [1, 1], [0, 0, 1, 0, 0, 1, 1, 1], [0, 1, 0, 1, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 283) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 284 :=
  generated_of_packed 283 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .core, .noncentric 64, .noncentric 8] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 284) : Classified H :=
  classify_of_checks 284 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node284

namespace Node285

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [5]],
   ![[0], [1], [2], [1, 1], [0, 1, 1, 1, 0, 1], [3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 284) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 285 :=
  generated_of_packed 284 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 2855 ⟨![[], [0], [1], [2], [], [0, 4], [1, 5], [2]], ![[1], [2], [3], [1, 1], [1, 1, 1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .core, .edge 2856 ⟨![[], [0, 4], [1], [2], [], [0], [1, 5], [2]], ![[5], [2], [3], [1, 5], [1, 1, 1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 224, .noncentric 192, .noncentric 224, .noncentric 192] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 285) : Classified H :=
  classify_of_checks 285 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node285

namespace Node286

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [4]],
   ![[0], [1], [2], [0, 1, 0, 1], [3], [0, 1, 0, 1, 1, 1, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 285) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 286 :=
  generated_of_packed 285 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 2857 ⟨![[], [0], [1], [2, 4, 5], [], [0, 4], [1, 5], [2, 4, 5]], ![[1], [2], [1, 1, 3, 5, 1], [1, 1], [1, 1, 1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .core, .edge 2858 ⟨![[], [0, 4], [1], [2, 4, 5], [], [0], [1, 5], [2, 4, 5]], ![[5], [2], [1, 1, 3, 5, 1], [1, 5], [1, 1, 1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 160, .noncentric 160, .noncentric 160, .noncentric 160, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 286) : Classified H :=
  classify_of_checks 286 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node286

namespace Node287

def gen : Fin 5 → SylowModel :=
  ![⟨⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [4], [5]],
   ![[0], [1], [2], [1, 1], [3], [4], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 286) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 287 :=
  generated_of_packed 286 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .edge 2865 ⟨![[], [0], [1], [2], [3], [], [0], [1, 5], [2, 5], [3]], ![[1], [2], [3], [4], [1, 1], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .core, .edge 2869 ⟨![[], [0], [1], [2], [3], [], [0], [1, 5], [2, 5], [3]], ![[1], [2], [3], [4], [1, 1], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .noncentric 224, .noncentric 224, .noncentric 224, .noncentric 224, .noncentric 224, .noncentric 224, .noncentric 224, .noncentric 224, .edge 2860 ⟨![[0], [1], [], [2], [3], [0, 5], [1, 5], [], [2], [3]], ![[0], [1], [3], [4], [1, 1], [0, 5], [0, 5], [0, 5], [0, 5], [0, 5]]⟩, .edge 2867 ⟨![[], [1], [0, 2, 5], [0, 5], [3], [], [1], [0, 2], [0], [3]], ![[8], [1], [2, 8], [4], [1, 1], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2863 ⟨![[0], [], [1, 1, 1, 2], [1, 1, 1], [3], [0], [4], [1, 2], [1], [3, 5]], ![[0], [8], [2, 8], [4], [6], [4, 9], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 2871 ⟨![[], [0, 1, 5], [0, 2, 5], [0, 5], [3], [], [0, 1, 5], [0, 2], [0], [3]], ![[8], [1, 8], [2, 8], [4], [1, 1], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2859 ⟨![[0], [1], [2], [3], [], [0], [1, 5], [2], [3], []], ![[0], [1], [2], [3], [1, 1], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2866 ⟨![[], [1], [2], [3], [0], [], [1], [2, 5], [3, 5], [0]], ![[4], [1], [2], [3], [1, 1], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 2862 ⟨![[0], [], [2], [3], [1, 1, 1], [0], [4], [2, 5], [3, 5], [1]], ![[0], [9], [2], [3], [6], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 2870 ⟨![[], [1, 0], [2], [3], [0], [], [1, 0], [2, 5], [3, 5], [0]], ![[4], [1, 4], [2], [3], [1, 1], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .noncentric 224, .noncentric 224, .noncentric 224, .noncentric 224, .noncentric 224, .noncentric 224, .noncentric 224, .noncentric 224, .edge 2861 ⟨![[0], [1], [], [2, 3], [2], [0, 5], [1, 5], [], [2, 3], [2]], ![[0], [1], [4], [3, 4], [1, 1], [0, 5], [0, 5], [0, 5], [0, 5], [0, 5]]⟩, .edge 2868 ⟨![[], [1], [2, 0], [3, 0], [0], [], [1], [0, 2], [0, 3], [0]], ![[4], [1], [2, 4], [3, 4], [1, 1], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2864 ⟨![[0], [], [1, 1, 1, 2], [1, 1, 1, 3], [1, 1, 1], [0], [4], [1, 2], [1, 3], [1]], ![[0], [9], [2, 9], [3, 9], [6], [2, 2, 6], [2, 2, 6], [2, 2, 6], [2, 2, 6], [2, 2, 6]]⟩, .edge 2872 ⟨![[], [1, 0], [2, 0], [3, 0], [0], [], [1, 0], [0, 2], [0, 3], [0]], ![[4], [1, 4], [2, 4], [3, 4], [1, 1], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 287) : Classified H :=
  classify_of_checks 287 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node287

namespace Node288

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 1, 0, 3, 1], [0, 1, 1, 1, 0, 1], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 287) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 288 :=
  generated_of_packed 287 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 2873 ⟨![[], [0], [1], [2, 3, 4], [], [0, 4], [1, 5], [2, 3, 4]], ![[1], [2], [1, 5, 3], [1, 1], [1, 1, 1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .core, .edge 2874 ⟨![[], [0, 4], [1], [0, 2, 0], [], [0], [1, 5], [0, 2, 0]], ![[5], [2], [1, 1, 3], [1, 5], [1, 1, 1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 224, .noncentric 224, .noncentric 224, .noncentric 224, .noncentric 288, .noncentric 288, .noncentric 288, .noncentric 288, .noncentric 224, .noncentric 224, .noncentric 224, .noncentric 224] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 288) : Classified H :=
  classify_of_checks 288 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node288

namespace Node289

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [1, 1], [0, 1, 1, 1, 0, 1], [0, 1, 1, 1, 2, 0, 2, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 288) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 289 :=
  generated_of_packed 288 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .noncentric 320, .core, .noncentric 256, .noncentric 32, .edge 2875 ⟨![[], [1], [0, 0, 0], [], [1, 3], [0]], ![[5], [1], [1, 1], [1, 1, 1, 4], [1, 1, 1, 2, 2, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .noncentric 96, .edge 2876 ⟨![[], [0, 1, 5], [0, 0, 0], [], [0, 3, 1], [0]], ![[5], [1, 5], [1, 4], [1, 1, 1, 4], [1, 1, 1, 2, 2, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 289) : Classified H :=
  classify_of_checks 289 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node289

namespace Node290

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 1, 1, 0], [0, 1, 0, 1, 1, 1], [0, 1, 1, 2, 1, 0, 1, 2], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 289) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 290 :=
  generated_of_packed 289 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .noncentric 320, .core, .noncentric 256, .noncentric 32, .edge 2877 ⟨![[], [1], [0, 0, 0], [], [3, 1], [0]], ![[5], [1], [4, 4], [1, 1, 4, 1], [1, 1, 2, 2, 4, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .noncentric 96, .edge 2878 ⟨![[], [0, 1], [0, 0, 0], [], [0, 3, 1], [0]], ![[5], [1, 5], [4, 1], [1, 1, 4, 1], [1, 1, 2, 2, 4, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 290) : Classified H :=
  classify_of_checks 290 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node290

namespace Node291

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [4]],
   ![[0], [1], [2], [1, 1], [3], [0, 0, 3], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 290) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 291 :=
  generated_of_packed 290 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 2885 ⟨![[], [0], [1], [2, 4], [4], [0, 5], [1, 5], [2, 4]], ![[1], [2], [3, 4], [1, 1], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .core, .edge 2889 ⟨![[], [0, 4, 5], [1], [2, 4], [4], [0], [1, 5], [2, 4]], ![[5], [2], [3, 4], [1, 5], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2880 ⟨![[0], [1], [], [2, 4], [0, 5], [1, 5], [], [2, 4]], ![[0], [1], [0, 0, 3], [1, 1], [0, 0], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2887 ⟨![[], [1], [0, 0, 0], [2, 4], [4], [1, 5], [0], [2, 4]], ![[6], [1], [3, 4], [1, 1], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2883 ⟨![[0], [], [1, 1, 1], [2, 4], [0, 5], [3], [1], [2, 4, 5]], ![[0], [6], [0, 0, 3], [5], [0, 0], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2891 ⟨![[], [0, 1, 4], [0, 0, 0], [2, 4], [4], [1, 0], [0], [2, 4]], ![[6], [1, 6], [3, 4], [1, 5], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2879 ⟨![[0], [1], [2], [], [0], [1, 5], [2], []], ![[0], [1], [2], [1, 1], [0, 0], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5]]⟩, .edge 2886 ⟨![[], [1], [2], [0], [4], [1, 5], [2, 5], [0, 4]], ![[3], [1], [2], [1, 1], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2882 ⟨![[0], [], [2], [0, 1, 0, 3], [0, 5], [3], [2, 5], [1, 4]], ![[0], [0, 0, 7], [2], [5], [0, 0], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2890 ⟨![[], [0, 1, 4], [2], [0], [4], [0, 1, 5], [2, 5], [0, 4]], ![[3], [1, 3], [2], [1, 5], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2881 ⟨![[0], [1], [], [2, 4], [0, 5], [1, 5], [], [2, 4]], ![[0], [1], [0, 0, 3], [1, 1], [0, 0], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2888 ⟨![[], [1], [2, 0, 4], [0], [4], [1, 5], [0, 2], [0, 4]], ![[3], [1], [2, 3], [1, 1], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2884 ⟨![[0], [], [1, 1, 1, 2], [0, 1, 0, 3], [0, 5], [3], [1, 2], [1, 4]], ![[0], [0, 0, 7], [0, 0, 2, 7], [5], [0, 0], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 2892 ⟨![[], [0, 1, 4], [2, 0, 4], [0], [4], [0, 1, 5], [0, 2], [0, 4]], ![[3], [1, 3], [2, 3], [1, 5], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 291) : Classified H :=
  classify_of_checks 291 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node291

namespace Node292

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 3, 1], [0, 0, 1, 3, 1], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 291) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 292 :=
  generated_of_packed 291 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 2899 ⟨![[], [0], [1], [0, 2, 0, 4], [4], [0, 4, 5], [1, 5], [0, 2, 0, 4]], ![[1], [2], [1, 5, 3], [1, 1], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .core, .edge 2903 ⟨![[], [0, 5], [1], [0, 0, 2, 4], [4], [0], [1, 5], [0, 0, 2, 4]], ![[5], [2], [1, 1, 3, 4], [1, 5], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2894 ⟨![[0], [1], [], [1, 2, 1, 4], [0, 5], [1, 5], [], [1, 2, 1, 4]], ![[0], [1], [0, 0, 1, 3, 1], [1, 1], [0, 0], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2901 ⟨![[], [1], [0, 0, 0], [0, 0, 2, 3], [4], [0, 0, 1], [0], [0, 0, 2, 3]], ![[6], [1], [1, 5, 3], [1, 1], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2897 ⟨![[0], [], [1, 1, 1], [1, 1, 2, 4], [0, 4, 5], [3], [1], [2, 3, 4]], ![[0], [6], [0, 0, 5, 7], [5], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2905 ⟨![[], [0, 1], [0, 0, 0], [0, 0, 2, 3], [4], [0, 1, 5], [0], [0, 0, 2, 3]], ![[6], [1, 6], [1, 1, 3, 4], [1, 5], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2893 ⟨![[0], [1], [2], [], [0], [1, 5], [2], []], ![[0], [1], [2], [1, 1], [0, 0], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5]]⟩, .edge 2900 ⟨![[], [1], [2], [0, 3, 5], [4], [1, 4, 5], [2, 5], [0, 3, 4, 5]], ![[1, 3, 5], [1], [2], [1, 1], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2896 ⟨![[0], [], [2], [1, 4], [0, 4, 5], [3], [2, 5], [1, 1, 1, 4]], ![[0], [0, 0, 3], [2], [5], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2904 ⟨![[], [0, 1], [2], [0, 1, 1], [4], [0, 1, 5], [2, 5], [1, 0, 1]], ![[1, 1, 3], [1, 1, 1, 3], [2], [1, 5], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2895 ⟨![[0], [1], [], [0, 2, 0, 3], [0, 5], [1, 5], [], [0, 2, 0, 3]], ![[0], [1], [0, 0, 1, 3, 5], [1, 1], [0, 0], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2902 ⟨![[], [1], [2, 0, 4], [0, 3, 5], [4], [1, 4, 5], [0, 2], [0, 3, 4, 5]], ![[1, 3, 5], [1], [1, 1, 3, 2], [1, 1], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2898 ⟨![[0], [], [1, 1, 1, 2], [1, 4], [0, 4, 5], [3], [1, 2], [1, 1, 1, 4]], ![[0], [0, 0, 3], [0, 0, 2, 3], [5], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2906 ⟨![[], [0, 1], [2, 0, 4], [0, 1, 1], [4], [0, 1, 5], [0, 2], [1, 0, 1]], ![[1, 1, 3], [1, 1, 1, 3], [1, 1, 2, 3], [1, 5], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 292) : Classified H :=
  classify_of_checks 292 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node292

namespace Node293

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [1, 1], [0, 1, 1, 1, 0, 1], [2, 2], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 292) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 293 :=
  generated_of_packed 292 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 2908 ⟨![[], [0], [1], [], [0, 3], [1, 3]], ![[1], [2], [1, 1], [1, 1, 1, 4], [2, 2], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .noncentric 67, .noncentric 67, .noncentric 67, .edge 2907 ⟨![[0], [], [1, 2], [0, 3, 5], [2], [1]], ![[0], [5], [4], [0, 4, 3, 4], [2, 5], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 2909 ⟨![[], [0, 0, 1, 0], [0, 3], [], [0, 1, 4], [0]], ![[5], [1, 5], [1, 4], [1, 1, 1, 4], [2, 5], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 293) : Classified H :=
  classify_of_checks 293 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node293

namespace Node294

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [1, 1], [0, 1, 1, 1, 0, 1], [2, 2], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 293) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 294 :=
  generated_of_packed 293 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 2911 ⟨![[], [0], [1], [], [0, 3], [3, 1]], ![[1], [2], [1, 1], [1, 1, 1, 4], [2, 2], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .noncentric 131, .noncentric 643, .noncentric 131, .edge 2910 ⟨![[0], [], [1, 2, 5], [0, 3, 5], [2], [1]], ![[0], [5], [4], [0, 4, 3, 4], [2, 5], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 2912 ⟨![[], [0, 0, 1, 0], [3, 0], [], [1, 0, 4], [0]], ![[5], [1, 5], [1, 4], [1, 1, 1, 4], [2, 5], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 294) : Classified H :=
  classify_of_checks 294 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node294

namespace Node295

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [1, 1], [0, 0, 0, 1, 0, 1, 1, 1], [0, 1, 1, 1, 0, 1], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 294) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 295 :=
  generated_of_packed 294 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 2913 ⟨![[], [0], [1], [3, 4, 5], [0, 3], [1, 5]], ![[1], [2], [1, 1], [1, 1, 1, 4], [1, 1, 1, 3, 4], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .core, .edge 2914 ⟨![[], [0, 4], [1], [3, 4, 5], [0], [1, 5]], ![[4], [2], [1, 4], [1, 1, 1, 3, 4], [1, 1, 1, 4], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .noncentric 864, .noncentric 864, .noncentric 864, .noncentric 864] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 295) : Classified H :=
  classify_of_checks 295 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node295

namespace Node296

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [1, 1], [0, 2, 0, 2], [0, 0, 0, 1, 0, 1, 1, 1], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 295) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 296 :=
  generated_of_packed 295 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 2915 ⟨![[], [0], [1], [3, 5], [0, 4, 5], [1, 5]], ![[1], [2], [1, 1], [2, 3, 5], [1, 1, 1, 2, 4, 2], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .core, .edge 2916 ⟨![[], [3, 0, 4], [1], [3, 5], [0], [1, 5]], ![[4], [2], [1, 4], [2, 3, 5], [1, 1, 1, 4, 3], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 296) : Classified H :=
  classify_of_checks 296 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node296

namespace Node297

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [4], [5]],
   ![[0], [1], [0, 0], [0, 0, 1, 2, 1, 2], [2], [3], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 296) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 297 :=
  generated_of_packed 296 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2920 ⟨![[0], [], [1], [2], [0, 3, 4], [3, 4, 5], [1, 5], [2]], ![[0], [2], [3], [0, 0], [0, 4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2927 ⟨![[], [0, 4], [1], [2], [3], [0], [1, 5], [2, 5]], ![[5], [2], [3], [4], [1, 1, 1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2918 ⟨![[0], [1], [], [2], [0, 5], [1, 5], [], [2]], ![[0], [1], [3], [0, 0], [0, 0, 1, 5], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2925 ⟨![[], [1], [0, 0, 0], [2], [3], [1, 3, 4], [0], [2, 5]], ![[6], [1], [3], [4], [1, 1, 2, 2], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2922 ⟨![[0], [], [1, 1, 1], [2], [0, 1, 1], [1, 1, 5], [1], [2]], ![[0], [6], [3], [0, 0], [0, 4], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 2929 ⟨![[], [0, 0, 1, 0], [0, 0, 0], [2], [3], [0, 1, 5], [0], [2, 5]], ![[6], [1, 6], [3], [4], [1, 1, 1, 5], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2917 ⟨![[0], [1], [2], [], [0, 5], [1], [2], []], ![[0], [1], [2], [0, 0], [0, 1, 1, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2924 ⟨![[], [1], [2], [0, 0, 0], [3], [1, 3, 4], [2, 5], [0]], ![[7], [1], [2], [4], [1, 1, 3, 3], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2921 ⟨![[0], [], [2], [1, 1, 1], [0, 3, 4], [1, 1], [2, 5], [1]], ![[0], [7], [2], [0, 0], [0, 4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2928 ⟨![[], [0, 1, 4], [2], [0, 0, 0], [3], [0, 1], [2, 5], [0]], ![[7], [1, 7], [2], [4], [1, 1, 1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2919 ⟨![[0], [1], [], [2], [0, 5], [1, 5], [], [2]], ![[0], [1], [3], [0, 0], [0, 0, 1, 5], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2926 ⟨![[], [1], [0, 0, 0, 2], [0, 0, 0], [3], [1, 3, 4], [0, 2], [0]], ![[7], [1], [2, 7], [4], [1, 1, 2, 2], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2923 ⟨![[0], [], [1, 1, 2, 1], [1, 1, 1], [0, 3, 4], [1, 1], [1, 2], [1]], ![[0], [7], [2, 7], [0, 0], [0, 4], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 2930 ⟨![[], [0, 1, 4], [0, 0, 0, 2], [0, 0, 0], [3], [0, 1], [0, 2], [0]], ![[7], [1, 7], [2, 7], [4], [1, 1, 1, 5], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 297) : Classified H :=
  classify_of_checks 297 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node297

namespace Node298

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [4]],
   ![[0], [1], [0, 0], [0, 1, 1, 1, 0, 1], [2], [0, 0, 1, 1], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 297) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 298 :=
  generated_of_packed 297 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 2931 ⟨![[0], [], [1], [0, 2, 3, 5], [2, 4], [1, 5]], ![[0], [2], [0, 0], [0, 2, 3, 2], [0, 0, 4], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .edge 2932 ⟨![[], [0, 3], [1], [2], [0], [1, 5]], ![[4], [2], [3], [1, 1, 1, 4], [1, 3, 4], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .noncentric 928, .noncentric 64, .noncentric 64, .noncentric 928] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 298) : Classified H :=
  classify_of_checks 298 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node298

namespace Node299

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [3]],
   ![[0], [1], [0, 1, 0, 1], [2], [0, 1, 1, 0], [0, 1, 0, 1, 1, 1], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 298) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 299 :=
  generated_of_packed 298 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 2933 ⟨![[0], [], [1], [2, 4, 0], [2, 3], [1, 5]], ![[0], [2], [0, 0], [0, 0, 4], [3, 0], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .edge 2934 ⟨![[], [0, 4], [1], [2], [0], [1, 5]], ![[4], [2], [3], [1, 4, 3], [1, 1, 1, 4], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .noncentric 160, .noncentric 160, .noncentric 160, .noncentric 160] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 299) : Classified H :=
  classify_of_checks 299 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node299

end ReeTwo.SylowModel.SmallEvenMaximalLower
