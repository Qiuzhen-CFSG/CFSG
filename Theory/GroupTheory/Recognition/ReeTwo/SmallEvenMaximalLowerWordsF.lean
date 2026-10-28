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

namespace Node125

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0, 2, 2], [0, 2, 2, 0, 2, 2], [0, 1, 2, 1, 0, 2], [0, 1, 0, 1], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 124) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 125 :=
  generated_of_packed 124 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1388 ⟨![[], [0], [1], [3, 6], [0, 2, 3], [0, 0, 1, 3, 4]], ![[1], [2], [2, 2, 3], [1, 1, 1, 3, 1], [1, 2, 1, 3, 5], [1, 3, 4], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩, .core, .edge 1390 ⟨![[], [0, 2], [1], [3, 6], [0], [1, 1, 4, 1, 5]], ![[4], [2], [2, 2, 3], [1, 1, 1, 3, 1], [1, 1, 5, 2], [1, 1], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩, .edge 1386 ⟨![[0], [1], [], [0, 1, 3, 1, 4], [1, 2, 3], [0, 0, 2]], ![[0], [1], [0, 0, 5], [0, 5, 0, 5], [0, 1, 1, 3], [0, 1, 0, 1], [1, 1, 1, 4, 5], [1, 1, 1, 4, 5], [1, 1, 1, 4, 5], [1, 1, 1, 4, 5]]⟩, .edge 1389 ⟨![[], [1], [1, 0, 1, 4], [3, 6], [1, 2, 3], [0]], ![[5], [1], [2, 3, 5], [1, 1, 1, 3, 1], [1, 2, 2, 4], [1, 3, 4], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩, .edge 1387 ⟨![[0], [], [1, 3, 5], [2, 0, 3], [2, 5], [1]], ![[0], [5], [0, 3], [3, 3], [0, 5, 3, 5], [0, 3, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 1391 ⟨![[], [0, 2, 1], [0, 1, 1, 4], [3, 6], [0, 1, 6], [0]], ![[5], [1, 5], [2, 3, 5], [1, 1, 1, 3, 1], [1, 5, 1, 2], [1, 1], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 125) : Classified H :=
  classify_of_checks 125 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node125

namespace Node126

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 1, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 1, 0, 1, 1, 1], [0, 2, 2, 0, 2, 2], [0, 2, 0, 0, 0, 2], [0, 1, 0, 1], [0, 0, 0, 2, 2, 0, 2, 2], [0, 0, 0, 2, 2, 0, 2, 2], [0, 0, 0, 2, 2, 0, 2, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 125) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 126 :=
  generated_of_packed 125 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1394 ⟨![[], [0], [1], [3, 6], [0, 2, 3], [2, 1]], ![[1], [2], [2, 2, 5, 2], [1, 1, 1, 3, 1], [5, 2], [1, 3, 4], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩, .core, .edge 1396 ⟨![[], [0, 2], [1], [3, 6], [0], [2, 1]], ![[4], [2], [1, 1, 1, 4], [1, 1, 1, 3, 1], [5, 2], [1, 1], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩, .edge 1392 ⟨![[0], [1], [], [2, 0], [2, 1], [2, 4]], ![[0], [1], [0, 0, 3, 0], [3, 3], [0, 0, 0, 5, 3], [4, 1], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 1395 ⟨![[], [1], [2, 3, 0], [3, 6], [1, 2, 3], [0]], ![[5], [1], [1, 1, 1, 3, 4], [1, 1, 1, 3, 1], [2, 2, 3], [1, 3, 4], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩, .edge 1393 ⟨![[0], [], [1, 5], [2, 0, 3], [2, 5], [1]], ![[0], [5], [0, 3], [3, 3], [2, 2, 4], [0, 3, 4], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 1397 ⟨![[], [0, 2, 4, 1], [2, 3, 0], [3, 6], [0, 4, 1], [0]], ![[5], [1, 5], [1, 1, 1, 4], [1, 1, 1, 3, 1], [2, 2, 3], [1, 1], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 126) : Classified H :=
  classify_of_checks 126 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node126

namespace Node127

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [1, 0, 1, 0, 1, 1], [1, 0, 1, 0], [0, 0, 0, 0], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 126) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 127 :=
  generated_of_packed 126 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .edge 1398 ⟨![[], [0], [1], [0, 1, 2]], ![[1], [2], [1, 1, 1, 3, 2], [1, 3, 2], [2, 2], [1, 1, 3, 3], [1, 1, 3, 3], [1, 1, 3, 3], [1, 1, 3, 3], [1, 1, 3, 3]]⟩, .core, .edge 1399 ⟨![[], [0, 2, 4], [1], [0]], ![[3], [2], [1, 1, 1, 3], [1, 1], [2, 2], [1, 1, 3, 3], [1, 1, 3, 3], [1, 1, 3, 3], [1, 1, 3, 3], [1, 1, 3, 3]]⟩] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 2 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 127) : Classified H :=
  classify_of_checks 127 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node127

namespace Node128

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [0, 0, 1, 0, 1, 0, 1, 1], [1, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 127) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 128 :=
  generated_of_packed 127 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .edge 1400 ⟨![[], [0], [1], [0, 2, 4]], ![[1], [2], [3, 1, 3, 3], [1, 2, 3], [2, 2], [1, 1, 2, 2, 3, 3], [1, 1, 2, 2, 3, 3], [1, 1, 2, 2, 3, 3], [1, 1, 2, 2, 3, 3], [1, 1, 2, 2, 3, 3]]⟩, .core, .edge 1401 ⟨![[], [0, 1, 2], [1], [0]], ![[3], [2], [1, 1, 1, 2, 2, 2, 3], [1, 1, 2, 2], [2, 2], [1, 1, 2, 2, 3, 3], [1, 1, 2, 2, 3, 3], [1, 1, 2, 2, 3, 3], [1, 1, 2, 2, 3, 3], [1, 1, 2, 2, 3, 3]]⟩] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 2 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 128) : Classified H :=
  classify_of_checks 128 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node128

namespace Node129

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [3]],
   ![[0], [1], [0, 0, 0, 1, 0, 1], [2], [0, 0, 2, 2, 2], [2, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 128) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 129 :=
  generated_of_packed 128 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 1403 ⟨![[0], [], [1, 3], [2, 0], [], [1, 3]], ![[0], [0, 0, 2, 2, 2], [0, 0, 0, 3], [0, 0], [0, 0, 0, 2, 0, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1406 ⟨![[], [0, 0, 0], [1, 3], [3], [0], [1, 3, 4]], ![[4], [2, 2, 2, 3], [1, 1, 3], [3], [2, 2, 2, 5], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1402 ⟨![[0], [1], [], [0, 4], [1], [5]], ![[0], [1], [0, 0, 0, 1, 0, 1], [0, 0], [0, 0, 0, 3, 5], [5], [5], [5], [5], [5]]⟩, .edge 1405 ⟨![[], [1], [0, 4], [3], [1, 2], [0, 3]], ![[2, 3, 5, 5], [1], [1, 4], [3], [3, 5, 5], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .edge 1404 ⟨![[0], [], [1, 3], [2, 0], [], [1, 3]], ![[0], [0, 0, 2, 2, 2], [0, 0, 0, 3], [0, 0], [0, 0, 0, 2, 3, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1407 ⟨![[], [0, 2, 1, 3], [0, 4], [3], [0, 1], [0, 3]], ![[1, 2, 1, 3], [1, 1, 2, 1, 3], [1, 1, 3], [3], [3, 5, 5], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 129) : Classified H :=
  classify_of_checks 129 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node129

namespace Node130

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 1, 1, 1, 0, 1], [1, 0, 1, 0, 2, 2], [2, 2], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 129) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 130 :=
  generated_of_packed 129 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1410 ⟨![[], [0], [1], [], [0, 2], [1, 4]], ![[1], [2], [4, 1, 4, 4], [1, 2, 2, 4], [2, 2], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 1412 ⟨![[], [0, 2], [1], [], [0], [1, 4]], ![[4], [2], [4, 1, 4, 4], [1, 1, 2, 2], [2, 2], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1408 ⟨![[0], [1], [], [0, 4], [1, 4], [4]], ![[0], [1], [0, 1, 1, 1, 0, 1], [1, 0, 1, 3], [5], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩, .edge 1411 ⟨![[], [1], [0, 4], [], [1, 2], [0]], ![[5], [1], [4, 1, 4, 4], [1, 2, 1, 2], [2, 5], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1409 ⟨![[0], [], [1, 1, 1], [0, 2, 5], [1, 1], [1]], ![[0], [5], [0, 4, 3, 4], [0, 4, 3], [2, 5], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 1413 ⟨![[], [1, 0], [0, 4], [], [0, 1], [0]], ![[5], [1, 5], [4, 1, 4, 4], [1, 1, 2, 5], [2, 5], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 130) : Classified H :=
  classify_of_checks 130 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node130

namespace Node131

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 3, 0, 3], [2, 2], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 130) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 131 :=
  generated_of_packed 130 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1416 ⟨![[0], [], [1], [2], [0], [], [1, 4], [2]], ![[0], [2], [3], [0, 3, 0, 3], [2, 2], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩, .edge 1422 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 4], [2, 4, 5]], ![[5], [2], [3], [3, 4, 7], [2, 2], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1415 ⟨![[0], [1], [], [2], [0, 4], [1, 4], [4], [2]], ![[0], [1], [3], [0, 3, 0, 3], [6], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩, .edge 1420 ⟨![[], [1], [0, 0, 0, 4], [2], [0, 0], [1], [0], [2, 4, 5]], ![[6], [1], [3], [3, 4, 7], [2, 6], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1418 ⟨![[0], [], [1, 4], [2], [0], [], [1], [2]], ![[0], [6], [3], [0, 3, 0, 3], [2, 6], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩, .edge 1424 ⟨![[], [0, 0, 0, 1], [0, 0, 0, 4], [2], [0, 0], [0, 1], [0], [2, 4, 5]], ![[6], [1, 6], [3], [3, 4, 7], [2, 6], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1414 ⟨![[0], [1], [2], [], [0, 4, 5], [1], [2], [4]], ![[0], [1], [2], [0, 4, 7], [7], [0, 0, 0, 4, 7], [0, 0, 0, 4, 7], [0, 0, 0, 4, 7], [0, 0, 0, 4, 7], [0, 0, 0, 4, 7]]⟩, .edge 1419 ⟨![[], [1], [2], [0, 3, 4], [3, 5], [1], [2, 4], [0]], ![[7], [1], [2], [3, 3], [2, 2], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1417 ⟨![[0], [], [2], [1], [0], [], [2, 4], [1]], ![[0], [3], [2], [0, 3, 0, 3], [2, 2], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩, .edge 1423 ⟨![[], [1, 0, 3], [2], [0, 3, 4], [3, 5], [0, 1, 4], [2, 4], [0]], ![[7], [1, 7], [2], [3, 3], [2, 2], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .noncentric 24, .edge 1421 ⟨![[], [1], [2, 0, 3], [0, 3, 4], [3, 5], [1], [0, 2, 4], [0]], ![[7], [1], [2, 7], [3, 3], [2, 6], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .noncentric 56, .edge 1425 ⟨![[], [1, 0, 3], [2, 0, 3], [0, 3, 4], [3, 5], [0, 1, 4], [0, 2, 4], [0]], ![[7], [1, 7], [2, 7], [3, 3], [2, 6], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 131) : Classified H :=
  classify_of_checks 131 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node131

namespace Node132

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 1, 1, 1, 0, 1, 2], [1, 0, 1, 0], [2, 2], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 131) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 132 :=
  generated_of_packed 131 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1426 ⟨![[], [0], [1, 2], [], [0, 2], [1, 2, 4]], ![[1], [1, 1, 1, 2, 4], [1, 1, 1, 4], [1, 4], [2, 2], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 1427 ⟨![[], [0, 2], [1, 2], [], [0], [1, 2, 4]], ![[4], [1, 1, 1, 4, 2], [1, 1, 1, 4], [1, 1], [2, 2], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .noncentric 64, .noncentric 288, .noncentric 32, .noncentric 320] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 132) : Classified H :=
  classify_of_checks 132 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node132

namespace Node133

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [1, 1], [0, 1, 0, 1], [0, 0, 0, 0], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 132) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 133 :=
  generated_of_packed 132 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .edge 1428 ⟨![[], [0], [1], [2, 3, 0, 1]], ![[1], [2], [1, 1], [3, 2, 1], [2, 2], [1, 1, 2, 3, 2, 3], [1, 1, 2, 3, 2, 3], [1, 1, 2, 3, 2, 3], [1, 1, 2, 3, 2, 3], [1, 1, 2, 3, 2, 3]]⟩, .core, .edge 1429 ⟨![[], [2, 0, 3], [1], [0]], ![[3], [2], [1, 3], [1, 1], [2, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2]]⟩] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 2 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 133) : Classified H :=
  classify_of_checks 133 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node133

namespace Node134

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 1, 0, 1], [0, 0, 0, 1, 0, 1, 2, 2], [2, 2], [1, 2, 1, 2, 2, 2], [1, 2, 1, 2, 2, 2], [1, 2, 1, 2, 2, 2], [1, 2, 1, 2, 2, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 133) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 134 :=
  generated_of_packed 133 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 1431 ⟨![[0], [], [1], [0, 3], [], [1, 5]], ![[0], [2], [0, 3], [0, 0, 0, 2, 2, 3], [2, 2], [2, 2, 2, 5], [2, 2, 2, 5], [2, 2, 2, 5], [2, 2, 2, 5], [2, 2, 2, 5]]⟩, .edge 1434 ⟨![[], [0, 2, 4], [1], [2, 3], [0], [1, 4]], ![[4], [2], [4, 4], [1, 1, 3], [2, 2], [1, 2, 4, 2], [1, 2, 4, 2], [1, 2, 4, 2], [1, 2, 4, 2], [1, 2, 4, 2]]⟩, .edge 1430 ⟨![[0], [1], [], [0, 4], [1, 5], [4]], ![[0], [1], [0, 1, 0, 1], [0, 0, 0, 1, 3, 1], [5], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4]]⟩, .edge 1433 ⟨![[], [1], [0, 0, 0], [0, 0], [1, 3, 5], [0]], ![[5], [1], [1, 3, 4], [1, 2, 2, 4, 3], [2, 5], [1, 2, 2, 1, 3], [1, 2, 2, 1, 3], [1, 2, 2, 1, 3], [1, 2, 2, 1, 3], [1, 2, 2, 1, 3]]⟩, .edge 1432 ⟨![[0], [], [1, 5], [0, 3], [], [1]], ![[0], [5], [0, 3], [0, 0, 0, 2, 5, 3], [2, 5], [2, 2, 2, 5], [2, 2, 2, 5], [2, 2, 2, 5], [2, 2, 2, 5], [2, 2, 2, 5]]⟩, .edge 1435 ⟨![[], [0, 2, 1], [0, 0, 0], [0, 0], [1, 0, 3], [0]], ![[5], [1, 5], [4, 4], [1, 1, 3], [2, 5], [1, 2, 2, 4, 3], [1, 2, 2, 4, 3], [1, 2, 2, 4, 3], [1, 2, 2, 4, 3], [1, 2, 2, 4, 3]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 134) : Classified H :=
  classify_of_checks 134 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node134

namespace Node135

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 1, 0, 1], [2, 2], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 134) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 135 :=
  generated_of_packed 134 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1439 ⟨![[0], [], [1], [2], [0, 5], [], [1, 5], [2, 5]], ![[0], [2], [3], [0, 4], [2, 2], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1446 ⟨![[], [0, 3], [1], [2], [3, 5], [0], [1, 4], [2, 4, 5]], ![[5], [2], [3], [1, 1], [2, 2], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1437 ⟨![[0], [1], [], [2], [0, 4], [1, 5], [4], [2]], ![[0], [1], [3], [0, 0, 1, 5], [6], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1444 ⟨![[], [1], [0, 0, 0, 4], [2], [0, 0], [1, 5], [0], [2, 4, 5]], ![[6], [1], [3], [1, 4, 5], [2, 6], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1441 ⟨![[0], [], [1, 5], [2], [0, 5], [], [1], [2, 5]], ![[0], [6], [3], [0, 4], [2, 6], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1448 ⟨![[], [0, 0, 1, 0], [0, 0, 0, 4], [2], [0, 0], [1, 0, 5], [0], [1, 1, 2]], ![[6], [1, 6], [3], [1, 1], [2, 6], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1436 ⟨![[0], [1], [2], [], [0, 4, 5], [1, 5], [2], [4]], ![[0], [1], [2], [0, 4, 7], [7], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1443 ⟨![[], [1], [2], [0, 3, 4], [3, 5], [1, 5], [2, 4], [0]], ![[7], [1], [2], [3, 3], [2, 2], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1440 ⟨![[0], [], [2], [1, 5], [0, 5], [], [2, 5], [1]], ![[0], [7], [2], [0, 4], [2, 2], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1447 ⟨![[], [1, 0, 3], [2], [0, 3, 4], [3, 5], [1, 0], [2, 4], [0]], ![[7], [1, 7], [2], [1, 1], [2, 2], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 1438 ⟨![[0], [1], [], [2, 4], [0, 4], [1, 5], [4], [2]], ![[0], [1], [7], [0, 0, 1, 5], [6], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1445 ⟨![[], [1], [2, 0, 3], [0, 3, 4], [3, 5], [1, 5], [0, 2, 4], [0]], ![[7], [1], [2, 7], [3, 3], [2, 6], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1442 ⟨![[0], [], [1, 1, 1, 2], [1, 5], [0, 5], [], [1, 2, 4], [1]], ![[0], [7], [2, 7], [0, 4], [2, 6], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1449 ⟨![[], [1, 0, 3], [2, 0, 3], [0, 3, 4], [3, 5], [1, 0], [0, 2, 4], [0]], ![[7], [1, 7], [2, 7], [1, 1], [2, 6], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 135) : Classified H :=
  classify_of_checks 135 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node135

namespace Node136

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [3]],
   ![[0], [1], [0, 0], [2], [0, 1, 1, 0, 2], [2, 2], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 135) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 136 :=
  generated_of_packed 135 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1452 ⟨![[], [0], [0, 1, 0, 2], [2], [3, 0], [1, 3, 5]], ![[1], [1, 3, 1, 5], [3], [4, 3, 4], [2, 2], [1, 4, 3], [1, 4, 3], [1, 4, 3], [1, 4, 3], [1, 4, 3]]⟩, .core, .edge 1454 ⟨![[], [3, 0, 2], [0, 1, 3, 0], [2], [0], [1, 3, 5]], ![[4], [1, 2, 3, 4], [3], [4, 3, 1], [1, 1], [4, 4], [4, 4], [4, 4], [4, 4], [4, 4]]⟩, .edge 1450 ⟨![[0], [1], [], [0, 4], [1], [4]], ![[0], [1], [0, 0], [0, 3, 1, 1], [5], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 1453 ⟨![[], [1], [1, 1, 0], [2], [3, 1], [3, 0]], ![[1, 1, 2], [1], [3], [4, 3, 4], [2, 5], [1, 4, 3], [1, 4, 3], [1, 4, 3], [1, 4, 3], [1, 4, 3]]⟩, .edge 1451 ⟨![[0], [], [2, 1], [0, 3, 5], [2, 3], [3, 1, 4]], ![[0], [0, 2, 3], [0, 0], [3, 4, 3], [2, 5], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4]]⟩, .edge 1455 ⟨![[], [2, 1, 0, 4], [2, 3, 0], [2], [0, 1, 5], [3, 0]], ![[1, 4, 2], [2, 3, 1], [3], [4, 3, 1], [1, 1], [4, 4], [4, 4], [4, 4], [4, 4], [4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 136) : Classified H :=
  classify_of_checks 136 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node136

namespace Node137

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 1, 0, 0, 0, 1], [0, 1, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 136) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 137 :=
  generated_of_packed 136 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .core, .edge 1456 ⟨![[0], [], [1, 0, 3], [3, 5]], ![[0], [0, 0, 0, 3, 2], [0, 3, 0], [0, 2, 0, 3, 2], [0, 0, 0, 0], [0, 2, 0, 3, 2, 3], [0, 2, 0, 3, 2, 3], [0, 2, 0, 3, 2, 3], [0, 2, 0, 3, 2, 3], [0, 2, 0, 3, 2, 3]]⟩, .edge 1457 ⟨![[], [0, 0, 0, 3], [2, 3], [0]], ![[3], [1, 1, 2], [1, 2, 3], [3, 1], [2, 2], [1, 1, 3, 3], [1, 1, 3, 3], [1, 1, 3, 3], [1, 1, 3, 3], [1, 1, 3, 3]]⟩] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 2 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 137) : Classified H :=
  classify_of_checks 137 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node137

namespace Node138

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 3, 0, 1, 1], [2, 2], [0, 0], [0, 0], [0, 0], [0, 0]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 137) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 138 :=
  generated_of_packed 137 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 1464 ⟨![[], [0], [1], [0, 0, 2], [4], [0, 3], [1, 4, 5], [2, 3, 5]], ![[1], [2], [1, 7, 1], [1, 1, 4], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .core, .edge 1468 ⟨![[], [0, 3, 4], [1], [2, 3, 4], [4], [0], [0, 1, 0], [2, 3, 5]], ![[5], [2], [1, 3, 5], [1, 4, 5], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1459 ⟨![[0], [1], [], [1, 1, 2], [0, 4, 5], [1, 5], [5], [1, 1, 2]], ![[0], [1], [1, 5, 3], [0, 0, 1, 1], [0, 0], [6], [6], [6], [6], [6]]⟩, .edge 1466 ⟨![[], [1], [0, 5], [1, 1, 2], [4], [1, 3], [0], [2, 3, 5]], ![[6], [1], [1, 7, 1], [1, 1, 4], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1462 ⟨![[0], [], [1, 1, 1], [1, 1, 2], [0, 3], [1, 1], [1], [2, 3]], ![[0], [6], [0, 7, 4], [0, 0, 5], [0, 0], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1470 ⟨![[], [1, 0], [0, 5], [1, 1, 2], [4], [0, 1], [0], [2, 3, 5]], ![[6], [1, 6], [1, 3, 5], [1, 4, 5], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1458 ⟨![[0], [1], [2], [], [0, 4, 5], [1, 4], [2], [5]], ![[0], [1], [2], [1, 5], [0, 0], [7], [7], [7], [7], [7]]⟩, .edge 1465 ⟨![[], [1], [2], [1, 1, 0], [4], [1, 3], [0, 2, 0], [0, 1, 1]], ![[1, 1, 7], [1], [2], [1, 1, 4], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1461 ⟨![[0], [], [2], [1, 4], [0, 3], [3, 4], [2, 5], [1, 3, 4]], ![[0], [0, 0, 3], [2], [3, 3], [0, 0], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1469 ⟨![[], [1, 0], [2], [3, 0, 4], [4], [0, 1, 4], [0, 2, 0], [0, 3, 4]], ![[1, 5, 7], [5, 3], [2], [1, 4, 5], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1460 ⟨![[0], [1], [], [0, 2, 0, 3], [0, 4, 5], [1, 5], [5], [1, 1, 2]], ![[0], [1], [1, 1, 3], [0, 0, 1, 1], [0, 0], [6], [6], [6], [6], [6]]⟩, .edge 1467 ⟨![[], [1], [2, 0], [1, 1, 0], [4], [1, 3], [0, 2], [0, 1, 1]], ![[1, 1, 7], [1], [1, 1, 2, 3], [1, 1, 4], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1463 ⟨![[0], [], [0, 2, 1, 0], [1, 4], [0, 3], [3, 4], [1, 2], [1, 3, 4]], ![[0], [0, 0, 3], [6, 7], [3, 3], [0, 0], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1471 ⟨![[], [1, 0], [2, 0], [3, 0, 4], [4], [0, 1, 4], [0, 2], [0, 3, 4]], ![[1, 5, 7], [5, 3], [1, 2, 1, 3], [1, 4, 5], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 138) : Classified H :=
  classify_of_checks 138 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node138

namespace Node139

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 3, 0, 3], [2, 2], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 138) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 139 :=
  generated_of_packed 138 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1475 ⟨![[0], [], [1], [2], [0, 5], [0, 0], [1, 4, 5], [2, 5]], ![[0], [2], [3], [0, 4], [2, 2], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1482 ⟨![[], [0, 3], [1], [2], [3, 5], [0], [1, 4], [0, 2, 0]], ![[5], [2], [3], [1, 1, 4], [2, 2], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1473 ⟨![[0], [1], [], [2], [0, 4], [1, 4, 5], [4], [2]], ![[0], [1], [3], [1, 5, 6], [6], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 1480 ⟨![[], [1], [1, 0, 1], [2], [0, 0], [1, 5], [0], [2, 4, 5]], ![[6], [1], [3], [1, 5], [2, 6], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1477 ⟨![[0], [], [0, 1, 0], [2], [0, 5], [0, 0], [1], [2, 5]], ![[0], [6], [3], [0, 4], [2, 6], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 1484 ⟨![[], [0, 0, 0, 1], [0, 0, 0, 4], [2], [0, 0], [0, 1, 5], [0], [2, 4, 5]], ![[6], [1, 6], [3], [1, 1, 4], [2, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1472 ⟨![[0], [1], [2], [], [0, 4, 5], [1, 5], [2], [4]], ![[0], [1], [2], [1, 5], [7], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5]]⟩, .edge 1479 ⟨![[], [1], [2], [0, 3, 4], [1, 1], [1, 5], [2, 4], [0]], ![[7], [1], [2], [1, 5], [2, 2], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 1476 ⟨![[0], [], [2], [1, 3], [0, 5], [0, 0], [2, 4, 5], [1]], ![[0], [7], [2], [0, 4], [2, 2], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1483 ⟨![[], [1, 0, 3], [2], [0, 1, 1], [3, 5], [1, 0], [2, 4], [0]], ![[7], [1, 7], [2], [3, 3], [2, 2], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1474 ⟨![[0], [1], [], [2, 4], [0, 4], [1, 4, 5], [4], [2]], ![[0], [1], [7], [1, 5, 6], [6], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 1481 ⟨![[], [1], [2, 0, 3], [0, 3, 4], [1, 1], [1, 5], [0, 2, 4], [0]], ![[7], [1], [2, 7], [1, 5], [2, 6], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 1478 ⟨![[0], [], [1, 2, 3], [1, 3], [0, 5], [0, 0], [2, 1], [1]], ![[0], [7], [2, 7], [0, 4], [2, 6], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 1485 ⟨![[], [1, 0, 3], [2, 0, 3], [0, 1, 1], [3, 5], [1, 0], [0, 2, 4], [0]], ![[7], [1, 7], [2, 7], [3, 3], [2, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 139) : Classified H :=
  classify_of_checks 139 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node139

namespace Node140

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0], [2, 2], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 139) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 140 :=
  generated_of_packed 139 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1489 ⟨![[0], [], [1], [2], [0, 3, 5], [], [1, 4], [2]], ![[0], [2], [3], [0, 0], [2, 2], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 1496 ⟨![[], [0, 5], [1], [2], [3], [0], [1, 4, 5], [2, 4]], ![[5], [2], [3], [4], [2, 2], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1487 ⟨![[0], [1], [], [2], [0, 4, 5], [1, 4], [4], [2]], ![[0], [1], [3], [0, 0], [6], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 1494 ⟨![[], [1], [1, 0, 1], [2], [3], [0, 0, 1], [0], [2, 4]], ![[6], [1], [3], [4], [2, 6], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 1491 ⟨![[0], [], [1, 4], [2], [0, 3, 5], [], [1], [2]], ![[0], [6], [3], [0, 0], [2, 6], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 1498 ⟨![[], [0, 1, 5], [0, 0, 0, 4], [2], [3], [0, 1], [0], [2, 4]], ![[6], [1, 6], [3], [4], [2, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1486 ⟨![[0], [1], [2], [], [0, 4], [1], [2], [4]], ![[0], [1], [2], [0, 0], [7], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 1493 ⟨![[], [1], [2], [0, 3, 4], [3], [1, 3, 5], [2, 4, 5], [0]], ![[7], [1], [2], [4], [2, 2], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1490 ⟨![[0], [], [2], [1], [0, 3, 5], [], [2, 4], [1]], ![[0], [3], [2], [0, 0], [2, 2], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 1497 ⟨![[], [1, 0, 3], [2], [0, 3, 4], [3], [0, 1, 4], [2, 4, 5], [0]], ![[7], [1, 7], [2], [4], [2, 2], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1488 ⟨![[0], [1], [], [2, 4], [0, 4, 5], [1, 4], [4], [2]], ![[0], [1], [7], [0, 0], [6], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 1495 ⟨![[], [1], [2, 0, 3], [0, 3, 4], [3], [1, 3, 5], [0, 2, 4], [0]], ![[7], [1], [2, 7], [4], [2, 6], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 1492 ⟨![[0], [], [1, 2], [1], [0, 3, 5], [], [2, 1], [1]], ![[0], [3], [2, 3], [0, 0], [2, 6], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 1499 ⟨![[], [1, 0, 3], [2, 0, 3], [0, 3, 4], [3], [0, 1, 4], [0, 2, 4], [0]], ![[7], [1, 7], [2, 7], [4], [2, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 140) : Classified H :=
  classify_of_checks 140 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node140

namespace Node141

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 1, 0, 1, 1, 2, 1], [1, 0, 1, 0], [2, 2], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 140) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 141 :=
  generated_of_packed 140 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1500 ⟨![[], [0], [1, 2], [], [0, 2], [1, 2, 4]], ![[1], [1, 1, 1, 4, 2], [1, 1, 1, 4], [1, 4], [2, 2], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 1501 ⟨![[], [0, 2], [1, 2], [], [0], [1, 2, 4]], ![[4], [1, 1, 1, 4, 2], [1, 1, 1, 4], [1, 1], [2, 2], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .noncentric 64, .noncentric 288, .noncentric 32, .noncentric 320] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 141) : Classified H :=
  classify_of_checks 141 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node141

namespace Node142

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 2, 2, 2, 3], [2, 2], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 141) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 142 :=
  generated_of_packed 141 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1505 ⟨![[0], [], [1, 2, 3], [1], [0, 5], [], [0, 1, 0, 2], [1, 5]], ![[0], [3], [0, 0, 2, 2, 2, 3], [0, 0], [2, 2], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1512 ⟨![[], [0, 0, 0], [1, 2, 3], [1], [3], [0], [1, 2, 3], [1, 5]], ![[5], [3], [2, 2, 2, 3, 4], [4], [2, 2], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 1502 ⟨![[0], [1], [], [2], [0], [1, 5], [4], [2]], ![[0], [1], [3], [0, 0], [6], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1509 ⟨![[], [1], [0, 2], [2], [3], [1, 5], [0, 2, 3], [2, 5]], ![[2, 2, 6, 3], [1], [3], [4], [2, 6], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1506 ⟨![[0], [], [2, 1, 3], [2], [0, 5], [], [1, 2, 3], [2, 5]], ![[0], [0, 0, 2, 2, 2, 3], [3], [0, 0], [2, 6], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1513 ⟨![[], [0, 0, 0, 1], [0, 2], [2], [3], [0, 1], [0, 2, 3], [2, 5]], ![[2, 2, 6, 3], [1, 2, 2, 6, 3], [3], [4], [2, 6], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 1504 ⟨![[0], [1], [2, 3], [], [0, 5], [1, 5], [2, 3], [4]], ![[0], [1], [0, 0, 2], [0, 0], [7], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1511 ⟨![[], [1], [2, 3], [0, 0, 0, 2], [3], [1, 5], [2, 3], [0, 2]], ![[2, 2, 2, 4, 7], [1], [2, 4], [4], [2, 2], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1508 ⟨![[0], [], [2, 3], [2, 1], [0, 5], [], [2, 3, 5], [1, 2]], ![[0], [0, 0, 2, 2, 2, 3], [0, 0, 2], [0, 0], [2, 2], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1515 ⟨![[], [0, 0, 0, 1], [2, 3], [0, 0, 0, 2], [3], [0, 1], [2, 3], [0, 2]], ![[2, 2, 2, 4, 7], [2, 1, 2, 2, 3], [2, 4], [4], [2, 2], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 1503 ⟨![[0], [1], [], [2, 3], [0], [1, 5], [4], [2, 3, 4]], ![[0], [1], [0, 0, 3], [0, 0], [6], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1510 ⟨![[], [1], [0, 2], [0, 3, 5], [3], [1, 5], [0, 2, 3], [0]], ![[7], [1], [2, 2, 2, 7], [4], [2, 6], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1507 ⟨![[0], [], [0, 1, 2, 0], [1, 5], [0, 5], [], [1, 2, 3], [1]], ![[0], [7], [0, 0, 2, 2, 2, 3], [0, 0], [2, 6], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1514 ⟨![[], [0, 0, 1, 0], [0, 2], [0, 3, 5], [3], [1, 0, 4], [0, 2, 3], [0]], ![[7], [1, 7], [2, 2, 2, 7], [4], [2, 6], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 142) : Classified H :=
  classify_of_checks 142 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node142

namespace Node143

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 3, 0, 3], [2, 2], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 142) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 143 :=
  generated_of_packed 142 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1518 ⟨![[0], [], [1], [2], [0, 3], [], [1, 5], [2, 5]], ![[0], [2], [3], [0, 0, 0, 4], [2, 2], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 1524 ⟨![[], [0, 5], [1], [2], [3, 5], [0], [1], [0, 2, 0]], ![[5], [2], [3], [1, 1, 4], [2, 2], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1517 ⟨![[0], [1], [], [2], [0], [1, 5], [4], [2]], ![[0], [1], [3], [0, 0, 1, 5], [6], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1523 ⟨![[], [1], [0, 3, 5], [2], [3, 5], [1, 3], [0], [2, 4, 5]], ![[6], [1], [3], [1, 5], [2, 6], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1520 ⟨![[0], [], [1, 5], [2], [0, 3], [], [1], [2, 5]], ![[0], [6], [3], [0, 0, 0, 4], [2, 6], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 1526 ⟨![[], [0, 1, 4], [0, 3, 5], [2], [3, 5], [0, 1, 1, 1], [0], [1, 1, 2]], ![[6], [1, 6], [3], [1, 1, 4], [2, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1516 ⟨![[0], [1], [2], [], [0, 4, 5], [1, 5], [2], [4]], ![[0], [1], [2], [0, 4, 7], [7], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1522 ⟨![[], [1], [2], [0, 3, 4], [3, 5], [1, 3], [2], [0]], ![[7], [1], [2], [1, 5], [2, 2], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 1519 ⟨![[0], [], [2], [1, 5], [0, 3], [], [2, 5], [1]], ![[0], [7], [2], [0, 0, 0, 4], [2, 2], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 1525 ⟨![[], [0, 1, 4], [2], [0, 3, 4], [3, 5], [0, 1, 1, 1], [2], [0]], ![[7], [1, 7], [2], [3, 3], [2, 2], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .noncentric 100, .noncentric 68, .edge 1521 ⟨![[0], [], [1, 1, 1, 2], [1, 5], [0, 3], [], [1, 2, 4], [1]], ![[0], [7], [2, 7], [0, 0, 0, 4], [2, 6], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 1527 ⟨![[], [0, 1, 4], [2, 0, 3], [0, 3, 4], [3, 5], [0, 1, 1, 1], [0, 2, 4], [0]], ![[7], [1, 7], [2, 7], [3, 3], [2, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 143) : Classified H :=
  classify_of_checks 143 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node143

namespace Node144

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0], [2, 2], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 143) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 144 :=
  generated_of_packed 143 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1531 ⟨![[0], [], [1], [2], [0, 3], [3, 5], [1, 4, 5], [2, 5]], ![[0], [2], [3], [0, 0], [2, 2], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1538 ⟨![[], [0], [1], [2], [3], [0], [1, 4, 5], [2, 4]], ![[1], [2], [3], [4], [2, 2], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1529 ⟨![[0], [1], [], [2], [0, 4, 5], [1, 4, 5], [4], [2]], ![[0], [1], [3], [0, 0], [6], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩, .edge 1536 ⟨![[], [1], [0, 0, 0, 4], [2], [3], [1, 3], [0], [2, 4]], ![[6], [1], [3], [4], [2, 6], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1533 ⟨![[0], [], [1, 3, 4], [2], [0, 3], [3, 5], [1], [2, 5]], ![[0], [6], [3], [0, 0], [2, 6], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 1540 ⟨![[], [0, 1, 5], [0, 0, 0, 4], [2], [3], [0, 1, 5], [0], [2, 4]], ![[6], [1, 6], [3], [4], [2, 6], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 1528 ⟨![[0], [1], [2], [], [0, 4], [1, 5], [2], [4]], ![[0], [1], [2], [0, 0], [7], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩, .edge 1535 ⟨![[], [1], [2], [0, 3, 4], [3], [1, 3], [2, 4, 5], [0]], ![[7], [1], [2], [4], [2, 2], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1532 ⟨![[0], [], [2], [1, 3], [0, 3], [3, 5], [2, 4, 5], [1]], ![[0], [7], [2], [0, 0], [2, 2], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1539 ⟨![[], [1, 0, 3], [2], [0, 1, 1], [3], [1, 0, 3], [2, 4, 5], [0]], ![[7], [1, 7], [2], [4], [2, 2], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1530 ⟨![[0], [1], [], [2, 4], [0, 4, 5], [1, 4, 5], [4], [2]], ![[0], [1], [7], [0, 0], [6], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩, .edge 1537 ⟨![[], [1], [2, 0, 3], [0, 3, 4], [3], [1, 3], [0, 2, 4], [0]], ![[7], [1], [2, 7], [4], [2, 6], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1534 ⟨![[0], [], [1, 2, 3], [1, 3], [0, 3], [3, 5], [2, 1], [1]], ![[0], [7], [2, 7], [0, 0], [2, 6], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 1541 ⟨![[], [1, 0, 3], [2, 0, 3], [0, 1, 1], [3], [1, 0, 3], [0, 2, 4], [0]], ![[7], [1, 7], [2, 7], [4], [2, 6], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 144) : Classified H :=
  classify_of_checks 144 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node144

namespace Node145

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [1, 2, 1, 2], [0, 1, 1, 0, 2, 1, 2, 1], [1, 1, 1, 1], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 144) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 145 :=
  generated_of_packed 144 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1544 ⟨![[], [0], [1], [], [0, 2], [1, 5]], ![[1], [2], [1, 2, 1, 2], [1, 1, 1, 1, 1, 4], [1, 1, 1, 1], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .core, .edge 1546 ⟨![[], [0, 2], [1], [], [0], [1, 5]], ![[4], [2], [1, 2, 4, 5], [1, 1, 1, 2, 1, 2], [1, 2, 1, 2], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .edge 1542 ⟨![[0], [1], [], [0, 5], [1, 3], []], ![[0], [1], [1, 4], [0, 1, 1, 0, 4, 1], [0, 1, 3, 4], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3]]⟩, .edge 1545 ⟨![[], [1], [0, 5], [], [1, 2], [0]], ![[5], [1], [1, 2, 4, 5], [1, 1, 1, 1, 1, 4], [1, 1, 1, 1], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1543 ⟨![[0], [], [1, 2, 4], [0, 2, 5], [2, 3], [1]], ![[0], [5], [5, 5], [0, 4, 3], [4, 4], [0, 2, 3, 5], [0, 2, 3, 5], [0, 2, 3, 5], [0, 2, 3, 5], [0, 2, 3, 5]]⟩, .edge 1547 ⟨![[], [1, 0, 5], [0, 5], [], [0, 1, 3], [0]], ![[5], [1, 5], [1, 2, 1, 2], [1, 1, 1, 2, 4, 5], [1, 2, 4, 5], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 145) : Classified H :=
  classify_of_checks 145 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node145

namespace Node146

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [2, 1, 2, 1], [0, 1, 0, 1, 2, 2], [1, 1, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 145) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 146 :=
  generated_of_packed 145 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1550 ⟨![[], [0], [1], [], [0, 2], [1, 1, 1]], ![[1], [2], [2, 1, 2, 1], [2, 2, 4, 1], [1, 1, 1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 1552 ⟨![[], [0, 2], [1], [], [0], [1, 1, 1]], ![[4], [2], [2, 1, 5, 4], [2, 2, 4, 4], [1, 2, 1, 5], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1548 ⟨![[0], [1], [], [0, 4, 5], [1, 3, 4], [4, 5]], ![[0], [1], [4, 1, 5], [0, 1, 3, 1], [0, 1, 3, 4], [0, 1, 0, 4], [0, 1, 0, 4], [0, 1, 0, 4], [0, 1, 0, 4], [0, 1, 0, 4]]⟩, .edge 1551 ⟨![[], [1], [0, 4, 5], [], [1, 2], [0]], ![[5], [1], [2, 4, 5, 1], [2, 1, 4, 5], [1, 1, 1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1549 ⟨![[0], [], [1, 2], [0, 1, 1], [2, 3], [1]], ![[0], [5], [0, 2, 3, 2], [0, 4, 3], [4, 4], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1553 ⟨![[], [1, 0], [0, 4, 5], [], [0, 3, 1], [0]], ![[5], [1, 5], [2, 4, 2, 4], [2, 1, 1, 5], [1, 2, 4, 2], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 146) : Classified H :=
  classify_of_checks 146 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node146

namespace Node147

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [2, 1, 2, 1], [1, 0, 1, 0], [1, 1, 1, 1], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 146) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 147 :=
  generated_of_packed 146 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1556 ⟨![[], [0], [1], [], [0, 2, 4], [1, 5]], ![[1], [2], [1, 1, 1, 4], [1, 4], [1, 1, 1, 1], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .core, .edge 1558 ⟨![[], [0, 2, 4], [1], [], [0], [1, 5]], ![[4], [2], [1, 1, 1, 4], [1, 1], [1, 4, 1, 4], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .edge 1554 ⟨![[0], [1], [], [0, 5], [3, 1], []], ![[0], [1], [4, 1], [0, 1, 3, 1], [1, 1, 1, 1], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3]]⟩, .edge 1557 ⟨![[], [1], [0, 5], [], [1, 2, 4], [0]], ![[5], [1], [1, 1, 1, 4], [1, 4], [1, 1, 1, 1], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1555 ⟨![[0], [], [0, 1, 0, 5], [1, 1, 0], [2, 3], [1]], ![[0], [5], [0, 2, 0, 5], [2, 4, 2], [4, 4], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1559 ⟨![[], [1, 0, 5], [0, 5], [], [0, 3, 1], [0]], ![[5], [1, 5], [1, 1, 1, 4], [1, 1], [1, 4, 1, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 147) : Classified H :=
  classify_of_checks 147 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node147

namespace Node148

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [1, 2, 1, 2], [1, 0, 1, 0], [1, 1, 1, 1], [0, 1, 0, 2, 1, 2], [0, 1, 0, 2, 1, 2], [0, 1, 0, 2, 1, 2], [0, 1, 0, 2, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 147) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 148 :=
  generated_of_packed 147 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1562 ⟨![[], [0], [1], [], [0, 2, 4], [1, 1, 1]], ![[1], [2], [1, 1, 1, 4], [1, 4], [1, 1, 1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 1564 ⟨![[], [0, 2, 4], [1], [], [0], [1, 1, 1]], ![[4], [2], [1, 1, 1, 4], [1, 1], [1, 2, 1, 2], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1560 ⟨![[0], [1], [], [0, 4, 5], [3, 1, 4], [4, 5]], ![[0], [1], [1, 4, 5], [1, 0, 1, 0], [0, 1, 0, 4], [0, 1, 3, 4], [0, 1, 3, 4], [0, 1, 3, 4], [0, 1, 3, 4], [0, 1, 3, 4]]⟩, .edge 1563 ⟨![[], [1], [0, 4, 5], [], [1, 2, 4], [0]], ![[5], [1], [1, 1, 1, 4], [1, 4], [1, 1, 1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1561 ⟨![[0], [], [1, 2, 5], [2, 0, 5], [2, 3], [1]], ![[0], [5], [5, 5], [2, 2, 4], [4, 4], [0, 2, 2, 3], [0, 2, 2, 3], [0, 2, 2, 3], [0, 2, 2, 3], [0, 2, 2, 3]]⟩, .edge 1565 ⟨![[], [1, 0], [0, 4, 5], [], [0, 1, 3], [0]], ![[5], [1, 5], [1, 1, 1, 4], [1, 1], [1, 2, 4, 5], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 148) : Classified H :=
  classify_of_checks 148 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node148

namespace Node149

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 2, 0, 2], [3, 3], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 148) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 149 :=
  generated_of_packed 148 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1567 ⟨![[0], [], [1], [2], [0], [], [0, 0, 1], [2, 4]], ![[0], [2], [3], [0, 2, 0, 2], [3, 3], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1574 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 5], [2, 4]], ![[5], [2], [3], [2, 4, 6], [3, 3], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1566 ⟨![[0], [1], [], [2], [0, 5], [0, 0, 1], [], [2, 5]], ![[0], [1], [3], [0, 4], [3, 3], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1572 ⟨![[], [1], [0, 3], [2], [3, 5], [1], [0], [2, 4]], ![[6], [1], [3], [2, 2], [3, 3], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 1569 ⟨![[0], [], [0, 0, 1], [2], [0], [], [1], [2, 4]], ![[0], [6], [3], [0, 2, 0, 6], [3, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1576 ⟨![[], [0, 1], [0, 3], [2], [1, 1], [1, 0, 5], [0], [2, 4]], ![[6], [1, 6], [3], [2, 2], [3, 3], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .noncentric 16, .edge 1571 ⟨![[], [1], [2], [0, 0, 0, 4], [0, 0], [1], [2, 5], [0]], ![[7], [1], [2], [2, 4, 6], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1568 ⟨![[0], [], [2], [1, 4], [0], [], [0, 0, 2], [1]], ![[0], [7], [2], [0, 2, 0, 2], [3, 7], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1575 ⟨![[], [0, 0, 0, 1], [2], [0, 0, 0, 4], [0, 0], [0, 1], [2, 5], [0]], ![[7], [1, 7], [2], [2, 4, 6], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 2072, .edge 1573 ⟨![[], [1], [0, 0, 2, 0], [0, 0, 0, 4], [0, 0], [1], [2, 0, 5], [0]], ![[7], [1], [2, 7], [2, 2], [3, 7], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 1570 ⟨![[0], [], [2, 1], [1, 4], [0], [], [0, 0, 2, 1], [1]], ![[0], [7], [2, 7], [0, 2, 0, 6], [3, 7], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1577 ⟨![[], [0, 0, 0, 1], [0, 0, 2, 0], [0, 0, 0, 4], [0, 0], [0, 1], [2, 0, 5], [0]], ![[7], [1, 7], [2, 7], [2, 2], [3, 7], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 149) : Classified H :=
  classify_of_checks 149 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node149

end ReeTwo.SylowModel.SmallEvenMaximalLower
