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

namespace Node25

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0, 0, 1, 0, 1, 1, 1, 1, 1], [0, 0, 0, 1, 1, 0, 0, 1, 1, 0], [0, 0, 0, 0, 1, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0], [0, 1, 1, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0], [1, 1, 1, 1], [1, 1, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 24) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 25 :=
  generated_of_packed 24 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .core, .edge 282 ⟨![[0], [], [0, 2, 3, 4], [0, 3, 0, 1]], ![[0], [0, 0, 3, 0, 2], [0, 2, 2, 0, 2, 2], [2, 0, 2, 2, 2, 2], [0, 2, 0, 3, 2, 3], [0, 0, 3, 2, 3, 2], [0, 0, 0, 2, 2, 0, 2, 2], [3, 3], [3, 3], [3, 3]]⟩, .edge 283 ⟨![[], [6, 0, 3], [2, 5], [0]], ![[3], [1, 1, 1, 2, 1, 1, 1], [1, 1, 2, 3, 2, 3, 2], [1, 1, 2, 1, 2, 2, 3, 2], [1, 1, 3, 3], [1, 1, 2, 3, 2, 3], [1, 1, 2, 2, 2, 3, 2, 3], [1, 3, 1, 3], [1, 3, 1, 3], [1, 3, 1, 3]]⟩] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 2 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 25) : Classified H :=
  classify_of_checks 25 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node25

namespace Node26

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0, 0, 1, 0, 0, 1, 0], [1, 1, 1, 0, 2, 1, 0], [1, 0, 0, 0, 1, 1, 0, 1], [0, 0, 1, 1, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 1, 0, 1, 1], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 25) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 26 :=
  generated_of_packed 25 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 286 ⟨![[], [0], [1, 2, 6], [4, 6, 7], [0, 2, 6], [1, 2, 4, 5]], ![[1], [1, 1, 1, 4, 2], [4, 4, 4, 1], [1, 1], [1, 4, 4, 1], [2, 2], [1, 1, 4, 3, 4], [2, 5, 3], [2, 5, 3], [2, 5, 3]]⟩, .core, .edge 288 ⟨![[], [0, 4, 2, 6], [1, 2, 6], [4, 6, 7], [0], [1, 2, 4, 5]], ![[4], [2, 4, 4, 1, 4], [4, 1, 1, 1], [1, 4], [1, 1, 1, 3, 1], [2, 2], [1, 1, 3, 4, 4], [2, 5, 3], [2, 5, 3], [2, 5, 3]]⟩, .edge 284 ⟨![[0], [1], [], [0, 0, 5, 0], [1, 5], [5]], ![[0], [1], [0, 1, 1, 4, 3, 1], [1, 1], [1, 0, 1, 4, 3, 1], [5], [0, 0, 1, 0, 0, 1, 1, 4], [0, 3, 5], [0, 3, 5], [0, 3, 5]]⟩, .edge 287 ⟨![[], [1], [2, 0, 7], [4, 6, 7], [1, 2, 6], [0, 2, 6]], ![[1, 1, 1, 4, 2], [1], [4, 4, 4, 1], [1, 1], [1, 4, 4, 1], [2, 5], [1, 1, 4, 3, 4], [5, 5], [5, 5], [5, 5]]⟩, .edge 285 ⟨![[0], [], [1, 3, 2], [0, 2, 0, 0], [3], [1, 2, 6]], ![[0], [5, 3, 0], [2, 0, 5, 0], [4], [2, 2, 3, 3, 4], [2, 5], [0, 0, 3, 3], [0, 2, 3, 5], [0, 2, 3, 5], [0, 2, 3, 5]]⟩, .edge 289 ⟨![[], [1, 0], [2, 0, 7], [1, 3, 1], [0, 1, 4, 5], [0, 2, 6]], ![[1, 1, 4, 1, 5], [4, 3, 2], [4, 1, 1, 1], [1, 4], [1, 1, 1, 3, 1], [2, 5], [1, 1, 3, 4, 4], [5, 5], [5, 5], [5, 5]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 26) : Classified H :=
  classify_of_checks 26 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node26

namespace Node27

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 1, 3, 1, 2], [1, 2, 1, 1, 1, 2], [0, 2, 2, 3, 0, 3], [0, 3, 0, 3], [1, 1, 1, 1], [1, 1, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 26) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 27 :=
  generated_of_packed 26 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 293 ⟨![[0], [], [2, 1, 3, 4, 5], [1], [0, 7], [3], [1, 3, 2], [1, 4, 6]], ![[0], [3], [5, 2, 7], [5], [0, 0, 2, 6], [6, 6], [0, 4], [5, 5], [5, 5], [5, 5]]⟩, .edge 300 ⟨![[], [0, 6], [0, 1, 2, 5, 0], [1], [6, 7], [0], [0, 1, 2, 0], [1, 5]], ![[5], [3], [1, 2, 1, 3], [1, 5], [1, 1, 1, 3, 1, 3], [2, 2, 3, 7], [3, 4, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 290 ⟨![[0], [1], [], [2], [0, 2, 2], [1, 4, 5], [2, 2], [2]], ![[0], [1], [3], [1, 1], [1, 1, 1, 5, 6], [1, 1, 1, 1, 6], [0, 3, 0, 3], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩, .edge 297 ⟨![[], [1], [0, 1, 2, 1], [2], [0, 0], [1, 7], [1, 0, 2, 1], [2, 5]], ![[1, 2, 1, 3], [1], [3], [1, 1], [1, 1, 1, 2, 5, 6], [2, 3, 6, 3], [3, 4, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 294 ⟨![[0], [], [1, 2, 7], [2], [0, 7], [3], [3, 2, 1, 5], [2, 4, 6]], ![[0], [5, 6, 7], [3], [5], [2, 2, 5], [6, 2], [0, 4], [5, 5], [5, 5], [5, 5]]⟩, .edge 301 ⟨![[], [0, 1, 5], [0, 3, 2, 4], [2], [0, 0], [1, 0, 7], [3, 2, 0, 4], [2, 5]], ![[1, 2, 5, 7], [1, 1, 2, 5, 7], [3], [1, 5], [1, 1, 1, 3, 1, 3], [2, 3, 6, 3], [3, 4, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 292 ⟨![[0], [1], [1, 2, 1, 6], [], [0, 5], [1, 4, 7], [1, 2, 1, 6], [5, 7]], ![[0], [1], [1, 2, 1], [1, 1], [1, 1, 1, 5], [0, 0, 0, 4], [0, 4, 7], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩, .edge 299 ⟨![[], [1], [1, 2, 1, 6], [0, 2, 5], [0, 0], [1, 7], [3, 4, 2], [2, 0, 5]], ![[1, 3, 5, 6], [1], [1, 2, 1], [1, 1], [1, 1, 1, 2, 1, 2], [2, 2, 3, 3, 4], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 296 ⟨![[0], [], [3, 2, 4, 5], [1, 3, 4, 2], [0, 7], [3], [2, 3, 7], [0, 0, 1, 2]], ![[0], [3, 2], [6, 5], [5], [0, 0, 2, 6], [6, 6], [0, 4], [5, 5], [5, 5], [5, 5]]⟩, .edge 303 ⟨![[], [0, 1, 5], [3, 2, 4, 5], [0, 2, 5], [0, 0], [1, 0, 7], [3, 4, 2], [2, 0, 5]], ![[1, 6, 1, 7], [1, 1, 6, 1, 7], [1, 6, 5], [1, 5], [1, 1, 1, 6, 1, 2], [2, 2, 3, 3, 4], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 291 ⟨![[0], [1], [], [1, 2, 1, 4], [0, 5, 7], [1, 4, 5], [5, 7], [2, 1, 4, 1]], ![[0], [1], [5, 1, 3], [1, 1], [1, 1, 1, 5, 6], [1, 1, 1, 1, 6], [0, 3, 0, 3], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩, .edge 298 ⟨![[], [1], [0, 3, 2, 4], [0, 5, 6, 7], [6, 7], [1, 7], [1, 2, 0, 1], [0]], ![[7], [1], [1, 2, 1, 3], [1, 1], [1, 1, 1, 2, 5, 6], [2, 3, 2, 4, 7], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 295 ⟨![[0], [], [1, 2, 6], [3, 4, 1], [0, 7], [3], [2, 3, 1, 4], [1]], ![[0], [7], [0, 0, 7, 6], [5], [2, 2, 5], [6, 2], [0, 4], [5, 5], [5, 5], [5, 5]]⟩, .edge 302 ⟨![[], [1, 0, 6], [0, 3, 2, 4], [0, 5, 6, 7], [6, 7], [1, 0], [1, 1, 0, 2], [0]], ![[7], [1, 7], [3, 1, 6, 5], [1, 5], [1, 1, 1, 6, 5, 6], [2, 3, 2, 4, 7], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 27) : Classified H :=
  classify_of_checks 27 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node27

namespace Node28

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0, 0, 1, 0, 0, 1, 2, 0], [0, 1, 0, 1, 0, 0], [0, 1, 2, 0, 0, 1, 0, 2], [0, 1, 0, 0, 1, 0], [0, 0, 1, 0, 2, 2, 0, 1], [0, 0, 0, 2, 2, 0, 2, 2], [0, 0, 0, 2, 2, 0, 2, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 27) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 28 :=
  generated_of_packed 27 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 305 ⟨![[0], [], [0, 1, 5, 0], [0, 3], [], [1, 2, 4, 6]], ![[0], [0, 0, 0, 2, 0, 3, 3], [0, 0], [0, 0, 0, 3], [0, 0, 0, 5, 0, 2], [0, 0, 3, 3], [0, 0, 2, 2, 3, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 308 ⟨![[], [0, 3, 2], [1, 2, 4, 5], [2], [0], [2, 1, 5]], ![[4], [1, 2, 4, 3], [3], [1, 1, 3], [2, 2, 5, 2], [1, 3, 4, 3], [1, 2, 4, 5], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩, .edge 304 ⟨![[0], [1], [], [4, 0], [1, 5, 6], [5, 6]], ![[0], [1], [0, 0], [0, 0, 0, 1, 0, 1], [0, 0, 3, 0], [0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 4], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 307 ⟨![[], [1], [0, 5], [2], [1, 3, 5, 7], [0, 2, 4, 5]], ![[1, 3, 1, 2, 3], [1], [3], [1, 3, 4, 3], [1, 2, 2, 1, 3], [1, 3, 1, 3], [1, 2, 5, 3, 1, 3], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩, .edge 306 ⟨![[0], [], [1, 2, 4, 6], [0, 3], [], [1, 2, 4, 5]], ![[0], [0, 0, 0, 2, 3, 0, 0], [0, 0], [0, 0, 0, 3], [0, 0, 0, 5, 3, 5], [0, 0, 3, 3], [0, 0, 2, 5, 3, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 309 ⟨![[], [0, 2, 3, 1], [0, 5], [2], [0, 1, 1, 1], [0, 2, 4, 5]], ![[1, 3, 4, 2, 3], [3, 1, 3, 2], [3], [1, 1, 3], [1, 2, 2, 4, 3], [1, 3, 4, 3], [1, 2, 3, 1, 3, 2], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 28) : Classified H :=
  classify_of_checks 28 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node28

namespace Node29

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [4]],
   ![[0], [1], [2], [0, 1, 3, 0, 1, 2, 3], [3], [0, 1, 1, 1, 0, 1], [2, 3, 2, 3], [0, 2, 0, 3, 2, 3], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 28) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 29 :=
  generated_of_packed 28 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 316 ⟨![[], [0], [0, 1, 5, 0, 6], [2], [], [0, 4], [0, 1, 6, 0], [2, 4, 5]], ![[1], [1, 1, 7, 2, 3], [3], [1, 1], [1, 1, 1, 5], [2, 2], [2, 7, 6, 7], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .core, .edge 320 ⟨![[], [0, 4], [0, 0, 1, 5, 6], [2], [], [0], [0, 0, 1, 6], [2, 4, 5]], ![[5], [1, 1, 3, 6, 3], [3], [1, 5], [1, 1, 1, 5], [2, 2], [2, 7, 6, 7], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 311 ⟨![[0], [1], [], [2], [0, 5], [4, 1], [5], [2, 6, 7]], ![[0], [1], [3], [1, 1], [0, 3, 4, 3], [6], [0, 3, 7, 0], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 318 ⟨![[], [1], [3, 4, 0, 6], [2], [], [1, 4], [2, 0, 2, 3], [2, 4, 5]], ![[1, 1, 7, 6, 7], [1], [3], [1, 1], [1, 1, 1, 5], [2, 6], [2, 3, 2, 7], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 314 ⟨![[0], [], [5, 1, 6], [2], [0, 4, 7], [3], [1, 1, 6, 1], [2, 4]], ![[0], [0, 3, 0, 2, 3], [3], [5], [3, 7], [2, 6], [0, 2, 0, 3, 6, 3], [0, 3, 7, 4], [0, 3, 7, 4], [0, 3, 7, 4]]⟩, .edge 322 ⟨![[], [1, 0], [1, 0, 1, 6], [2], [], [1, 0, 4], [0, 1, 6, 1], [2, 4, 5]], ![[1, 1, 3, 2, 7], [1, 1, 1, 3, 2, 7], [3], [1, 5], [1, 1, 1, 5], [2, 6], [2, 3, 2, 7], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 310 ⟨![[0], [1], [1, 2, 5, 1, 6], [], [0, 4, 5], [4, 1], [1, 2, 1, 5], []], ![[0], [1], [0, 1, 4, 5, 6], [1, 1], [0, 2, 2, 4], [2, 2], [0, 6, 0, 2], [0, 6, 0, 6], [0, 6, 0, 6], [0, 6, 0, 6]]⟩, .edge 317 ⟨![[], [1], [0, 0, 2, 3, 6], [0, 0, 0], [], [1, 4], [0, 2, 0, 3], [0]], ![[7], [1], [1, 1, 7, 6, 7], [1, 1], [1, 1, 1, 5], [2, 2], [2, 7, 2, 3], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 313 ⟨![[0], [], [1, 1, 2, 5, 6], [1, 1, 1], [0, 4, 7], [3], [1, 2, 1, 5], [1]], ![[0], [7], [0, 3, 2, 3, 4], [5], [3, 5, 3], [2, 2], [0, 2, 3, 2, 4, 7], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6]]⟩, .edge 321 ⟨![[], [0, 1, 7], [0, 0, 1, 2, 1], [0, 0, 0], [], [0, 4, 1], [0, 2, 0, 3], [0]], ![[7], [1, 7], [1, 1, 3, 2, 7], [1, 5], [1, 1, 1, 5], [2, 2], [2, 7, 2, 3], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 312 ⟨![[0], [1], [], [3, 4, 2], [0, 5], [4, 1], [5], [2, 2, 2, 3, 4]], ![[0], [1], [3, 1, 5], [1, 1], [0, 3, 0, 7], [6], [0, 3, 3, 4], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 319 ⟨![[], [1], [0, 3, 4, 2], [0, 0, 0], [], [1, 4], [0, 0, 0, 2, 3], [0]], ![[7], [1], [1, 1, 7, 6], [1, 1], [1, 1, 1, 5], [2, 6], [2, 3, 6, 3], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 315 ⟨![[0], [], [5, 1, 2], [1, 1, 1], [0, 4, 7], [3], [0, 1, 2, 3, 0], [1]], ![[0], [7], [0, 7, 0, 6], [5], [3, 5, 3], [2, 6], [0, 2, 3, 2, 0, 3], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 323 ⟨![[], [0, 1, 7], [0, 2, 1, 1], [0, 0, 0], [], [0, 4, 1], [0, 0, 0, 2, 3], [0]], ![[7], [1, 7], [1, 1, 3, 2], [1, 5], [1, 1, 1, 5], [2, 6], [2, 3, 6, 3], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 29) : Classified H :=
  classify_of_checks 29 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node29

namespace Node30

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [4]],
   ![[0], [1], [2], [0, 0, 0, 1, 2, 1, 0], [3], [0, 0, 1, 1, 2, 2], [2, 3, 2, 3], [0, 1, 1, 3, 0, 3], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 29) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 30 :=
  generated_of_packed 29 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 327 ⟨![[0], [], [1, 3, 5], [2], [0, 3, 4], [3, 4, 7], [1, 3, 4], [2, 5]], ![[0], [5, 6], [3], [0, 0], [0, 4], [3, 7], [0, 3, 4, 3], [2, 2, 6, 6], [2, 2, 6, 6], [2, 2, 6, 6]]⟩, .edge 334 ⟨![[], [0, 4], [1, 3, 5], [2], [3], [0], [1, 3, 5], [2, 4, 6]], ![[5], [5, 2, 1], [3], [4], [1, 1, 1, 5], [2, 3, 2, 3], [1, 3, 7, 4, 5], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 325 ⟨![[0], [1], [], [2], [0], [1, 4, 5], [5, 6], [2, 6]], ![[0], [1], [3], [0, 0], [0, 0, 5, 5], [3, 6, 7], [3, 7], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 332 ⟨![[], [1], [0, 5], [2], [3], [1, 3, 4], [0, 3, 5], [2, 4, 6]], ![[1, 6, 5], [1], [3], [4], [1, 1, 1, 4, 5], [2, 3, 6, 7], [2, 1, 2, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 329 ⟨![[0], [], [1], [2], [0, 3, 4], [3, 4, 7], [1, 3, 5], [2, 5]], ![[0], [2], [3], [0, 0], [0, 4], [3, 7], [0, 0, 2, 2], [2, 2, 6, 6], [2, 2, 6, 6], [2, 2, 6, 6]]⟩, .edge 336 ⟨![[], [6, 0, 1], [0, 5], [2], [3], [0, 4, 1, 6], [0, 3, 5], [2, 4, 6]], ![[1, 2, 1], [1, 1, 2, 1], [3], [4], [1, 1, 1, 5], [2, 3, 6, 7], [2, 1, 6, 1], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 324 ⟨![[0], [1], [1, 2, 1], [], [4, 6, 0], [5, 1], [1, 2, 1, 6], []], ![[0], [1], [5, 2, 5], [0, 0], [0, 0, 5, 5], [2, 6], [0, 1, 1, 4], [0, 0, 4, 4], [0, 0, 4, 4], [0, 0, 4, 4]]⟩, .edge 331 ⟨![[], [1], [1, 2, 1], [0, 0, 0], [3], [1, 3, 4], [1, 2, 1], [0]], ![[7], [1], [5, 2, 5], [4], [1, 1, 1, 4, 5], [2, 3, 2, 7], [1, 1, 3, 3], [1, 5], [1, 5], [1, 5]]⟩, .edge 328 ⟨![[0], [], [2, 3, 5], [1, 1, 1], [0, 3, 4], [1, 5, 1], [2, 3, 4], [1]], ![[0], [7], [5, 6], [0, 0], [0, 4], [3, 5, 3], [0, 3, 0, 7], [2, 2, 6, 6], [2, 2, 6, 6], [2, 2, 6, 6]]⟩, .edge 335 ⟨![[], [0, 4, 5, 1], [2, 3, 5], [0, 0, 0], [3], [0, 5, 1], [2, 3, 5], [0]], ![[7], [1, 7], [5, 2, 1], [4], [1, 1, 1, 5], [2, 3, 2, 7], [1, 5, 3, 3], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 326 ⟨![[0], [1], [], [3, 2], [0], [1, 4, 5], [5, 6], [3, 2, 5]], ![[0], [1], [0, 0, 3], [0, 0], [0, 0, 5, 5], [3, 3], [3, 3, 6], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 333 ⟨![[], [1], [5, 0, 2, 6], [0, 0, 0], [3], [1, 3, 4], [0, 0, 2, 5, 0], [0]], ![[7], [1], [1, 7, 5, 2], [4], [1, 1, 1, 4, 5], [2, 3, 2, 3], [1, 1, 3, 3], [1, 5], [1, 5], [1, 5]]⟩, .edge 330 ⟨![[0], [], [4, 2, 1], [1, 1, 1], [0, 3, 4], [1, 5, 1], [1, 1, 2, 1, 7], [1]], ![[0], [7], [0, 4, 2, 3], [0, 0], [0, 4], [3, 5, 3], [0, 0, 2, 2], [2, 2, 6, 6], [2, 2, 6, 6], [2, 2, 6, 6]]⟩, .edge 337 ⟨![[], [0, 4, 5, 1], [5, 0, 2, 6], [0, 0, 0], [3], [0, 5, 1], [0, 0, 2, 5, 0], [0]], ![[7], [1, 7], [2, 1, 3, 5], [4], [1, 1, 1, 5], [2, 3, 2, 3], [1, 5, 3, 3], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 30) : Classified H :=
  classify_of_checks 30 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node30

namespace Node31

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [1, 1, 1, 2, 1, 1, 1], [0, 0, 0, 1, 1, 1, 0, 1], [0, 1, 2, 1, 0, 1, 1, 2], [0, 0, 1, 0, 1, 1, 0, 1], [0, 1, 2, 1, 0, 1, 2, 1], [0, 1, 0, 1, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 30) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 31 :=
  generated_of_packed 30 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 339 ⟨![[0], [], [2, 1, 4], [0, 3, 5, 7], [2], [2, 1]], ![[0], [4, 5], [4], [0, 3, 5, 5], [2, 2, 2, 5], [0, 0, 2, 2], [0, 0], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩, .edge 342 ⟨![[], [0, 3, 6], [2, 1, 4], [6], [0], [2, 1, 4]], ![[4], [2, 2, 4, 2, 1], [1, 4], [1, 3, 4, 1, 1], [1, 1, 2, 4, 2, 4], [2, 2, 3], [3], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩, .edge 338 ⟨![[0], [1], [], [0], [1, 4], [5, 6]], ![[0], [1], [1, 1], [0, 1, 1, 4, 0, 4], [1, 1, 1, 4], [0, 0, 5], [0, 0], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 341 ⟨![[], [1], [1, 0, 3, 1], [6], [1, 3], [0, 1, 4, 1]], ![[1, 2, 4, 2, 2], [1], [1, 1], [1, 1, 1, 4], [1, 2, 1, 1, 4, 2], [2, 2], [3], [1, 4, 1, 4], [1, 4, 1, 4], [1, 4, 1, 4]]⟩, .edge 340 ⟨![[0], [], [1], [0, 3, 5, 7], [2], [2, 1, 4]], ![[0], [2], [4], [0, 3, 5, 2], [0, 2, 4, 3, 2], [0, 0, 2, 5], [0, 0], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩, .edge 343 ⟨![[], [0, 0, 1, 0], [0, 1, 1, 5], [6], [1, 0, 3, 7], [0, 2, 4, 7]], ![[1, 2, 1, 2, 5], [2, 4, 1, 4], [1, 4], [1, 3, 4, 1, 1], [1, 1, 2, 1, 2, 4], [2, 2], [3], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 31) : Classified H :=
  classify_of_checks 31 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node31

namespace Node32

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [1, 0, 0, 1, 1, 2, 1], [0, 0, 1, 1, 2, 2], [1, 2, 1, 1, 1, 2], [1, 1, 2, 1, 1, 2], [0, 1, 2, 0, 1, 2], [1, 1, 1, 1], [1, 1, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 31) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 32 :=
  generated_of_packed 31 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 345 ⟨![[0], [], [0, 1, 0, 5], [3, 0, 7], [2, 3, 6], [1, 1, 1, 2]], ![[0], [0, 0, 2, 5, 2], [0, 0], [0, 0, 3, 0], [0, 3, 5, 4, 2], [0, 3, 3, 0], [0, 3, 5, 4, 5], [4, 4], [4, 4], [4, 4]]⟩, .edge 348 ⟨![[], [0, 3, 2], [2, 1, 4, 5], [2], [0], [1, 2, 5]], ![[4], [1, 5, 3, 1], [3], [1, 1, 3, 1, 4], [2, 2, 5, 2], [1, 1, 4, 4], [1, 1], [1, 4, 1, 4], [1, 4, 1, 4], [1, 4, 1, 4]]⟩, .edge 344 ⟨![[0], [1], [], [4, 0], [1, 4, 7], [5, 6, 7]], ![[0], [1], [0, 0], [0, 0, 4, 4], [0, 0, 3, 0], [0, 1, 3, 4], [0, 1, 3, 5, 4], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 347 ⟨![[], [1], [5, 0], [2], [3, 1, 7], [1, 0, 5, 1]], ![[4, 5, 4], [1], [3], [1, 4, 4, 4], [1, 4, 2, 2], [1, 1, 4, 4], [1, 3, 4], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩, .edge 346 ⟨![[0], [], [3, 1], [3, 0, 7], [2, 3, 6], [2, 1, 4]], ![[0], [0, 0, 2, 4], [0, 0], [0, 0, 3, 0], [0, 3, 2, 2], [0, 3, 3, 0], [0, 3, 5, 4, 2], [4, 4], [4, 4], [4, 4]]⟩, .edge 349 ⟨![[], [1, 0, 0, 0], [5, 0], [2], [0, 1, 4, 7], [0, 1, 3, 1]], ![[4, 2, 3, 1], [3, 2, 4], [3], [4, 2, 4, 5], [4, 5, 1, 5], [1, 1, 4, 4], [1, 1], [1, 4, 1, 4], [1, 4, 1, 4], [1, 4, 1, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 32) : Classified H :=
  classify_of_checks 32 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node32

namespace Node33

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [5]],
   ![[0], [1], [2], [2, 2], [1, 2, 2, 2, 1, 2], [3], [1, 2, 2, 1, 2, 2], [0, 0], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 32) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 33 :=
  generated_of_packed 32 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 353 ⟨![[0], [], [1], [2], [0], [], [1, 4], [2, 5]], ![[0], [2], [3], [2, 2], [2, 2, 2, 6], [0, 0], [2, 2, 6, 6], [0, 3, 0, 7], [0, 3, 0, 7], [0, 3, 0, 7]]⟩, .edge 360 ⟨![[], [0, 5], [1], [2], [5], [0], [1, 7], [2, 7]], ![[5], [2], [3], [2, 2], [1, 2, 2, 2, 5, 6], [4], [1, 2, 2, 5, 2, 2], [3, 7], [3, 7], [3, 7]]⟩, .edge 351 ⟨![[0], [1], [], [2], [0, 7], [1, 4, 6, 7], [3], [2, 7]], ![[0], [1], [3], [6], [1, 6, 5, 6], [0, 0], [1, 6, 1, 6], [3, 7], [3, 7], [3, 7]]⟩, .edge 358 ⟨![[], [1], [0, 5, 7], [2], [5], [1], [0], [2, 7]], ![[6], [1], [3], [2, 6], [1, 2, 2, 2, 1, 2], [4], [1, 2, 2, 1, 2, 2], [3, 7], [3, 7], [3, 7]]⟩, .edge 355 ⟨![[0], [], [1, 4], [2], [0], [], [1], [2, 5]], ![[0], [6], [3], [2, 6], [2, 6, 2, 2], [0, 0], [2, 6, 6, 2], [0, 3, 0, 7], [0, 3, 0, 7], [0, 3, 0, 7]]⟩, .edge 362 ⟨![[], [1, 0, 0, 0], [0, 5, 7], [2], [5], [0, 3, 1, 4], [0], [2, 7]], ![[6], [1, 6], [3], [2, 6], [1, 2, 2, 2, 1, 6], [4], [1, 2, 2, 5, 2, 2], [3, 7], [3, 7], [3, 7]]⟩, .edge 350 ⟨![[0], [1], [2], [], [0, 7], [1, 5], [2, 7], []], ![[0], [1], [2], [2, 2], [1, 2, 2, 2, 1, 2], [0, 0], [1, 2, 2, 1, 2, 2], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 357 ⟨![[], [1], [2], [0, 0, 0], [5], [1], [2, 7], [0]], ![[7], [1], [2], [2, 2], [1, 2, 2, 2, 1, 2], [4], [1, 2, 2, 1, 2, 2], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 354 ⟨![[0], [], [2], [1, 5], [0], [], [2, 4], [1]], ![[0], [7], [2], [2, 2], [2, 2, 2, 6], [0, 0], [2, 2, 6, 6], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 361 ⟨![[], [0, 1], [2], [0, 0, 0], [5], [0, 1, 5], [2, 7], [0]], ![[7], [1, 7], [2], [2, 2], [1, 2, 2, 2, 5, 6], [4], [1, 2, 2, 5, 2, 2], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 352 ⟨![[0], [1], [], [2, 2, 2], [0, 7], [1, 4, 6, 7], [3], [2]], ![[0], [1], [7], [6], [1, 6, 5, 6], [0, 0], [1, 6, 1, 6], [3, 3, 6], [3, 3, 6], [3, 3, 6]]⟩, .edge 359 ⟨![[], [1], [0, 2, 5], [0, 0, 0], [5], [1], [2, 0], [0]], ![[7], [1], [2, 7], [2, 6], [1, 2, 2, 2, 1, 2], [4], [1, 2, 2, 1, 2, 2], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 356 ⟨![[0], [], [2, 1, 5], [1, 5], [0], [], [1, 2, 7], [1]], ![[0], [7], [2, 7], [2, 6], [2, 6, 2, 2], [0, 0], [2, 6, 6, 2], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 363 ⟨![[], [0, 1], [0, 2, 5], [0, 0, 0], [5], [0, 1, 5], [2, 0], [0]], ![[7], [1, 7], [2, 7], [2, 6], [1, 2, 2, 2, 1, 6], [4], [1, 2, 2, 5, 2, 2], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 33) : Classified H :=
  classify_of_checks 33 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node33

namespace Node34

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [2, 2], [1, 2, 2, 2, 1, 2], [0, 0, 0, 2, 0, 2, 2, 2], [1, 2, 2, 1, 2, 2], [0, 2, 2, 0, 2, 2], [0, 0, 0, 2, 2, 0, 2, 2], [0, 0, 0, 2, 2, 0, 2, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 33) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 34 :=
  generated_of_packed 33 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 365 ⟨![[0], [], [1], [0], [], [1, 3]], ![[0], [2], [2, 2], [2, 2, 2, 5], [0, 5, 0, 2, 5, 2], [2, 2, 5, 5], [0, 0, 2, 5, 2, 5], [2, 5, 2, 5], [2, 5, 2, 5], [2, 5, 2, 5]]⟩, .edge 368 ⟨![[], [0, 0, 0], [1], [0, 0], [0], [4, 1]], ![[4], [2], [2, 2], [1, 2, 5, 2, 4, 2], [2, 2, 5, 2], [1, 2, 2, 4, 5, 5], [2, 2, 3, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩, .edge 364 ⟨![[0], [1], [], [0, 4], [1, 3, 5, 7], [2]], ![[0], [1], [5], [1, 5, 4, 5], [0, 0, 0, 3], [1, 5, 1, 5], [0, 5, 0, 5], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 367 ⟨![[], [1], [0, 4, 6], [6, 7], [1], [0]], ![[5], [1], [2, 5], [1, 2, 5, 2, 1, 5], [2, 2, 3, 5, 2], [1, 2, 5, 1, 2, 5], [2, 2, 3, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩, .edge 366 ⟨![[0], [], [1, 3], [0], [], [1]], ![[0], [5], [2, 5], [2, 5, 2, 2], [0, 5, 0, 5, 5, 5], [2, 5, 5, 2], [0, 0, 2, 2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2]]⟩, .edge 369 ⟨![[], [1, 0, 0, 0], [0, 4, 6], [6, 7], [0, 2, 1, 3], [0]], ![[5], [1, 5], [2, 5], [1, 2, 2, 2, 1, 5], [2, 2, 3, 5, 2], [1, 2, 2, 1, 2, 2], [2, 2, 3, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 34) : Classified H :=
  classify_of_checks 34 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node34

namespace Node35

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [2, 3, 2, 3], [0, 2, 0, 2, 3, 3], [3, 3], [1, 0, 1, 0], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 34) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 35 :=
  generated_of_packed 34 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 376 ⟨![[], [0], [1], [2], [], [0, 3], [1, 3, 5], [2, 5]], ![[1], [2], [3], [1, 1, 1, 5], [2, 3, 3, 6], [3, 3], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .core, .edge 380 ⟨![[], [0, 3], [1], [2], [], [0], [1, 3, 5], [2, 5]], ![[5], [2], [3], [1, 1, 1, 5], [2, 3, 3, 6], [3, 3], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 371 ⟨![[0], [1], [], [2], [0, 3, 5, 7], [1, 3, 4], [3, 4, 7], [4, 2, 5]], ![[0], [1], [3], [3, 7, 6], [7, 3], [3, 3], [0, 5, 0, 5], [0, 6, 0, 6], [0, 6, 0, 6], [0, 6, 0, 6]]⟩, .edge 378 ⟨![[], [1], [0, 3, 5], [2], [], [1, 3], [0], [2, 5]], ![[6], [1], [3], [1, 1, 1, 5], [2, 3, 3, 2], [3, 3], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 374 ⟨![[0], [], [1, 4, 6], [2], [0, 3, 7], [3, 6], [1], [2, 7]], ![[0], [6], [3], [0, 3, 4, 7], [0, 4, 2, 6], [3, 3], [0, 5, 4], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 382 ⟨![[], [0, 3, 1], [0, 3, 5], [2], [], [0, 1, 7], [0], [2, 5]], ![[6], [1, 6], [3], [1, 1, 1, 5], [2, 3, 3, 2], [3, 3], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 370 ⟨![[0], [1], [2], [], [0, 5], [1, 7], [4, 5, 2], [5]], ![[0], [1], [2], [2, 6, 7], [2, 4, 2, 0], [7], [0, 1, 0, 5], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 377 ⟨![[], [1], [2], [0, 5], [], [1, 3], [2, 3, 5], [0]], ![[7], [1], [2], [1, 1, 1, 5], [2, 3, 7, 6], [3, 7], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 373 ⟨![[0], [], [2], [3, 1, 6], [0, 3, 7], [3, 6], [2, 3, 4], [1]], ![[0], [7], [2], [0, 2, 6, 4], [0, 4, 2, 2], [3, 7], [0, 5, 4], [2, 6], [2, 6], [2, 6]]⟩, .edge 381 ⟨![[], [1, 0], [2], [0, 5], [], [1, 0, 3], [2, 3, 5], [0]], ![[7], [1, 7], [2], [1, 1, 1, 5], [2, 3, 7, 6], [3, 7], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 372 ⟨![[0], [1], [], [3, 5, 2], [0, 2, 5, 2], [1, 3, 4], [2, 4, 2], [2]], ![[0], [1], [7], [7, 7], [3, 3, 6], [3, 7], [0, 5, 0, 5], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 379 ⟨![[], [1], [2, 0], [0, 5], [], [1, 3], [0, 4, 2], [0]], ![[7], [1], [2, 7], [1, 1, 1, 5], [2, 3, 7, 2], [3, 7], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 375 ⟨![[0], [], [6, 1, 2], [3, 1, 6], [0, 3, 7], [3, 6], [1, 4, 2], [1]], ![[0], [7], [2, 7], [0, 3, 0, 7], [0, 4, 2, 6], [3, 7], [0, 5, 4], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 383 ⟨![[], [1, 0], [2, 0], [0, 5], [], [1, 0, 3], [0, 4, 2], [0]], ![[7], [1, 7], [2, 7], [1, 1, 1, 5], [2, 3, 7, 2], [3, 7], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 35) : Classified H :=
  classify_of_checks 35 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node35

namespace Node36

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 1, 1, 1, 0, 1], [0, 1, 3, 0, 3, 1], [1, 2, 3, 2, 1, 3], [1, 0, 1, 0], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 35) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 36 :=
  generated_of_packed 35 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 390 ⟨![[], [0], [1], [2], [], [0, 3], [1, 3, 5], [0, 2, 3, 0]], ![[1], [2], [3], [1, 1, 1, 5], [3, 5, 1, 7], [1, 1, 2, 1, 6, 5], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .core, .edge 394 ⟨![[], [0, 3], [1], [2], [], [0], [1, 3, 5], [0, 0, 2, 4]], ![[5], [2], [3], [1, 1, 1, 5], [3, 5, 5, 7], [1, 1, 2, 1, 2, 5], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 385 ⟨![[0], [1], [], [2], [0, 3, 5, 7], [1, 3, 4], [3, 4, 7], [2, 5, 6]], ![[0], [1], [3], [0, 1, 1, 1, 0, 1], [0, 1, 1, 1, 0, 5], [1, 3, 5, 7], [0, 5, 0, 5], [0, 6, 0, 6], [0, 6, 0, 6], [0, 6, 0, 6]]⟩, .edge 392 ⟨![[], [1], [0, 3, 5], [2], [], [1, 3], [0], [1, 2, 3, 1]], ![[6], [1], [3], [1, 1, 1, 5], [3, 5, 1, 7], [1, 1, 2, 5, 2, 5], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 388 ⟨![[0], [], [1, 4, 6], [2], [0, 3, 7], [3, 6], [1], [2, 4]], ![[0], [6], [3], [0, 5, 4, 5], [3, 7], [0, 2, 0, 2, 5], [0, 5, 4], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 396 ⟨![[], [0, 3, 1], [0, 3, 5], [2], [], [0, 1, 7], [0], [2, 4, 6, 7]], ![[6], [1, 6], [3], [1, 1, 1, 5], [3, 5, 5, 7], [1, 1, 2, 2, 3, 7], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 384 ⟨![[0], [1], [2], [], [4, 0, 6], [4, 1], [5, 2, 6], []], ![[0], [1], [2], [0, 1, 5, 4], [0, 1, 4, 1], [1, 2, 6, 5], [1, 0, 1, 0], [0, 1, 4, 5], [0, 1, 4, 5], [0, 1, 4, 5]]⟩, .edge 391 ⟨![[], [1], [2], [0, 0, 0], [], [1, 3], [2, 3, 5], [0]], ![[7], [1], [2], [1, 1, 1, 5], [3, 1, 5, 3], [1, 1, 2, 1, 6, 5], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 387 ⟨![[0], [], [2], [1, 1, 1], [0, 3, 7], [3, 6], [2, 3, 4], [1]], ![[0], [7], [2], [0, 2, 6, 4], [3, 5, 3], [0, 6, 4, 2], [0, 5, 4], [2, 6], [2, 6], [2, 6]]⟩, .edge 395 ⟨![[], [0, 0, 1, 0], [2], [0, 0, 0], [], [0, 4, 1], [2, 3, 5], [0]], ![[7], [1, 7], [2], [1, 1, 1, 5], [3, 1, 1, 3], [1, 1, 2, 1, 2, 5], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 386 ⟨![[0], [1], [], [0, 2, 0], [0, 3, 5, 7], [1, 3, 4], [3, 4, 7], [2]], ![[0], [1], [7], [0, 1, 1, 1, 0, 1], [0, 1, 1, 1, 0, 5], [1, 7, 5, 7], [0, 5, 0, 5], [0, 6, 0, 6], [0, 6, 0, 6], [0, 6, 0, 6]]⟩, .edge 393 ⟨![[], [1], [0, 0, 2, 0], [0, 0, 0], [], [1, 3], [0, 5, 2, 6], [0]], ![[7], [1], [2, 7], [1, 1, 1, 5], [3, 1, 5, 3], [1, 1, 2, 5, 2, 5], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 389 ⟨![[0], [], [1, 4, 5, 2], [1, 1, 1], [0, 3, 7], [3, 6], [3, 2, 1], [1]], ![[0], [7], [2, 7], [0, 3, 4, 3], [3, 5, 3], [2, 3, 2, 7], [0, 5, 4], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 397 ⟨![[], [0, 0, 1, 0], [0, 0, 2, 0], [0, 0, 0], [], [0, 4, 1], [0, 5, 2, 6], [0]], ![[7], [1, 7], [2, 7], [1, 1, 1, 5], [3, 1, 1, 3], [1, 1, 2, 2, 3, 3], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 36) : Classified H :=
  classify_of_checks 36 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node36

namespace Node37

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 1, 1, 1, 0, 1], [3, 0, 3, 0], [0, 1, 0, 1, 3, 3], [1, 0, 1, 0], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 36) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 37 :=
  generated_of_packed 36 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 404 ⟨![[], [0], [1], [2], [], [0, 3], [1, 3, 5], [2, 2, 2, 4]], ![[1], [2], [3], [1, 1, 1, 5], [3, 7], [1, 3, 3, 5], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .core, .edge 408 ⟨![[], [0, 3], [1], [2], [], [0], [1, 3, 5], [2, 2, 2, 4]], ![[5], [2], [3], [1, 1, 1, 5], [3, 7], [1, 1, 7, 7], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 399 ⟨![[0], [1], [], [2], [0, 3, 5, 7], [1, 3, 4], [3, 4, 7], [4, 2, 6]], ![[0], [1], [3], [0, 3, 0, 3, 6], [0, 7, 0, 7], [1, 3, 5, 3], [0, 3, 0, 7], [0, 6, 0, 6], [0, 6, 0, 6], [0, 6, 0, 6]]⟩, .edge 406 ⟨![[], [1], [0, 3, 5], [2], [], [1, 3], [0], [0, 0, 2, 6]], ![[6], [1], [3], [1, 1, 1, 5], [3, 7], [1, 3, 3, 5], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 402 ⟨![[0], [], [1, 4, 6], [2], [0, 3, 7], [3, 6], [1], [4, 2]], ![[0], [6], [3], [0, 3, 4, 7], [0, 4, 2, 6], [0, 2, 0, 2, 5], [0, 5, 4], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 410 ⟨![[], [0, 3, 1], [0, 3, 5], [2], [], [0, 1, 7], [0], [0, 0, 2, 6]], ![[6], [1, 6], [3], [1, 1, 1, 5], [3, 7], [1, 1, 7, 7], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 398 ⟨![[0], [1], [2], [], [0, 4, 5, 6], [4, 1], [1, 2, 1], [5, 6, 7]], ![[0], [1], [2], [1, 2, 5, 6], [0, 7, 4], [0, 1, 4, 5], [1, 0, 1, 0], [0, 7, 0, 7], [0, 7, 0, 7], [0, 7, 0, 7]]⟩, .edge 405 ⟨![[], [1], [2], [1, 0, 1, 5], [], [1, 3], [2, 3, 5], [0]], ![[7], [1], [2], [1, 1, 1, 5], [3, 3], [1, 3, 7, 5], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 401 ⟨![[0], [], [2], [0, 1, 0, 5], [0, 3, 7], [3, 6], [2, 3, 4], [1]], ![[0], [7], [2], [0, 2, 6, 4], [0, 4, 2, 2], [0, 6, 4, 2], [0, 5, 4], [2, 6], [2, 6], [2, 6]]⟩, .edge 409 ⟨![[], [0, 0, 1, 0], [2], [4, 5, 6, 0], [], [1, 0, 2, 2], [2, 3, 5], [0]], ![[7], [1, 7], [2], [1, 1, 1, 5], [3, 3], [1, 1, 7, 3], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 400 ⟨![[0], [1], [], [2, 1, 1], [0, 2, 2, 7], [1, 3, 4], [3, 4, 7], [2]], ![[0], [1], [7], [0, 3, 4, 6, 7], [3, 0, 7, 4], [1, 3, 1, 7], [0, 5, 0, 5], [0, 4, 7, 7], [0, 4, 7, 7], [0, 4, 7, 7]]⟩, .edge 407 ⟨![[], [1], [4, 2, 0], [1, 0, 1, 5], [], [1, 3], [0, 4, 2, 5], [0]], ![[7], [1], [2, 7], [1, 1, 1, 5], [3, 3], [1, 3, 7, 5], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 403 ⟨![[0], [], [1, 5, 2, 6], [0, 1, 0, 5], [0, 3, 7], [3, 6], [1, 4, 2, 5], [1]], ![[0], [7], [2, 7], [0, 5, 4, 5], [0, 4, 2, 6], [2, 6, 3, 3], [0, 5, 4], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 411 ⟨![[], [0, 0, 1, 0], [4, 2, 0], [4, 5, 6, 0], [], [1, 3, 0, 4], [0, 4, 2, 5], [0]], ![[7], [1, 7], [2, 7], [1, 1, 1, 5], [3, 3], [1, 1, 7, 3], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 37) : Classified H :=
  classify_of_checks 37 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node37

namespace Node38

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [2, 3, 2, 3], [0, 1, 2, 1, 0, 2], [3, 3], [1, 1, 2, 2], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 37) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 38 :=
  generated_of_packed 37 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 418 ⟨![[], [0], [1], [2], [], [0, 0, 0, 7], [1, 3, 5], [2, 5]], ![[1], [2], [3], [2, 3, 2, 3], [1, 6, 1, 2], [3, 3], [1, 1, 2, 2], [1, 5], [1, 5], [1, 5]]⟩, .core, .edge 422 ⟨![[], [0, 3, 4, 6], [1], [2], [], [0], [1, 3, 5], [2, 5]], ![[5], [2], [3], [2, 3, 2, 3], [1, 2, 5, 2], [3, 3], [1, 2, 2, 5], [1, 1], [1, 1], [1, 1]]⟩, .edge 413 ⟨![[0], [1], [], [2], [0, 3, 5, 7], [1, 1, 1, 5], [1, 1, 6], [4, 2, 5]], ![[0], [1], [3], [3, 7, 6], [7, 3], [1, 5], [1, 1, 6], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 420 ⟨![[], [1], [0, 3, 5], [2], [], [1, 1, 1, 7], [0], [2, 5]], ![[6], [1], [3], [2, 7, 6, 3], [1, 6, 5, 6], [3, 3], [1, 1, 2, 6], [1, 5], [1, 5], [1, 5]]⟩, .edge 416 ⟨![[0], [], [5, 1], [2], [0, 3, 4, 6], [1, 1, 5, 6], [1], [2, 6, 7]], ![[0], [6], [3], [2, 7, 6, 3], [0, 6, 4, 6], [3, 3], [2, 5, 6], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 424 ⟨![[], [0, 0, 1, 0], [0, 3, 5], [2], [], [0, 1, 5, 6], [0], [2, 5]], ![[6], [1, 6], [3], [2, 7, 6, 3], [1, 2, 1, 6], [3, 3], [1, 2, 6, 5], [1, 1], [1, 1], [1, 1]]⟩, .edge 412 ⟨![[0], [1], [2], [], [0, 5], [1, 6], [4, 5, 2], [5]], ![[0], [1], [2], [2, 6, 7], [2, 4, 2, 0], [7], [1, 0, 5, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 419 ⟨![[], [1], [2], [0, 5], [], [0, 1, 6, 0], [2, 3, 5], [0]], ![[7], [1], [2], [2, 3, 6, 7], [1, 6, 1, 2], [3, 7], [1, 1, 2, 2], [1, 5], [1, 5], [1, 5]]⟩, .edge 415 ⟨![[0], [], [2], [1, 2, 2], [0, 3, 4, 6], [2, 2, 6], [1, 1, 2, 6], [1]], ![[0], [7], [2], [2, 3, 6, 7], [0, 2, 4, 6], [3, 7], [2, 2, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 423 ⟨![[], [1, 0], [2], [0, 5], [], [0, 1, 5, 6], [2, 3, 5], [0]], ![[7], [1, 7], [2], [2, 3, 6, 7], [1, 2, 5, 2], [3, 7], [1, 2, 2, 5], [1, 1], [1, 1], [1, 1]]⟩, .edge 414 ⟨![[0], [1], [], [3, 5, 2], [0, 2, 5, 2], [1, 1, 1, 5], [1, 1, 6], [2]], ![[0], [1], [7], [7, 7], [3, 3, 6], [1, 5], [1, 1, 6], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 421 ⟨![[], [1], [2, 0], [0, 5], [], [0, 1, 6, 0], [0, 4, 2], [0]], ![[7], [1], [2, 7], [2, 7, 2, 7], [1, 6, 5, 6], [3, 7], [1, 1, 2, 6], [1, 5], [1, 5], [1, 5]]⟩, .edge 417 ⟨![[0], [], [1, 1, 2, 1], [1, 1, 1, 5], [0, 3, 4, 6], [1, 1, 5, 6], [1, 4, 2], [1]], ![[0], [7], [2, 7], [2, 7, 2, 7], [0, 6, 4, 6], [3, 7], [2, 5, 6], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 425 ⟨![[], [1, 0], [2, 0], [0, 5], [], [0, 1, 5, 6], [0, 4, 2], [0]], ![[7], [1, 7], [2, 7], [2, 7, 2, 7], [1, 2, 1, 6], [3, 7], [1, 2, 6, 5], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 38) : Classified H :=
  classify_of_checks 38 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node38

namespace Node39

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [2, 3, 1, 3, 2, 1], [0, 1, 3, 0, 3, 1], [1, 2, 2, 3, 1, 3], [0, 1, 0, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 38) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 39 :=
  generated_of_packed 38 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 432 ⟨![[], [0], [1], [2], [], [0, 3, 5], [1, 3, 5], [2, 4, 6, 7]], ![[1], [2], [3], [1, 1, 3, 6, 2, 7], [1, 5, 3, 7], [1, 1, 3, 2, 2, 7], [5, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .core, .edge 436 ⟨![[], [0, 3, 5], [1], [2], [], [0], [1, 3, 5], [0, 2, 0, 4]], ![[5], [2], [3], [1, 1, 3, 2, 2, 7], [1, 1, 3, 7], [1, 1, 3, 6, 2, 7], [5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 427 ⟨![[0], [1], [], [2], [0, 1, 1, 6], [0, 1, 0], [3, 4, 7], [2, 5, 6]], ![[0], [1], [3], [1, 3, 7, 1], [1, 7, 5, 7], [1, 3, 7, 5], [5, 1], [0, 6, 0, 6], [0, 6, 0, 6], [0, 6, 0, 6]]⟩, .edge 434 ⟨![[], [1], [0, 3, 5], [2], [], [1, 3, 5], [0], [2, 4, 6, 7]], ![[6], [1], [3], [1, 1, 3, 6, 6, 7], [1, 5, 3, 7], [1, 1, 3, 2, 6, 7], [5, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 430 ⟨![[0], [], [1, 6], [2], [0, 3, 5, 7], [1, 4, 5, 1], [1], [2, 4, 6]], ![[0], [6], [3], [2, 3, 7, 2], [0, 3, 4, 3, 5], [2, 3, 7, 5, 6], [0, 4, 5], [0, 3, 0, 7], [0, 3, 0, 7], [0, 3, 0, 7]]⟩, .edge 438 ⟨![[], [0, 3, 1, 4], [0, 3, 5], [2], [], [0, 0, 0, 1], [0], [1, 1, 2, 3]], ![[6], [1, 6], [3], [1, 1, 3, 2, 6, 7], [1, 1, 3, 7], [1, 1, 3, 6, 6, 7], [5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 426 ⟨![[0], [1], [2], [], [4, 0, 6], [4, 6, 1], [5, 2, 6], []], ![[0], [1], [2], [2, 5, 2, 1], [0, 1, 4, 1], [1, 2, 2, 5], [0, 1, 0, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 433 ⟨![[], [1], [2], [0, 0, 0], [], [0, 1, 0], [2, 3, 5], [0]], ![[7], [1], [2], [1, 1, 3, 2, 6, 3], [1, 5, 3, 3], [1, 1, 3, 3, 6, 6], [5, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 429 ⟨![[0], [], [2], [1, 1, 1], [0, 3, 5, 7], [1, 4, 6, 1], [0, 2, 0], [1]], ![[0], [7], [2], [2, 3, 3, 6], [0, 3, 3, 4], [2, 3, 3, 2], [0, 4, 5], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 437 ⟨![[], [1, 0, 0, 0], [2], [0, 0, 0], [], [0, 1, 0, 0], [2, 3, 5], [0]], ![[7], [1, 7], [2], [1, 1, 3, 3, 6, 6], [1, 1, 3, 3], [1, 1, 3, 2, 6, 3], [5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 428 ⟨![[0], [1], [], [0, 2, 0], [0, 1, 1, 6], [0, 1, 0], [3, 4, 7], [2]], ![[0], [1], [7], [1, 1, 3, 3, 6], [1, 3, 1, 7], [1, 3, 3, 5, 6], [5, 1], [0, 6, 0, 6], [0, 6, 0, 6], [0, 6, 0, 6]]⟩, .edge 435 ⟨![[], [1], [0, 0, 2, 0], [0, 0, 0], [], [0, 1, 0], [0, 5, 2, 6], [0]], ![[7], [1], [2, 7], [1, 1, 3, 2, 2, 3], [1, 5, 3, 3], [1, 1, 3, 3, 6, 2], [5, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 431 ⟨![[0], [], [1, 5, 2], [1, 1, 1], [0, 3, 5, 7], [1, 4, 6, 1], [1, 5, 2, 6], [1]], ![[0], [7], [2, 7], [2, 2, 3, 3, 5], [0, 3, 3, 4], [3, 3, 6, 2], [0, 4, 5], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 439 ⟨![[], [0, 2, 2, 1], [0, 0, 2, 0], [0, 0, 0], [], [0, 1, 0, 0], [0, 5, 2, 6], [0]], ![[7], [1, 7], [2, 7], [1, 1, 3, 3, 6, 2], [1, 1, 3, 3], [1, 1, 3, 2, 2, 3], [5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 39) : Classified H :=
  classify_of_checks 39 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node39

namespace Node40

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 3, 0, 2, 2, 3], [3, 0, 3, 0], [0, 3, 2, 0, 2, 3], [1, 1, 2, 2], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 39) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 40 :=
  generated_of_packed 39 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 446 ⟨![[], [0], [1], [2], [], [0, 0, 0, 7], [1, 3, 5], [2, 2, 2, 4]], ![[1], [2], [3], [2, 2, 7, 3], [3, 7], [2, 6, 7, 3], [1, 1, 2, 2], [1, 5], [1, 5], [1, 5]]⟩, .core, .edge 450 ⟨![[], [0, 3, 4, 6], [1], [2], [], [0], [1, 3, 5], [2, 2, 2, 4]], ![[5], [2], [3], [2, 2, 7, 3], [3, 7], [2, 6, 7, 3], [1, 2, 2, 5], [1, 1], [1, 1], [1, 1]]⟩, .edge 441 ⟨![[0], [1], [], [2], [0, 3, 5, 7], [1, 1, 1, 5], [1, 1, 6], [4, 2, 6]], ![[0], [1], [3], [0, 3, 0, 3, 6], [0, 7, 0, 7], [1, 5], [1, 1, 6], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 448 ⟨![[], [1], [0, 3, 5], [2], [], [1, 1, 1, 7], [0], [0, 0, 2, 6]], ![[6], [1], [3], [2, 3, 7, 6], [3, 7], [2, 2, 7, 3], [1, 1, 2, 6], [1, 5], [1, 5], [1, 5]]⟩, .edge 444 ⟨![[0], [], [5, 1], [2], [0, 3, 4, 6], [1, 1, 5, 6], [1], [4, 2, 6]], ![[0], [6], [3], [2, 2, 3, 7], [0, 6, 4, 6], [2, 2, 6, 2], [2, 5, 6], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 452 ⟨![[], [0, 0, 1, 0], [0, 3, 5], [2], [], [0, 1, 5, 6], [0], [0, 0, 2, 6]], ![[6], [1, 6], [3], [2, 3, 7, 6], [3, 7], [2, 2, 7, 3], [1, 2, 6, 5], [1, 1], [1, 1], [1, 1]]⟩, .edge 440 ⟨![[0], [1], [2], [], [0, 4, 5, 6], [1, 4, 6], [2, 4, 6], [5, 6, 7]], ![[0], [1], [2], [1, 7, 5, 7], [0, 7, 4], [0, 2, 4, 2, 7], [1, 1, 2, 2], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 447 ⟨![[], [1], [2], [4, 5, 6, 0], [], [0, 1, 6, 0], [2, 3, 5], [0]], ![[7], [1], [2], [2, 2, 7, 7], [3, 3], [2, 6, 7, 7], [1, 1, 2, 2], [1, 5], [1, 5], [1, 5]]⟩, .edge 443 ⟨![[0], [], [2], [1, 3], [0, 3, 4, 6], [2, 2, 6], [2, 1, 1, 4], [1]], ![[0], [7], [2], [2, 6, 3, 3], [0, 2, 4, 6], [2, 3, 6, 3], [2, 2, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 451 ⟨![[], [0, 0, 1, 0], [2], [4, 5, 6, 0], [], [0, 2, 1, 2], [2, 3, 5], [0]], ![[7], [1, 7], [2], [2, 2, 7, 7], [3, 3], [2, 6, 7, 7], [1, 2, 2, 5], [1, 1], [1, 1], [1, 1]]⟩, .edge 442 ⟨![[0], [1], [], [2, 3, 6], [0, 2, 2, 7], [1, 1, 1, 5], [1, 1, 6], [2]], ![[0], [1], [7], [1, 5, 7, 7], [1, 3, 1, 7], [1, 5], [1, 1, 6], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 449 ⟨![[], [1], [4, 2, 0], [4, 5, 6, 0], [], [0, 1, 6, 0], [0, 4, 2, 5], [0]], ![[7], [1], [2, 7], [2, 3, 3, 6], [3, 3], [2, 2, 7, 7], [1, 1, 2, 6], [1, 5], [1, 5], [1, 5]]⟩, .edge 445 ⟨![[0], [], [1, 2, 4], [1, 3], [0, 3, 4, 6], [3, 4, 6, 7], [1, 4, 2, 5], [1]], ![[0], [7], [2, 7], [2, 3, 6, 3], [0, 6, 4, 6], [2, 2, 6, 2], [2, 5, 6], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 453 ⟨![[], [0, 0, 1, 0], [4, 2, 0], [4, 5, 6, 0], [], [1, 3, 0, 6], [0, 4, 2, 5], [0]], ![[7], [1, 7], [2, 7], [2, 3, 3, 6], [3, 3], [2, 2, 7, 7], [1, 2, 6, 5], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 40) : Classified H :=
  classify_of_checks 40 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node40

namespace Node41

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [1, 0, 1, 0, 1, 1], [1, 0, 1, 0], [0, 0, 0, 0], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 40) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 41 :=
  generated_of_packed 40 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 456 ⟨![[], [0], [1], [2], [0, 2, 3], [2, 1]], ![[1], [2], [3], [1, 1, 1, 4, 3], [1, 4, 3], [3, 3], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 458 ⟨![[], [0, 3, 5], [1], [2], [0], [2, 1]], ![[4], [2], [3], [1, 1, 1, 4], [1, 1], [3, 3], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 454 ⟨![[0], [1], [], [0, 2, 5], [2, 1], []], ![[0], [1], [0, 0], [0, 1, 1, 4, 3, 1], [1, 0, 1, 0], [0, 0, 0, 0], [0, 1, 1, 0, 1, 4], [0, 1, 1, 0, 1, 4], [0, 1, 1, 0, 1, 4], [0, 1, 1, 0, 1, 4]]⟩, .edge 457 ⟨![[], [1], [0], [2], [1, 2, 3], [0]], ![[2], [1], [3], [1, 1, 1, 4, 3], [1, 4, 3], [3, 3], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 455 ⟨![[0], [], [1, 1, 1], [0, 2, 3, 6], [3, 4], [1]], ![[0], [5], [0, 0], [2, 3, 0, 5], [3, 4, 0], [4, 4], [0, 2, 2, 0, 4], [0, 2, 2, 0, 4], [0, 2, 2, 0, 4], [0, 2, 2, 0, 4]]⟩, .edge 459 ⟨![[], [1, 0], [0], [2], [0, 1, 2], [0]], ![[2], [1, 2], [3], [1, 1, 1, 4], [1, 1], [3, 3], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 41) : Classified H :=
  classify_of_checks 41 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node41

namespace Node42

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [1, 2, 1, 2], [1, 0, 1, 0], [0, 0, 0, 0], [0, 1, 0, 2, 1, 2], [0, 1, 0, 2, 1, 2], [0, 1, 0, 2, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 41) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 42 :=
  generated_of_packed 41 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 462 ⟨![[], [0], [1], [2], [0, 2, 3], [1, 4, 6]], ![[1], [2], [3], [1, 2, 1, 2], [1, 4, 3], [3, 3], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 464 ⟨![[], [0, 3, 5], [1], [2], [0], [0, 0, 1]], ![[4], [2], [3], [1, 1, 1, 4], [1, 1], [3, 3], [1, 1, 2, 5], [1, 1, 2, 5], [1, 1, 2, 5], [1, 1, 2, 5]]⟩, .edge 460 ⟨![[0], [1], [], [0, 4], [1, 4], []], ![[0], [1], [0, 0], [1, 4], [0, 1, 3, 4], [0, 0, 0, 0], [0, 1, 0, 4], [0, 1, 0, 4], [0, 1, 0, 4], [0, 1, 0, 4]]⟩, .edge 463 ⟨![[], [1], [0, 0, 0, 5], [2], [1, 2, 3], [0]], ![[5], [1], [3], [1, 2, 4, 5], [1, 4, 3], [3, 3], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 461 ⟨![[0], [], [1, 3, 5], [0, 2, 3, 6], [3, 4], [1]], ![[0], [5], [0, 0], [5, 5], [2, 2, 4], [4, 4], [0, 2, 2, 3], [0, 2, 2, 3], [0, 2, 2, 3], [0, 2, 2, 3]]⟩, .edge 465 ⟨![[], [0, 0, 1, 0], [0, 0, 0, 5], [2], [0, 1, 4], [0]], ![[5], [1, 5], [3], [1, 1, 1, 4], [1, 1], [3, 3], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 42) : Classified H :=
  classify_of_checks 42 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node42

namespace Node43

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [1, 2, 2, 1], [1, 0, 1, 0], [0, 0, 0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 42) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 43 :=
  generated_of_packed 42 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 468 ⟨![[], [0], [1], [2], [0, 2, 3], [1, 1, 2, 1]], ![[1], [2], [3], [1, 1, 5, 5], [5, 5], [3, 3], [2, 5, 3], [2, 5, 3], [2, 5, 3], [2, 5, 3]]⟩, .core, .edge 470 ⟨![[], [0, 3, 5], [1], [2], [0], [0, 0, 2, 1]], ![[4], [2], [3], [1, 1, 1, 4], [1, 1], [3, 3], [2, 5, 3], [2, 5, 3], [2, 5, 3], [2, 5, 3]]⟩, .edge 466 ⟨![[0], [1], [], [0, 2, 4, 5], [2, 1, 4], [4, 6]], ![[0], [1], [0, 0], [1, 5, 1], [0, 3], [0, 0, 0, 0], [0, 3, 5], [0, 3, 5], [0, 3, 5], [0, 3, 5]]⟩, .edge 469 ⟨![[], [1], [4, 0], [2], [1, 2, 3], [0]], ![[5], [1], [3], [1, 1, 5, 2], [5, 2], [3, 3], [5, 5], [5, 5], [5, 5], [5, 5]]⟩, .edge 467 ⟨![[0], [], [0, 1, 4, 0], [0, 2, 3, 6], [3, 4], [1]], ![[0], [5], [0, 0], [2, 4, 5], [5, 2], [4, 4], [0, 2, 3, 5], [0, 2, 3, 5], [0, 2, 3, 5], [0, 2, 3, 5]]⟩, .edge 471 ⟨![[], [1, 0, 6], [4, 0], [2], [0, 2, 1], [0]], ![[5], [1, 5], [3], [1, 1, 1, 4], [1, 1], [3, 3], [5, 5], [5, 5], [5, 5], [5, 5]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 43) : Classified H :=
  classify_of_checks 43 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node43

namespace Node44

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [1, 1], [0, 1, 0, 1], [0, 0, 0, 0], [0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 43) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 44 :=
  generated_of_packed 43 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 474 ⟨![[], [0], [1], [2], [3, 4, 0, 2], [2, 1]], ![[1], [2], [3], [1, 1], [4, 3, 1], [3, 3], [1, 2, 4, 2], [1, 2, 4, 2], [1, 2, 4, 2], [1, 2, 4, 2]]⟩, .core, .edge 476 ⟨![[], [3, 0, 4], [1], [2], [0], [2, 1]], ![[4], [2], [3], [1, 4], [1, 1], [3, 3], [1, 2, 1, 2], [1, 2, 1, 2], [1, 2, 1, 2], [1, 2, 1, 2]]⟩, .edge 472 ⟨![[0], [1], [], [0, 2, 5], [2, 4, 1], []], ![[0], [1], [0, 0], [1, 1], [0, 1, 0, 1], [0, 0, 0, 0], [0, 1, 3, 4], [0, 1, 3, 4], [0, 1, 3, 4], [0, 1, 3, 4]]⟩, .edge 475 ⟨![[], [1], [0], [2], [3, 4, 1, 2], [0]], ![[2], [1], [3], [1, 1], [4, 3, 1], [3, 3], [2, 4, 2, 4], [2, 4, 2, 4], [2, 4, 2, 4], [2, 4, 2, 4]]⟩, .edge 473 ⟨![[0], [], [1, 1, 1], [0, 1, 1, 5], [3], [1]], ![[0], [5], [0, 0], [4], [0, 3, 4], [4, 4], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 477 ⟨![[], [1, 0], [0], [2], [0, 1, 2, 4], [0]], ![[2], [1, 2], [3], [1, 4], [1, 1], [3, 3], [1, 2, 4, 2, 3], [1, 2, 4, 2, 3], [1, 2, 4, 2, 3], [1, 2, 4, 2, 3]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 44) : Classified H :=
  classify_of_checks 44 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node44

namespace Node45

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [0, 2, 0, 1, 1, 2], [1, 0, 1, 0], [0, 0, 0, 0], [0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 44) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 45 :=
  generated_of_packed 44 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 480 ⟨![[], [0], [1], [2], [0, 3, 5], [1, 4, 6]], ![[1], [2], [3], [4, 1, 4, 4], [1, 3, 4], [3, 3], [1, 2, 3, 5, 4], [1, 2, 3, 5, 4], [1, 2, 3, 5, 4], [1, 2, 3, 5, 4]]⟩, .core, .edge 482 ⟨![[], [0, 2, 3], [1], [2], [0], [0, 0, 1]], ![[4], [2], [3], [1, 2, 3, 5, 4], [1, 1, 3, 3], [3, 3], [2, 4, 2, 4], [2, 4, 2, 4], [2, 4, 2, 4], [2, 4, 2, 4]]⟩, .edge 478 ⟨![[0], [1], [], [0, 4], [1, 6], []], ![[0], [1], [0, 0], [0, 3, 1, 1], [0, 1, 0, 4], [0, 0, 0, 0], [0, 1, 3, 4], [0, 1, 3, 4], [0, 1, 3, 4], [0, 1, 3, 4]]⟩, .edge 481 ⟨![[], [1], [0, 0, 0, 5], [2], [1, 3, 5], [0]], ![[5], [1], [3], [1, 1, 5, 5], [1, 3, 4], [3, 3], [1, 5, 1, 5], [1, 5, 1, 5], [1, 5, 1, 5], [1, 5, 1, 5]]⟩, .edge 479 ⟨![[0], [], [1, 1, 1], [3, 0, 6], [1, 1, 6], [1]], ![[0], [5], [0, 0], [3, 5, 0, 5], [3, 4, 0], [0, 0, 0, 0], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 483 ⟨![[], [0, 2, 1, 3], [0, 0, 0, 5], [2], [0, 1, 6], [0]], ![[5], [1, 5], [3], [1, 4, 5, 5], [2, 2, 3], [3, 3], [1, 1, 5, 3, 5], [1, 1, 5, 3, 5], [1, 1, 5, 3, 5], [1, 1, 5, 3, 5]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 45) : Classified H :=
  classify_of_checks 45 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node45

namespace Node46

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [1, 1], [0, 1, 0, 1], [0, 0, 0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 45) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 46 :=
  generated_of_packed 45 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 486 ⟨![[], [0], [1], [2], [3, 4, 0, 2], [1, 1, 2, 1]], ![[1], [2], [3], [1, 1], [5, 5], [3, 3], [2, 5, 3], [2, 5, 3], [2, 5, 3], [2, 5, 3]]⟩, .core, .edge 488 ⟨![[], [3, 0, 4], [1], [2], [0], [1, 1, 2, 1]], ![[4], [2], [3], [1, 4], [1, 1], [3, 3], [2, 5, 3], [2, 5, 3], [2, 5, 3], [2, 5, 3]]⟩, .edge 484 ⟨![[0], [1], [], [1, 0, 1], [1, 2, 5], [4, 6]], ![[0], [1], [0, 0], [1, 1], [0, 3], [0, 0, 0, 0], [0, 3, 5], [0, 3, 5], [0, 3, 5], [0, 3, 5]]⟩, .edge 487 ⟨![[], [1], [4, 0], [2], [3, 4, 1, 2], [0]], ![[5], [1], [3], [1, 1], [5, 2], [3, 3], [5, 5], [5, 5], [5, 5], [5, 5]]⟩, .edge 485 ⟨![[0], [], [0, 1, 0], [1, 1, 0], [3], [1]], ![[0], [5], [0, 0], [4], [5, 2], [4, 4], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 489 ⟨![[], [1, 0, 6], [4, 0], [2], [0, 2, 4, 1], [0]], ![[5], [1, 5], [3], [1, 4], [1, 1], [3, 3], [5, 5], [5, 5], [5, 5], [5, 5]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 46) : Classified H :=
  classify_of_checks 46 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node46

namespace Node47

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0, 0, 1, 0, 1], [0, 2, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2], [0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 46) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 47 :=
  generated_of_packed 46 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 491 ⟨![[0], [], [1], [2, 0], [], [1, 4, 6]], ![[0], [2], [0, 0, 0, 3], [0, 2, 0, 2], [0, 2, 3, 0, 5, 3], [0, 0, 0, 0], [0, 3, 0, 5, 3, 2], [0, 3, 0, 5, 3, 2], [0, 3, 0, 5, 3, 2], [0, 3, 0, 5, 3, 2]]⟩, .edge 494 ⟨![[], [0, 0, 0], [1], [3, 4], [0], [1, 4, 6]], ![[4], [2], [1, 1, 3], [2, 3, 5], [1, 2, 4, 5], [3, 3], [1, 2, 4, 2], [1, 2, 4, 2], [1, 2, 4, 2], [1, 2, 4, 2]]⟩, .edge 490 ⟨![[0], [1], [], [0, 4], [1, 4, 6], []], ![[0], [1], [0, 0, 0, 1, 0, 1], [0, 3], [0, 0, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 0, 0, 3, 3]]⟩, .edge 493 ⟨![[], [1], [0, 3, 5], [3, 4], [1, 2], [0]], ![[5], [1], [1, 4], [5, 5], [2, 2, 3], [3, 3], [1, 2, 4, 2, 3], [1, 2, 4, 2, 3], [1, 2, 4, 2, 3], [1, 2, 4, 2, 3]]⟩, .edge 492 ⟨![[0], [], [1, 1, 1], [2, 0], [], [1]], ![[0], [5], [0, 0, 0, 3], [0, 2, 2, 0], [0, 2, 0, 3, 2, 3], [0, 0, 0, 0], [0, 3, 0, 5, 0, 5], [0, 3, 0, 5, 0, 5], [0, 3, 0, 5, 0, 5], [0, 3, 0, 5, 0, 5]]⟩, .edge 495 ⟨![[], [0, 2, 1, 3], [0, 3, 5], [3, 4], [4, 0, 1], [0]], ![[5], [1, 5], [1, 1, 3], [5, 5], [2, 2, 3], [3, 3], [1, 2, 1, 3, 5], [1, 2, 1, 3, 5], [1, 2, 1, 3, 5], [1, 2, 1, 3, 5]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 47) : Classified H :=
  classify_of_checks 47 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node47

namespace Node48

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 2, 1, 2], [1, 0, 1, 0, 3, 3], [3, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 47) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 48 :=
  generated_of_packed 47 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 502 ⟨![[], [0], [1], [2], [], [0, 3], [1, 6], [2, 5]], ![[1], [2], [3], [1, 2, 1, 2], [1, 3, 3, 5], [3, 3], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .core, .edge 506 ⟨![[], [0, 3], [1], [2], [], [0], [1, 6], [2, 5]], ![[5], [2], [3], [1, 2, 5, 6], [1, 1, 3, 3], [3, 3], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 497 ⟨![[0], [1], [], [2], [0, 6], [1, 4], [], [2, 6]], ![[0], [1], [3], [1, 5], [0, 1, 0, 1, 3, 7], [3, 3], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 504 ⟨![[], [1], [0, 6], [2], [], [1, 3], [0], [2, 5]], ![[6], [1], [3], [1, 2, 5, 6], [1, 3, 3, 5], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 500 ⟨![[0], [], [1, 3, 5], [2], [0, 3, 6], [3, 4], [1], [2, 5]], ![[0], [6], [3], [6, 6], [0, 5, 4], [3, 3], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6]]⟩, .edge 508 ⟨![[], [1, 0, 6], [0, 6], [2], [], [0, 1, 4], [0], [2, 5]], ![[6], [1, 6], [3], [1, 2, 1, 2], [1, 1, 3, 3], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 496 ⟨![[0], [1], [2], [], [0, 5], [1, 5], [2, 6], [5]], ![[0], [1], [2], [1, 2, 1, 2], [1, 0, 1, 4], [7], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 503 ⟨![[], [1], [2], [0, 5], [], [1, 3], [2, 6], [0]], ![[7], [1], [2], [1, 2, 1, 2], [1, 3, 1, 3], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 499 ⟨![[0], [], [2], [1, 1, 1], [0, 3, 6], [1, 1], [2, 4, 6], [1]], ![[0], [7], [2], [2, 5, 6], [0, 5, 4], [3, 7], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 507 ⟨![[], [1, 0], [2], [0, 5], [], [0, 1], [2, 6], [0]], ![[7], [1, 7], [2], [1, 2, 5, 6], [1, 1, 3, 7], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 498 ⟨![[0], [1], [], [2, 6], [0, 6], [1, 4], [], [2]], ![[0], [1], [7], [1, 5], [0, 1, 0, 1, 3, 3], [3, 7], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 505 ⟨![[], [1], [2, 0], [0, 5], [], [1, 3], [2, 0, 6], [0]], ![[7], [1], [2, 7], [1, 2, 5, 6], [1, 3, 1, 3], [3, 7], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 501 ⟨![[0], [], [1, 3, 2], [1, 1, 1], [0, 3, 6], [1, 1], [2, 1, 4], [1]], ![[0], [7], [2, 7], [6, 6], [0, 5, 4], [3, 7], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6]]⟩, .edge 509 ⟨![[], [1, 0], [2, 0], [0, 5], [], [0, 1], [2, 0, 6], [0]], ![[7], [1, 7], [2, 7], [1, 2, 1, 2], [1, 1, 3, 7], [3, 7], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 48) : Classified H :=
  classify_of_checks 48 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node48

namespace Node49

def gen : Fin 5 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [3], [4]],
   ![[0], [1], [2], [3], [4], [0, 2, 0, 2], [3, 3], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 48) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 49 :=
  generated_of_packed 48 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .core, .edge 517 ⟨![[0], [], [1], [2], [3], [0], [], [0, 0, 1], [2, 5], [3]], ![[0], [2], [3], [4], [0, 2, 0, 2], [3, 3], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7]]⟩, .edge 532 ⟨![[], [0, 0, 0], [1], [2], [3], [0, 0], [0], [1, 6], [2, 5], [3, 5, 6]], ![[6], [2], [3], [4], [2, 5, 7], [3, 3], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 513 ⟨![[0], [1], [], [2], [3], [0, 6], [0, 0, 1], [], [2, 6], [3, 6]], ![[0], [1], [3], [4], [0, 5], [3, 3], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 528 ⟨![[], [1], [0, 4], [2], [3], [4, 6], [1], [0], [2, 5], [3, 5, 6]], ![[7], [1], [3], [4], [2, 2], [3, 3], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 521 ⟨![[0], [], [0, 0, 1], [2], [3], [0], [], [1], [2, 5], [3]], ![[0], [7], [3], [4], [0, 2, 0, 7], [3, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 536 ⟨![[], [0, 1], [0, 4], [2], [3], [1, 1], [1, 0, 6], [0], [2, 5], [3, 5, 6]], ![[7], [1, 7], [3], [4], [2, 2], [3, 3], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 511 ⟨![[0], [1], [2], [], [3], [0, 5], [1, 5], [2, 6], [5], [3]], ![[0], [1], [2], [4], [0, 0, 2, 7], [8], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 526 ⟨![[], [1], [2], [0, 0, 0, 5], [3], [0, 0], [1], [2, 6], [0], [3, 5, 6]], ![[8], [1], [2], [4], [2, 5, 7], [3, 8], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 519 ⟨![[0], [], [2], [1, 5], [3], [0], [], [0, 0, 2], [1], [3]], ![[0], [8], [2], [4], [0, 2, 0, 2], [3, 8], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7]]⟩, .edge 534 ⟨![[], [0, 0, 0, 1], [2], [0, 0, 0, 5], [3], [0, 0], [0, 1], [2, 6], [0], [3, 5, 6]], ![[8], [1, 8], [2], [4], [2, 5, 7], [3, 8], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 515 ⟨![[0], [1], [], [2, 6], [3], [0, 6], [0, 0, 1], [], [2], [3, 6]], ![[0], [1], [8], [4], [0, 5], [3, 8], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 530 ⟨![[], [1], [0, 0, 2, 0], [0, 0, 0, 5], [3], [0, 0], [1], [2, 0, 6], [0], [2, 2, 3]], ![[8], [1], [2, 8], [4], [2, 2], [3, 8], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 523 ⟨![[0], [], [2, 1], [1, 5], [3], [0], [], [0, 0, 2, 1], [1], [3]], ![[0], [8], [2, 8], [4], [0, 2, 0, 7], [3, 8], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 538 ⟨![[], [0, 0, 0, 1], [0, 0, 2, 0], [0, 0, 0, 5], [3], [0, 0], [0, 1], [2, 0, 6], [0], [2, 2, 3]], ![[8], [1, 8], [2, 8], [4], [2, 2], [3, 8], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 510 ⟨![[0], [1], [2], [3], [], [0, 5, 6], [1], [2, 6], [3], [5]], ![[0], [1], [2], [3], [0, 5, 9], [9], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 525 ⟨![[], [1], [2], [3], [0, 4, 5], [4, 6], [1], [2, 6], [3, 5], [0]], ![[9], [1], [2], [3], [4, 4], [3, 3], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 518 ⟨![[0], [], [2], [3], [1], [0], [], [0, 0, 2], [3, 5], [1]], ![[0], [4], [2], [3], [0, 2, 0, 2], [3, 3], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7]]⟩, .edge 533 ⟨![[], [1, 0, 4], [2], [3], [0, 4, 5], [4, 6], [0, 1, 5], [2, 6], [3, 5], [0]], ![[9], [1, 9], [2], [3], [4, 4], [3, 3], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 514 ⟨![[0], [1], [], [3], [2, 6], [0, 6], [0, 0, 1], [], [3, 6], [2]], ![[0], [1], [9], [3], [0, 5], [3, 3], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 529 ⟨![[], [1], [2, 0, 4], [3], [0, 4, 5], [4, 6], [1], [2, 0], [3, 5], [0]], ![[9], [1], [2, 9], [3], [2, 2], [3, 3], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 522 ⟨![[0], [], [2, 1, 5], [3], [1], [0], [], [0, 2, 0, 1], [3, 5], [1]], ![[0], [4], [2, 4], [3], [0, 2, 0, 7], [3, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 537 ⟨![[], [1, 0, 4], [2, 0, 4], [3], [0, 4, 5], [4, 6], [0, 1, 5], [2, 0], [3, 5], [0]], ![[9], [1, 9], [2, 9], [3], [2, 2], [3, 3], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 512 ⟨![[0], [1], [2], [], [3, 5], [0, 5], [1, 5], [2, 6], [5], [3]], ![[0], [1], [2], [9], [0, 0, 2, 7], [8], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 527 ⟨![[], [1], [2], [3, 0, 4], [0, 4, 5], [4, 6], [1], [2, 6], [0, 3, 5], [0]], ![[9], [1], [2], [3, 9], [4, 4], [3, 8], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 520 ⟨![[0], [], [2], [1, 3], [1], [0], [], [0, 0, 2], [3, 1], [1]], ![[0], [4], [2], [3, 4], [0, 2, 0, 2], [3, 8], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7], [0, 2, 0, 7]]⟩, .edge 535 ⟨![[], [1, 0, 4], [2], [3, 0, 4], [0, 4, 5], [4, 6], [0, 1, 5], [2, 6], [0, 3, 5], [0]], ![[9], [1, 9], [2], [3, 9], [4, 4], [3, 8], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 516 ⟨![[0], [1], [], [2, 2, 2, 3], [2, 6], [0, 6], [0, 0, 1], [], [2, 3, 5], [2]], ![[0], [1], [9], [3, 9], [0, 5], [3, 8], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 531 ⟨![[], [1], [2, 0, 4], [3, 0, 4], [0, 4, 5], [4, 6], [1], [2, 0], [0, 3, 5], [0]], ![[9], [1], [2, 9], [3, 9], [2, 2], [3, 8], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 524 ⟨![[0], [], [2, 1, 5], [1, 3], [1], [0], [], [0, 2, 0, 1], [3, 1], [1]], ![[0], [4], [2, 4], [3, 4], [0, 2, 0, 7], [3, 8], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 539 ⟨![[], [1, 0, 4], [2, 0, 4], [3, 0, 4], [0, 4, 5], [4, 6], [0, 1, 5], [2, 0], [0, 3, 5], [0]], ![[9], [1, 9], [2, 9], [3, 9], [2, 2], [3, 8], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 5 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 49) : Classified H :=
  classify_of_checks 49 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node49

end ReeTwo.SylowModel.SmallEvenMaximalLower
