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

namespace Node175

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0], [1, 0, 1, 0], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 174) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 175 :=
  generated_of_packed 174 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .noncentric 96, .core, .edge 1811 ⟨![[], [2, 0, 1], [1], [0]], ![[3], [2], [3, 2, 1], [2, 2], [1, 2, 1, 2], [1, 1, 2, 2], [1, 1, 2, 2], [1, 1, 2, 2], [1, 1, 2, 2], [1, 1, 2, 2]]⟩] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 175) : Classified H :=
  classify_of_checks 175 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node175

namespace Node176

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [0, 0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 0], [0, 0, 1, 1, 0, 1, 1, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 175) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 176 :=
  generated_of_packed 175 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .noncentric 96, .core, .edge 1812 ⟨![[], [1, 2, 0], [1], [0]], ![[3], [2], [3, 2, 1], [2, 2], [1, 1, 2, 2, 3, 3], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 176) : Classified H :=
  classify_of_checks 176 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node176

namespace Node177

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [2, 0, 0, 2, 2], [2, 2], [0, 0, 0, 2, 0, 2, 2, 2], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 176) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 177 :=
  generated_of_packed 176 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .noncentric 96, .noncentric 96, .edge 1813 ⟨![[0], [1], [], [0, 4], [1, 5], [3, 5]], ![[0], [1], [0, 0], [1, 4, 5], [0, 0, 0, 3], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4]]⟩, .edge 1814 ⟨![[], [1], [3, 4, 0], [2], [1, 5], [2, 0, 3]], ![[2, 2, 2, 3], [1], [3], [1, 2, 4, 5], [2, 2, 2, 5, 3], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4]]⟩, .noncentric 96, .noncentric 96] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 177) : Classified H :=
  classify_of_checks 177 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node177

namespace Node178

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 1, 0, 1, 0, 0], [0, 0], [0, 1, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 177) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 178 :=
  generated_of_packed 177 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .core, .edge 1815 ⟨![[0], [], [1, 0, 4], []], ![[0], [0, 2, 0, 0], [0, 0], [0, 2, 2, 0], [0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 2, 2, 0, 2, 2], [0, 0, 0, 2, 2, 0, 2, 2], [0, 0, 0, 2, 2, 0, 2, 2], [0, 0, 0, 2, 2, 0, 2, 2], [0, 0, 0, 2, 2, 0, 2, 2]]⟩, .noncentric 96] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 178) : Classified H :=
  classify_of_checks 178 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node178

namespace Node179

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0, 0, 1, 0, 1], [0, 0], [0, 0, 0, 1, 1, 0], [1, 1], [0, 0, 0, 0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 178) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 179 :=
  generated_of_packed 178 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .core, .edge 1816 ⟨![[0], [], [1, 0, 5], [4]], ![[0], [0, 2, 2, 2], [0, 0], [0, 0, 2, 2], [3], [0, 2, 0, 3, 2, 3], [0, 2, 0, 3, 2, 3], [0, 2, 0, 3, 2, 3], [0, 2, 0, 3, 2, 3], [0, 2, 0, 3, 2, 3]]⟩, .noncentric 96] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 179) : Classified H :=
  classify_of_checks 179 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node179

namespace Node180

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0, 1, 0, 0, 1], [1, 1, 0, 1, 1, 0], [1, 1, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 179) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 180 :=
  generated_of_packed 179 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .edge 1817 ⟨![[], [0], [2, 4, 5], [2, 1, 0]], ![[1], [2, 1, 2, 1], [1, 1, 3, 3, 2], [1, 1, 1, 1], [1, 3, 3, 1], [1, 1, 3, 2, 3, 2], [1, 1, 3, 2, 3, 2], [1, 1, 3, 2, 3, 2], [1, 1, 3, 2, 3, 2], [1, 1, 3, 2, 3, 2]]⟩, .core, .edge 1818 ⟨![[], [1, 0, 3], [2, 4, 5], [0]], ![[3], [1, 1, 3, 1], [1, 1, 2, 3, 3], [1, 3, 1, 3], [1, 1, 1, 2, 1, 2], [1, 1, 1, 3, 1, 3], [1, 1, 1, 3, 1, 3], [1, 1, 1, 3, 1, 3], [1, 1, 1, 3, 1, 3], [1, 1, 1, 3, 1, 3]]⟩] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 2 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 180) : Classified H :=
  classify_of_checks 180 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node180

namespace Node181

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [1, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 1], [1, 1, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 180) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 181 :=
  generated_of_packed 180 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .edge 1819 ⟨![[], [0], [2, 4, 5], [0, 1, 2, 3]], ![[1], [1, 2, 1, 2], [3, 1], [1, 1, 1, 1], [1, 2, 3], [1, 3, 2], [1, 3, 2], [1, 3, 2], [1, 3, 2], [1, 3, 2]]⟩, .core, .edge 1820 ⟨![[], [0, 1, 3], [0, 2, 0], [0]], ![[3], [1, 1, 1, 3], [3, 2, 3], [1, 3, 1, 3], [1, 1], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 2 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 181) : Classified H :=
  classify_of_checks 181 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node181

namespace Node182

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [4]],
   ![[0], [1], [0, 0, 0, 1, 1, 1, 0, 1], [0, 0], [2], [1, 0, 1, 0], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 181) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 182 :=
  generated_of_packed 181 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1821 ⟨![[], [0], [1], [3], [0, 2], [1, 5]], ![[1], [2], [1, 1, 1, 4], [3], [1, 3, 4], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .core, .edge 1822 ⟨![[], [0, 2, 3], [1], [3], [0], [1, 5]], ![[4], [2], [1, 1, 1, 3, 4], [3], [1, 1], [2, 5], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 182) : Classified H :=
  classify_of_checks 182 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node182

namespace Node183

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [0, 0, 0, 1, 0, 1, 1, 1, 2], [1, 0, 1, 0], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 182) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 183 :=
  generated_of_packed 182 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1823 ⟨![[], [0], [1, 2], [3], [0, 2, 5], [1, 2]], ![[1], [1, 1, 1, 2, 4], [1, 1, 1, 2, 4, 2], [3], [1, 3, 4], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2]]⟩, .core, .edge 1824 ⟨![[], [0, 2, 3], [1, 2], [3], [0], [1, 2]], ![[4], [1, 1, 1, 2, 3, 4], [1, 1, 1, 4, 3], [3], [1, 1], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2]]⟩, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 183) : Classified H :=
  classify_of_checks 183 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node183

namespace Node184

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 3, 3], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 183) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 184 :=
  generated_of_packed 183 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 96, .edge 1828 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 3], [0, 2, 0]], ![[5], [2], [3], [3, 3, 4], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .noncentric 2064, .edge 1827 ⟨![[], [1], [0, 2, 2], [2], [4, 5], [1], [0], [0, 2, 0]], ![[6], [1], [3], [3, 3, 4], [3, 7], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1826 ⟨![[0], [], [1, 3, 4], [2], [0], [], [1], [0, 0, 2]], ![[0], [6], [3], [3, 7], [0, 3, 0, 7], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .noncentric 2988, .noncentric 2056, .noncentric 2068, .edge 1825 ⟨![[0], [], [2], [0, 0, 1], [0], [], [2, 2, 2], [1]], ![[0], [7], [2], [3, 3], [0, 3, 0, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1829 ⟨![[], [1, 0, 5], [2], [0, 2, 2], [4, 5], [0, 1, 3], [2, 3], [0]], ![[7], [1, 7], [2], [3, 4, 7], [2, 6], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .noncentric 8, .noncentric 4, .noncentric 104, .noncentric 36] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 184) : Classified H :=
  classify_of_checks 184 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node184

namespace Node185

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 3, 3], [1, 2, 1, 2], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 184) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 185 :=
  generated_of_packed 184 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 96, .edge 1838 ⟨![[], [0, 4], [1], [2], [4, 5], [0], [1, 3], [2, 3, 5]], ![[5], [2], [3], [3, 3, 4], [2, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1831 ⟨![[0], [1], [], [2], [0, 3], [1, 2, 2], [3, 4], [2, 5]], ![[0], [1], [3], [1, 5], [1, 5, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 1837 ⟨![[], [1], [0, 2, 2], [2], [1, 1], [1, 5], [0], [0, 2, 0]], ![[6], [1], [3], [3, 3, 4], [1, 5], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1834 ⟨![[0], [], [1, 3], [2], [0, 5], [0, 0], [1], [2, 4]], ![[0], [6], [3], [3, 3, 5], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 1840 ⟨![[], [1, 0, 5], [0, 2, 2], [2], [4, 5], [0, 1, 5], [0], [0, 2, 0]], ![[6], [1, 6], [3], [3, 3, 4], [3, 7], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1830 ⟨![[0], [1], [2], [], [0, 3, 5], [1, 4], [2, 5], [0, 0, 3]], ![[0], [1], [2], [0, 0, 7], [0, 0, 1, 5], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1836 ⟨![[], [1], [2], [0, 2, 2], [1, 1], [1, 5], [2, 3], [0]], ![[7], [1], [2], [3, 4, 7], [1, 5], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 1833 ⟨![[0], [], [2], [1, 5], [0, 5], [0, 0], [0, 2, 0], [1]], ![[0], [7], [2], [3, 5, 7], [0, 4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1839 ⟨![[], [1, 0, 5], [2], [0, 1, 1], [4, 5], [0, 1, 3, 5], [2, 3], [0]], ![[7], [1, 7], [2], [3, 4, 7], [2, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1832 ⟨![[0], [1], [], [0, 0, 2, 3], [0, 3], [0, 0, 1, 3], [3, 4], [2]], ![[0], [1], [7], [1, 5], [1, 5, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .noncentric 4, .edge 1835 ⟨![[0], [], [1, 2, 4], [1, 5], [0, 5], [0, 0], [2, 1, 4], [1]], ![[0], [7], [2, 7], [3, 5, 7], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .noncentric 36] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 185) : Classified H :=
  classify_of_checks 185 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node185

namespace Node186

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 2, 2], [0, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 185) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 186 :=
  generated_of_packed 185 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 96, .edge 1850 ⟨![[], [0, 5], [1], [2], [4], [0], [1, 3, 5], [2, 3]], ![[5], [2], [3], [2, 2, 4], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1842 ⟨![[0], [1], [], [2], [0, 3, 5], [1, 3, 4], [3, 4], [2, 5]], ![[0], [1], [3], [0, 0, 6], [0, 0], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 1848 ⟨![[], [1], [0, 2, 2], [2], [4], [1, 4, 5], [0], [2, 3]], ![[6], [1], [3], [2, 4, 6], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1845 ⟨![[0], [], [1, 3, 4], [2], [0, 4, 5], [], [1], [2, 4, 5]], ![[0], [6], [3], [3, 7], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 1852 ⟨![[], [0, 1, 5], [0, 2, 2], [2], [4], [0, 1], [0], [2, 3]], ![[6], [1, 6], [3], [2, 4, 6], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1841 ⟨![[0], [1], [2], [], [0, 3], [1, 4, 5], [2, 5], [2, 2, 5]], ![[0], [1], [2], [1, 5, 7], [0, 0], [0, 4, 7], [0, 4, 7], [0, 4, 7], [0, 4, 7], [0, 4, 7]]⟩, .edge 1847 ⟨![[], [1], [2], [0, 2, 2], [4], [1, 4, 5], [0, 2, 0], [0]], ![[7], [1], [2], [2, 2, 4], [4], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 1844 ⟨![[0], [], [2], [1, 4, 5], [0, 4, 5], [], [2, 2, 2], [1]], ![[0], [7], [2], [3, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 1851 ⟨![[], [1, 0, 5], [2], [0, 2, 2], [4], [1, 0], [0, 2, 0], [0]], ![[7], [1, 7], [2], [2, 2, 4], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1843 ⟨![[0], [1], [], [0, 2, 0, 3], [0, 3, 5], [1, 3, 4], [3, 4], [2]], ![[0], [1], [7], [0, 0, 6], [0, 0], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 1849 ⟨![[], [1], [0, 2, 5], [0, 3, 4], [4], [1, 4, 5], [0, 2, 3, 4], [0]], ![[7], [1], [2, 7], [2, 4, 6], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1846 ⟨![[0], [], [1, 2], [1, 4, 5], [0, 4, 5], [], [2, 1, 4], [1]], ![[0], [7], [2, 7], [3, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 1853 ⟨![[], [1, 0, 5], [0, 2, 5], [0, 3, 4], [4], [1, 0], [0, 2, 3, 4], [0]], ![[7], [1, 7], [2, 7], [2, 4, 6], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 186) : Classified H :=
  classify_of_checks 186 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node186

namespace Node187

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 2, 2], [0, 0], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 186) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 187 :=
  generated_of_packed 186 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 96, .edge 1863 ⟨![[], [0], [1], [2], [4], [0], [1, 3, 5], [2, 3]], ![[1], [2], [3], [2, 2, 4], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 1855 ⟨![[0], [1], [], [2], [0, 3, 5], [1, 2, 2], [3, 4], [2, 5]], ![[0], [1], [3], [1, 5], [0, 0], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 1861 ⟨![[], [1], [0, 2, 2], [2], [4], [1, 4], [0], [2, 3]], ![[6], [1], [3], [2, 4, 6], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1858 ⟨![[0], [], [1, 3], [2], [0, 4], [4, 5], [1], [2, 4]], ![[0], [6], [3], [3, 3, 5], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 1865 ⟨![[], [0, 1, 5], [0, 2, 2], [2], [4], [0, 1, 5], [0], [2, 3]], ![[6], [1, 6], [3], [2, 4, 6], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1854 ⟨![[0], [1], [2], [], [0, 3], [1, 4], [2, 5], [1, 1, 3]], ![[0], [1], [2], [1, 1, 7], [0, 0], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1860 ⟨![[], [1], [2], [0, 2, 2], [4], [1, 4], [0, 2, 0], [0]], ![[7], [1], [2], [2, 2, 4], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1857 ⟨![[0], [], [2], [1, 5], [0, 4], [4, 5], [0, 2, 0], [1]], ![[0], [7], [2], [3, 5, 7], [0, 0], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1864 ⟨![[], [1, 0, 5], [2], [0, 1, 1], [4], [1, 0, 5], [0, 2, 0], [0]], ![[7], [1, 7], [2], [2, 2, 4], [4], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 1856 ⟨![[0], [1], [], [0, 2, 0, 3], [0, 3, 5], [1, 1, 1, 3], [3, 4], [2]], ![[0], [1], [7], [1, 5], [0, 0], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 1862 ⟨![[], [1], [0, 2, 5], [0, 3, 4], [4], [1, 4], [0, 1, 2, 1], [0]], ![[7], [1], [2, 7], [2, 4, 6], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1859 ⟨![[0], [], [1, 2, 4], [1, 5], [0, 4], [4, 5], [2, 1, 4], [1]], ![[0], [7], [2, 7], [3, 5, 7], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 1866 ⟨![[], [1, 0, 5], [0, 2, 5], [0, 1, 1], [4], [1, 0, 5], [0, 1, 1, 2], [0]], ![[7], [1, 7], [2, 7], [2, 4, 6], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 187) : Classified H :=
  classify_of_checks 187 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node187

namespace Node188

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 2, 3, 2, 3], [0, 2, 0, 2], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 187) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 188 :=
  generated_of_packed 187 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 96, .edge 1873 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 5], [2, 3]], ![[5], [2], [3], [1, 3, 5, 3], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 2056, .edge 1871 ⟨![[], [1], [0, 4], [2], [4, 5], [1], [0], [2, 3]], ![[6], [1], [3], [1, 3, 1, 7], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 1869 ⟨![[0], [], [0, 0, 1], [2], [0], [], [1], [2, 2, 2]], ![[0], [6], [3], [2, 3, 2, 7], [0, 2, 0, 6], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1875 ⟨![[], [0, 1], [0, 4], [2], [1, 1], [1, 0, 5], [0], [2, 3]], ![[6], [1, 6], [3], [1, 3, 5, 3], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .noncentric 16, .noncentric 4, .edge 1868 ⟨![[0], [], [2], [1, 3, 4], [0], [], [0, 0, 2], [1]], ![[0], [7], [2], [2, 3, 2, 7], [0, 2, 0, 2], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1874 ⟨![[], [1, 0, 5], [2], [0, 3, 4, 5], [4, 5], [0, 1], [2, 5], [0]], ![[7], [1, 7], [2], [1, 3, 5, 7], [2, 4, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1867 ⟨![[0], [1], [], [2, 5], [0, 5], [0, 0, 1], [], [2]], ![[0], [1], [7], [0, 0, 3, 3], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1872 ⟨![[], [1], [2, 0, 5], [0, 2, 2], [4, 5], [1], [0, 2, 2, 2], [0]], ![[7], [1], [2, 7], [2, 2, 3, 7], [2, 2], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 1870 ⟨![[0], [], [2, 1], [1, 3, 4], [0], [], [0, 0, 2, 1], [1]], ![[0], [7], [2, 7], [2, 3, 6, 3], [0, 2, 0, 6], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1876 ⟨![[], [1, 0, 5], [2, 0, 5], [0, 2, 2], [4, 5], [0, 1], [0, 2, 2, 2], [0]], ![[7], [1, 7], [2, 7], [1, 3, 5, 7], [2, 2], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 188) : Classified H :=
  classify_of_checks 188 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node188

namespace Node189

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 3, 3], [0, 2, 0, 2], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 188) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 189 :=
  generated_of_packed 188 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 96, .edge 1884 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 5], [0, 2, 0]], ![[5], [2], [3], [3, 3, 4], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 2064, .edge 1882 ⟨![[], [1], [0, 4], [2], [4, 5], [1], [0], [2, 3, 5]], ![[6], [1], [3], [3, 3, 4], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 1879 ⟨![[0], [], [0, 0, 1], [2], [0], [], [1], [0, 0, 2]], ![[0], [6], [3], [3, 7], [0, 2, 0, 6], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1885 ⟨![[], [0, 1], [0, 4], [2], [1, 1], [1, 0, 5], [0], [2, 3, 5]], ![[6], [1, 6], [3], [3, 3, 4], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .noncentric 16, .edge 1881 ⟨![[], [1], [2], [0, 3, 4], [4, 5], [1], [2, 5], [0]], ![[7], [1], [2], [3, 4, 7], [2, 4, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1878 ⟨![[0], [], [2], [0, 0, 1], [0], [], [0, 0, 2], [1]], ![[0], [7], [2], [3, 3], [0, 2, 0, 2], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .noncentric 36, .edge 1877 ⟨![[0], [1], [], [2, 5], [0, 5], [0, 0, 1], [], [2]], ![[0], [1], [7], [0, 0, 3, 7], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1883 ⟨![[], [1], [0, 2, 3], [0, 2, 2], [4, 5], [1], [0, 2, 2, 2], [0]], ![[7], [1], [2, 7], [3, 4, 7], [2, 2], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 1880 ⟨![[0], [], [2, 1, 3], [0, 0, 1], [0], [], [0, 1, 0, 2], [1]], ![[0], [7], [2, 7], [3, 3], [0, 2, 0, 6], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1886 ⟨![[], [1, 0, 5], [0, 2, 3], [0, 2, 2], [4, 5], [0, 1, 3], [0, 2, 2, 2], [0]], ![[7], [1, 7], [2, 7], [3, 4, 7], [2, 2], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 189) : Classified H :=
  classify_of_checks 189 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node189

namespace Node190

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 0, 1, 3, 0, 1, 3], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 189) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 190 :=
  generated_of_packed 189 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1889 ⟨![[0], [], [1], [2], [0], [], [1], [1, 1, 2]], ![[0], [2], [3], [0, 0, 0, 3, 0, 7], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1896 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 3], [2, 3]], ![[5], [2], [3], [1, 3, 5, 3], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .noncentric 2056, .edge 1894 ⟨![[], [1], [0, 2, 2, 5], [2], [4, 5], [1], [0], [2, 3]], ![[6], [1], [3], [1, 3, 1, 7], [3, 7], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1891 ⟨![[0], [], [1], [2], [0], [], [1], [1, 1, 2]], ![[0], [2], [3], [0, 0, 0, 3, 0, 7], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1898 ⟨![[], [1, 0, 5], [0, 1, 1, 5], [2], [4, 5], [1, 0, 4], [0], [2, 3]], ![[6], [1, 6], [3], [1, 3, 5, 3], [3, 7], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1887 ⟨![[0], [1], [2], [], [0, 3], [1, 2, 2], [2], [2, 2]], ![[0], [1], [2], [0, 0, 0, 4], [0, 0, 0, 4, 7], [0, 4, 7], [0, 4, 7], [0, 4, 7], [0, 4, 7], [0, 4, 7]]⟩, .edge 1893 ⟨![[], [1], [2], [0, 2, 2, 5], [4, 5], [1], [2, 3], [0]], ![[7], [1], [2], [2, 2, 2, 6], [2, 6], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 1890 ⟨![[0], [], [2], [1, 2, 2], [0], [], [2], [1]], ![[0], [7], [2], [0, 0, 0, 3, 0, 3], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1897 ⟨![[], [1, 0, 5], [2], [0, 2, 2, 5], [4, 5], [0, 1], [2, 3], [0]], ![[7], [1, 7], [2], [1, 3, 5, 7], [2, 6], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 1888 ⟨![[0], [1], [], [1, 2, 1], [0, 3], [1], [3, 4], [2]], ![[0], [1], [7], [0, 0, 0, 4], [0, 0, 0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 1895 ⟨![[], [1], [0, 2, 5], [0, 3, 4, 5], [4, 5], [1], [0, 1, 2, 1], [0]], ![[7], [1], [2, 7], [1, 3, 1, 3, 4], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1892 ⟨![[0], [], [2, 1], [1, 3, 4], [0], [], [2, 1], [1]], ![[0], [7], [2, 7], [0, 0, 0, 3, 0, 3], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .noncentric 36] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 190) : Classified H :=
  classify_of_checks 190 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node190

namespace Node191

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 2, 2], [1, 2, 1, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 190) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 191 :=
  generated_of_packed 190 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1901 ⟨![[0], [], [1], [2], [0], [], [1, 3, 5], [0, 0, 2]], ![[0], [2], [3], [3, 7], [2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 1907 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 3, 5], [0, 2, 0]], ![[5], [2], [3], [2, 2, 4], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .noncentric 2064, .edge 1906 ⟨![[], [1], [0, 3, 4], [2], [4, 5], [1], [0], [2, 3, 5]], ![[6], [1], [3], [2, 4, 6], [3, 7], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1903 ⟨![[0], [], [1, 3, 5], [2], [0], [], [1], [0, 0, 2]], ![[0], [6], [3], [3, 7], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 1909 ⟨![[], [0, 1, 5], [0, 3, 4], [2], [4, 5], [0, 1, 4], [0], [2, 3, 5]], ![[6], [1, 6], [3], [2, 4, 6], [3, 7], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1899 ⟨![[0], [1], [2], [], [0, 3, 5], [0, 0, 1], [2], [2, 2]], ![[0], [1], [2], [0, 0, 7], [1, 2, 1, 2], [0, 4, 7], [0, 4, 7], [0, 4, 7], [0, 4, 7], [0, 4, 7]]⟩, .edge 1905 ⟨![[], [1], [2], [0, 3, 4], [4, 5], [1], [1, 2, 1], [0]], ![[7], [1], [2], [2, 2, 4], [2, 6], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 1902 ⟨![[0], [], [2], [0, 0, 1], [0], [], [2, 3, 5], [1]], ![[0], [7], [2], [3, 3], [2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 1908 ⟨![[], [1, 0, 5], [2], [0, 3, 4], [4, 5], [0, 1, 3], [2, 3, 5], [0]], ![[7], [1, 7], [2], [2, 2, 4], [2, 6], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 1900 ⟨![[0], [1], [], [0, 0, 2, 3], [0, 3, 5], [1, 3, 5], [0, 0, 3], [2]], ![[0], [1], [7], [0, 0, 6], [1, 5, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .noncentric 4, .edge 1904 ⟨![[0], [], [1, 2, 4], [0, 0, 1], [0], [], [2, 1, 5], [1]], ![[0], [7], [2, 7], [3, 3], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 1910 ⟨![[], [1, 0, 5], [0, 2, 5], [0, 3, 4], [4, 5], [0, 1, 3], [0, 2, 3, 4, 5], [0]], ![[7], [1, 7], [2, 7], [2, 4, 6], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 191) : Classified H :=
  classify_of_checks 191 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node191

namespace Node192

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 2, 3, 2, 3], [0, 3, 0, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 191) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 192 :=
  generated_of_packed 191 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 96, .edge 1919 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 3], [2, 5]], ![[5], [2], [3], [1, 3, 5, 3], [2, 6], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 8, .edge 1917 ⟨![[], [1], [0, 3, 4, 5], [2], [4, 5], [1], [0], [2, 5]], ![[6], [1], [3], [1, 3, 1, 7], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1914 ⟨![[0], [], [1], [2], [0], [], [1], [2, 3, 5]], ![[0], [2], [3], [0, 0, 0, 3, 0, 7], [0, 3, 0, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1921 ⟨![[], [1, 0, 5], [0, 1, 1, 5], [2], [4, 5], [1, 0, 4], [0], [2, 5]], ![[6], [1, 6], [3], [1, 3, 5, 3], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1911 ⟨![[0], [1], [2], [], [0, 5], [1, 3, 5], [2, 5], []], ![[0], [1], [2], [0, 0, 2, 6], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1916 ⟨![[], [1], [2], [0, 4], [4, 5], [1], [2, 3], [0]], ![[7], [1], [2], [2, 2, 2, 6], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 1913 ⟨![[0], [], [2], [1, 1, 1], [0], [], [2], [1]], ![[0], [7], [2], [0, 0, 0, 3, 0, 3], [0, 3, 0, 7], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1920 ⟨![[], [1, 0, 4], [2], [0, 4], [4, 5], [1, 0, 5], [2, 3], [0]], ![[7], [1, 7], [2], [1, 3, 5, 7], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 1912 ⟨![[0], [1], [], [2, 2, 2], [0, 3], [1], [3, 4], [2]], ![[0], [1], [7], [0, 0, 0, 4], [0, 3, 4, 7], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 1918 ⟨![[], [1], [2, 0, 4], [0, 4], [4, 5], [1], [0, 2, 5], [0]], ![[7], [1], [2, 7], [2, 3, 3, 6], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1915 ⟨![[0], [], [1, 2, 5], [1, 1, 1], [0], [], [1, 2, 5], [1]], ![[0], [7], [2, 7], [0, 0, 0, 3, 0, 3], [0, 3, 0, 7], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1922 ⟨![[], [1, 0, 4], [2, 0, 4], [0, 4], [4, 5], [1, 0, 5], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [1, 3, 5, 7], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 192) : Classified H :=
  classify_of_checks 192 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node192

namespace Node193

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 1], [0, 1, 0, 1], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 192) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 193 :=
  generated_of_packed 192 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 96, .edge 1932 ⟨![[], [0, 2, 2], [1], [2], [4, 5], [0], [1, 5], [2, 3]], ![[5], [2], [3], [1, 5], [1, 1], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1924 ⟨![[0], [1], [], [2], [0, 5], [1, 4], [], [2, 5]], ![[0], [1], [3], [1, 1], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1930 ⟨![[], [1], [0, 4], [2], [4, 5], [0, 1, 0], [0], [2, 3]], ![[6], [1], [3], [1, 1], [2, 2], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1927 ⟨![[0], [], [1, 1, 1], [2], [0, 3, 5], [3], [1], [0, 2, 0]], ![[0], [6], [3], [5], [0, 4, 5], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1933 ⟨![[], [0, 1, 3], [0, 4], [2], [4, 5], [0, 1, 4], [0], [2, 3]], ![[6], [1, 6], [3], [1, 5], [1, 1], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 1923 ⟨![[0], [1], [2], [], [0, 3], [0, 0, 1, 3], [2, 5], [3, 4]], ![[0], [1], [2], [1, 1], [1, 1, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1929 ⟨![[], [1], [2], [0, 3, 4, 5], [4, 5], [1, 3, 5], [2, 5], [0]], ![[7], [1], [2], [1, 1], [1, 4, 5], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1926 ⟨![[0], [], [2], [0, 0, 1], [0, 1, 1], [3], [2, 4], [1]], ![[0], [7], [2], [5], [2, 6], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .noncentric 4, .edge 1925 ⟨![[0], [1], [], [2, 5], [0, 5], [1, 4], [], [2]], ![[0], [1], [7], [1, 1], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1931 ⟨![[], [1], [2, 0, 5], [0, 2, 2], [4, 5], [1, 3, 5], [0, 2, 2, 2], [0]], ![[7], [1], [2, 7], [1, 1], [2, 2], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1928 ⟨![[0], [], [1, 2, 5], [0, 0, 1], [0, 1, 1], [3], [0, 0, 2, 1], [1]], ![[0], [7], [2, 7], [5], [0, 4, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 1934 ⟨![[], [1, 0, 5], [2, 0, 5], [0, 2, 2], [4, 5], [0, 1, 5], [0, 2, 2, 2], [0]], ![[7], [1, 7], [2, 7], [1, 5], [1, 1], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 193) : Classified H :=
  classify_of_checks 193 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node193

namespace Node194

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 3, 3], [0, 2, 0, 2], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 193) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 194 :=
  generated_of_packed 193 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 96, .edge 1943 ⟨![[], [0, 0, 0], [1], [2], [4, 5], [0], [1, 5], [2, 3, 5]], ![[5], [2], [3], [1, 1, 4], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1936 ⟨![[0], [1], [], [2], [0, 5], [1, 4], [], [2, 5]], ![[0], [1], [3], [0, 0, 3, 3], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1941 ⟨![[], [1], [0, 4], [2], [4, 5], [1, 3], [0], [2, 3, 5]], ![[6], [1], [3], [1, 5], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 1939 ⟨![[0], [], [1, 4], [2], [0, 3], [], [1], [2, 4]], ![[0], [6], [3], [0, 0, 0, 4], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 1945 ⟨![[], [1, 0, 4], [0, 4], [2], [4, 5], [0, 1, 4], [0], [2, 3, 5]], ![[6], [1, 6], [3], [1, 1, 4], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 1935 ⟨![[0], [1], [2], [], [0, 3, 5], [1, 4], [2, 5], [0, 0, 3]], ![[0], [1], [2], [0, 0, 7], [1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 36, .edge 1938 ⟨![[0], [], [2], [1, 4], [0, 3], [], [2, 4], [1]], ![[0], [7], [2], [0, 0, 0, 4], [2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 1944 ⟨![[], [0, 1, 4], [2], [0, 3, 4], [4, 5], [0, 1, 1, 1], [2, 5], [0]], ![[7], [1, 7], [2], [1, 1, 4], [2, 4, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1937 ⟨![[0], [1], [], [2, 5], [0, 5], [1, 4], [], [2]], ![[0], [1], [7], [0, 0, 3, 7], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1942 ⟨![[], [1], [0, 2, 3], [0, 2, 2], [4, 5], [1, 3], [0, 2, 2, 2], [0]], ![[7], [1], [2, 7], [1, 5], [2, 2], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 1940 ⟨![[0], [], [1, 2, 3], [1, 4], [0, 3], [], [0, 1, 2, 0], [1]], ![[0], [7], [2, 7], [0, 0, 0, 4], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 1946 ⟨![[], [0, 1, 4], [0, 2, 3], [0, 2, 2], [4, 5], [0, 1, 1, 1], [0, 2, 2, 2], [0]], ![[7], [1, 7], [2, 7], [1, 1, 4], [2, 2], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 194) : Classified H :=
  classify_of_checks 194 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node194

namespace Node195

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 1], [0, 1, 0, 1], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 194) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 195 :=
  generated_of_packed 194 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1950 ⟨![[0], [], [1], [2], [0, 3, 5], [3], [1, 5], [0, 2, 0]], ![[0], [2], [3], [5], [0, 4, 5], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1956 ⟨![[], [0, 1, 1], [1], [2], [4, 5], [0], [1, 3], [2, 3]], ![[5], [2], [3], [1, 5], [1, 1], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 1948 ⟨![[0], [1], [], [2], [0, 3], [1, 5], [2, 2], [2]], ![[0], [1], [3], [1, 1], [1, 1, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 1955 ⟨![[], [1], [0, 2, 2, 5], [2], [4, 5], [0, 1, 0], [0], [2, 3]], ![[6], [1], [3], [1, 1], [3, 7], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1952 ⟨![[0], [], [1, 3, 5], [2], [0, 3, 5], [3], [1], [0, 2, 0]], ![[0], [6], [3], [5], [0, 4, 5], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1958 ⟨![[], [0, 1, 5], [0, 1, 1, 3], [2], [1, 1], [0, 1, 1, 1, 3], [0], [2, 3]], ![[6], [1, 6], [3], [1, 5], [1, 1], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1947 ⟨![[0], [1], [2], [], [0, 3], [2, 1, 2], [2], [2, 2]], ![[0], [1], [2], [1, 1], [1, 1, 7], [0, 4, 7], [0, 4, 7], [0, 4, 7], [0, 4, 7], [0, 4, 7]]⟩, .edge 1954 ⟨![[], [1], [2], [0, 2, 2, 5], [4, 5], [1, 3, 5], [2, 3], [0]], ![[7], [1], [2], [1, 1], [2, 6], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1951 ⟨![[0], [], [2], [0, 0, 1], [0, 1, 1], [3], [2, 5], [1]], ![[0], [7], [2], [5], [0, 4, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 1957 ⟨![[], [1, 0, 5], [2], [0, 1, 1, 4], [4, 5], [0, 1, 5], [2, 3], [0]], ![[7], [1, 7], [2], [1, 5], [1, 1], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 1949 ⟨![[0], [1], [], [2, 3, 4], [0, 3], [1, 5], [3, 4], [2]], ![[0], [1], [7], [1, 1], [1, 1, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .noncentric 36, .edge 1953 ⟨![[0], [], [0, 0, 1, 2], [0, 0, 1], [0, 1, 1], [3], [2, 1], [1]], ![[0], [7], [2, 7], [5], [0, 4, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 1959 ⟨![[], [1, 0, 5], [0, 2, 5], [0, 1, 1, 4], [4, 5], [0, 1, 5], [0, 2, 3, 4], [0]], ![[7], [1, 7], [2, 7], [1, 5], [1, 1], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 195) : Classified H :=
  classify_of_checks 195 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node195

namespace Node196

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 2, 2], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 195) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 196 :=
  generated_of_packed 195 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1963 ⟨![[0], [], [1], [2], [0, 3], [], [1, 3], [2, 4]], ![[0], [2], [3], [0, 0, 0, 4], [0, 3, 7, 4], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1970 ⟨![[], [0, 0, 0], [1], [2], [4, 5], [0], [1, 3, 5], [2, 3, 5]], ![[5], [2], [3], [1, 1, 4], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 1961 ⟨![[0], [1], [], [2], [0, 3, 5], [1, 3], [2, 2], [2]], ![[0], [1], [3], [1, 5], [0, 1, 4, 1], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 1968 ⟨![[], [1], [0, 3, 4], [2], [4, 5], [1, 3], [0], [2, 3, 5]], ![[6], [1], [3], [1, 5], [3, 7], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1965 ⟨![[0], [], [1, 3], [2], [0, 3], [], [1], [2, 4]], ![[0], [6], [3], [0, 0, 0, 4], [0, 3, 7, 4], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1972 ⟨![[], [0, 1, 3], [0, 3, 4], [2], [1, 1], [0, 1, 1, 1], [0], [2, 3, 5]], ![[6], [1, 6], [3], [1, 1, 4], [3, 7], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1960 ⟨![[0], [1], [2], [], [0, 3, 5], [1, 4], [2], [2, 2]], ![[0], [1], [2], [0, 0, 7], [1, 5], [0, 4, 7], [0, 4, 7], [0, 4, 7], [0, 4, 7], [0, 4, 7]]⟩, .edge 1967 ⟨![[], [1], [2], [0, 3, 4], [4, 5], [1, 3], [2, 3, 5], [0]], ![[7], [1], [2], [1, 5], [2, 6], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 1964 ⟨![[0], [], [2], [1, 4], [0, 3], [], [2, 3], [1]], ![[0], [7], [2], [0, 0, 0, 4], [0, 3, 3, 4], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1971 ⟨![[], [0, 1, 4], [2], [0, 3, 4], [4, 5], [0, 1, 1, 1], [1, 1, 2], [0]], ![[7], [1, 7], [2], [1, 1, 4], [2, 6], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 1962 ⟨![[0], [1], [], [0, 0, 2, 3], [0, 3, 5], [1, 3], [0, 0, 3], [2]], ![[0], [1], [7], [1, 5], [0, 1, 4, 1], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 1969 ⟨![[], [1], [0, 2, 5], [0, 3, 4], [4, 5], [1, 3], [0, 1, 2, 1, 5], [0]], ![[7], [1], [2, 7], [1, 5], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1966 ⟨![[0], [], [0, 0, 1, 2], [1, 4], [0, 3], [], [2, 1, 5], [1]], ![[0], [7], [2, 7], [0, 0, 0, 4], [0, 3, 3, 4], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .noncentric 4] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 196) : Classified H :=
  classify_of_checks 196 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node196

namespace Node197

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 1, 3, 1, 3], [0, 1, 0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 196) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 197 :=
  generated_of_packed 196 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1974 ⟨![[0], [], [1], [2], [0, 4, 5], [], [1, 4, 5], [2, 3, 5]], ![[0], [2], [3], [0, 0, 3, 7], [0, 4], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]⟩, .noncentric 4, .noncentric 4, .edge 1976 ⟨![[], [1], [0, 5], [2], [5], [1, 4, 5], [0], [2]], ![[6], [1], [3], [1, 3, 1, 3, 4], [1, 4, 5], [4], [4], [4], [4], [4]]⟩, .noncentric 4, .edge 1978 ⟨![[], [0, 1, 5], [0, 5], [2], [5], [0, 1, 1, 1], [0], [2]], ![[6], [1, 6], [3], [1, 3, 4, 5, 3], [1, 1], [4], [4], [4], [4], [4]]⟩, .edge 1973 ⟨![[0], [1], [2], [], [0], [1, 3, 5], [2], []], ![[0], [1], [2], [0, 0, 1, 5], [0, 1, 0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]⟩, .noncentric 4, .edge 1975 ⟨![[0], [], [2], [1, 1, 1], [0, 4, 5], [], [2, 4, 5], [1]], ![[0], [7], [2], [0, 0, 3, 3], [0, 4], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]⟩, .noncentric 4, .noncentric 4, .edge 1977 ⟨![[], [1], [0, 2, 5], [0, 5], [5], [1, 4, 5], [0, 2], [0]], ![[7], [1], [2, 7], [1, 3, 5, 3], [1, 4, 5], [4], [4], [4], [4], [4]]⟩, .noncentric 4, .edge 1979 ⟨![[], [1, 0, 5], [0, 2, 5], [0, 5], [5], [0, 1, 1, 1], [0, 2], [0]], ![[7], [1, 7], [2, 7], [1, 3, 1, 7], [1, 1], [4], [4], [4], [4], [4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 197) : Classified H :=
  classify_of_checks 197 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node197

namespace Node198

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 1, 3, 1, 3], [0, 1, 0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 197) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 198 :=
  generated_of_packed 197 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 96, .edge 1987 ⟨![[], [0, 4], [1], [2], [5], [0], [1, 3, 5], [2]], ![[5], [2], [3], [1, 1, 2, 2], [1, 1], [4], [4], [4], [4], [4]]⟩, .noncentric 4, .edge 1985 ⟨![[], [1], [0, 3], [2], [5], [1, 4, 5], [0], [2]], ![[6], [1], [3], [2, 2, 2, 6], [2, 2], [4], [4], [4], [4], [4]]⟩, .noncentric 36, .edge 1989 ⟨![[], [0, 1, 3], [0, 3], [2], [5], [1, 0], [0], [2]], ![[6], [1, 6], [3], [1, 1, 2, 6], [1, 1], [4], [4], [4], [4], [4]]⟩, .edge 1980 ⟨![[0], [1], [2], [], [0], [1, 3, 5], [2, 5], []], ![[0], [1], [2], [0, 0, 1, 5], [0, 1, 0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]⟩, .edge 1984 ⟨![[], [1], [2], [0, 5], [5], [1, 4, 5], [0, 2, 0], [0]], ![[7], [1], [2], [1, 3, 5, 3], [1, 4, 5], [4], [4], [4], [4], [4]]⟩, .edge 1982 ⟨![[0], [], [2], [1, 1, 1], [0, 4, 5], [], [2], [1]], ![[0], [7], [2], [0, 0, 3, 3], [0, 4], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]⟩, .edge 1988 ⟨![[], [1, 0, 5], [2], [0, 5], [5], [0, 1, 1, 1], [0, 2, 0], [0]], ![[7], [1, 7], [2], [1, 1, 2, 2], [1, 1], [4], [4], [4], [4], [4]]⟩, .edge 1981 ⟨![[0], [1], [], [2, 2, 2], [0, 3, 5], [1], [3, 4], [2]], ![[0], [1], [7], [0, 4], [0, 4, 6], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]⟩, .edge 1986 ⟨![[], [1], [2, 0, 5], [0, 5], [5], [1, 4, 5], [0, 2, 5], [0]], ![[7], [1], [2, 7], [1, 3, 5, 3], [2, 2], [4], [4], [4], [4], [4]]⟩, .edge 1983 ⟨![[0], [], [1, 2, 5], [1, 1, 1], [0, 4, 5], [], [1, 2, 5], [1]], ![[0], [7], [2, 7], [0, 0, 3, 3], [0, 4], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]⟩, .edge 1990 ⟨![[], [1, 0, 5], [2, 0, 5], [0, 5], [5], [0, 1, 1, 1], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [1, 1, 2, 6], [1, 1], [4], [4], [4], [4], [4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 198) : Classified H :=
  classify_of_checks 198 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node198

namespace Node199

def gen : Fin 5 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [4], [5]],
   ![[0], [1], [2], [1, 2, 1, 2], [3], [4], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 198) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 199 :=
  generated_of_packed 198 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .edge 1993 ⟨![[], [0], [1], [2], [3], [], [0, 4], [1, 5], [2], [3, 5]], ![[1], [2], [3], [4], [1, 1, 1, 6], [1, 6], [1, 6], [1, 6], [1, 6], [1, 6]]⟩, .core, .edge 1995 ⟨![[], [0, 4], [1], [2], [3], [], [0], [1, 5], [2], [3, 5]], ![[6], [2], [3], [4], [1, 1, 1, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .edge 1991 ⟨![[0], [1], [], [3], [2], [0, 5], [1, 5], [], [3], [2]], ![[0], [1], [4], [3], [1, 6], [0, 5], [0, 5], [0, 5], [0, 5], [0, 5]]⟩, .edge 1994 ⟨![[], [1], [0, 2, 5], [3], [0, 5], [], [1, 4], [0, 2], [3], [0]], ![[9], [1], [2, 9], [3], [1, 1, 1, 6], [1, 6], [1, 6], [1, 6], [1, 6], [1, 6]]⟩, .edge 1992 ⟨![[0], [], [1, 2, 4], [3], [1, 4], [0, 4], [4, 5], [1, 2], [3], [1]], ![[0], [9], [2, 9], [3], [0, 5], [0, 5, 6], [0, 5, 6], [0, 5, 6], [0, 5, 6], [0, 5, 6]]⟩, .edge 1996 ⟨![[], [1, 0, 5], [0, 2, 5], [3], [0, 5], [], [0, 1, 5], [0, 2], [3], [0]], ![[9], [1, 9], [2, 9], [3], [1, 1, 1, 6], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 199) : Classified H :=
  classify_of_checks 199 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node199

end ReeTwo.SylowModel.SmallEvenMaximalLower
