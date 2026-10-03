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

namespace Node100

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 1, 2, 0, 1, 2], [0, 2, 2, 2, 0, 2], [0, 1, 1, 1, 0, 1], [0, 1, 0, 1, 2, 1, 1, 2], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 99) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 100 :=
  generated_of_packed 99 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1208 ⟨![[], [0], [1], [], [0, 4], [1, 3]], ![[1], [2], [2, 4, 5, 1], [2, 2, 2, 5], [1, 1, 1, 4], [1, 1, 1, 2, 2, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 1210 ⟨![[], [0, 4], [1], [], [0], [1, 3]], ![[4], [2], [2, 4, 2, 4], [2, 2, 2, 5], [1, 1, 1, 4], [1, 1, 1, 4, 2, 2], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1206 ⟨![[0], [1], [], [0, 3, 6], [1, 5], [4, 5]], ![[0], [1], [0, 3, 1, 1], [0, 5, 3, 5], [1, 1, 1, 4, 5], [1, 1, 1, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 1209 ⟨![[], [1], [0, 3], [], [1, 4], [0]], ![[5], [1], [2, 1, 2, 1], [2, 2, 2, 5], [1, 1, 1, 4], [1, 1, 1, 2, 5, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1207 ⟨![[0], [], [2, 1, 3, 5], [0, 4, 6], [1, 1, 4], [1]], ![[0], [5], [0, 2, 0, 2], [0, 2, 0, 4, 2], [2, 2, 4], [0, 2, 5, 3], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 1211 ⟨![[], [0, 1], [0, 3], [], [0, 1, 4], [0]], ![[5], [1, 5], [2, 1, 5, 4], [2, 2, 2, 5], [1, 1, 1, 4], [1, 1, 1, 4, 2, 5], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 100) : Classified H :=
  classify_of_checks 100 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node100

namespace Node101

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [1, 1], [0, 0, 2, 2], [2, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 1, 0, 1, 1, 1], [0, 0, 0, 1, 0, 1, 1, 1], [0, 0, 0, 1, 0, 1, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 100) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 101 :=
  generated_of_packed 100 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1214 ⟨![[], [0], [1], [3, 4], [0, 6], [1, 4, 5, 6]], ![[1], [2], [1, 1], [2, 2, 3], [2, 2], [2, 3, 5, 3], [1, 1, 1, 4], [1, 1, 1, 4], [1, 1, 1, 4], [1, 1, 1, 4]]⟩, .core, .edge 1216 ⟨![[], [3, 0, 4], [1], [3, 4], [0], [1, 4, 5, 6]], ![[4], [2], [1, 4], [2, 2, 3], [2, 2], [2, 3, 5, 3], [1, 1, 1, 3, 4], [1, 1, 1, 3, 4], [1, 1, 1, 3, 4], [1, 1, 1, 3, 4]]⟩, .edge 1212 ⟨![[0], [1], [], [0, 4, 5], [1, 3], [4]], ![[0], [1], [1, 1], [0, 0, 5], [5], [0, 0, 0, 3, 5], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 1215 ⟨![[], [1], [0, 3, 5], [3, 4], [1, 6], [0]], ![[5], [1], [1, 1], [2, 5, 3], [2, 5], [2, 2, 3], [1, 1, 1, 4], [1, 1, 1, 4], [1, 1, 1, 4], [1, 1, 1, 4]]⟩, .edge 1213 ⟨![[0], [], [2, 1, 3], [0, 6], [2], [1]], ![[0], [5], [4], [0, 0, 2, 5], [2, 5], [0, 0, 0, 2, 3, 5], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]⟩, .edge 1217 ⟨![[], [0, 1, 6], [0, 3, 5], [3, 4], [1, 5, 0], [0]], ![[5], [1, 5], [1, 4], [2, 5, 3], [2, 5], [2, 2, 3], [1, 1, 1, 3, 4], [1, 1, 1, 3, 4], [1, 1, 1, 3, 4], [1, 1, 1, 3, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 101) : Classified H :=
  classify_of_checks 101 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node101

namespace Node102

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [0, 1, 0, 1, 1, 1], [0, 0, 1, 2, 1, 2, 2, 2], [0, 0, 1, 2, 1, 2], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 101) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 102 :=
  generated_of_packed 101 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 1219 ⟨![[0], [], [1], [0, 2, 3], [2, 3, 6], [3, 1, 4]], ![[0], [2], [0, 0], [0, 3], [0, 2, 2, 2, 5, 3], [0, 2, 5, 3], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩, .edge 1222 ⟨![[], [0, 3], [1], [2], [0], [1, 6]], ![[4], [2], [3], [1, 1, 1, 4], [1, 2, 2, 2, 3, 4, 2], [1, 2, 3, 4, 5], [1, 1, 3], [1, 1, 3], [1, 1, 3], [1, 1, 3]]⟩, .edge 1218 ⟨![[0], [1], [], [0, 6], [3, 4, 1], [4, 5]], ![[0], [1], [0, 0], [0, 0, 4, 4], [0, 0, 1, 4], [0, 0, 1, 4, 5], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]⟩, .edge 1221 ⟨![[], [1], [0, 2, 6], [2], [1, 2, 3], [0]], ![[5], [1], [3], [1, 1, 1, 3, 4], [1, 2, 2, 2, 4, 5], [2, 1, 2, 4], [1, 4], [1, 4], [1, 4], [1, 4]]⟩, .edge 1220 ⟨![[0], [], [2, 4, 1], [0, 2, 3], [2, 3, 6], [1]], ![[0], [5], [0, 0], [0, 3], [0, 0, 2, 2, 5, 2], [0, 0, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩, .edge 1223 ⟨![[], [5, 0, 1], [0, 2, 6], [2], [0, 3, 1, 5], [0]], ![[5], [1, 5], [3], [1, 1, 1, 4], [1, 2, 2, 2, 1, 2], [2, 1, 5, 1], [1, 1, 3], [1, 1, 3], [1, 1, 3], [1, 1, 3]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 102) : Classified H :=
  classify_of_checks 102 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node102

namespace Node103

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [0, 0, 2, 1, 1, 2], [1, 1, 2, 1, 2, 1], [0, 1, 1, 2, 0, 2], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 102) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 103 :=
  generated_of_packed 102 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 1225 ⟨![[0], [], [1], [0, 2, 3], [2, 3, 6], [1, 4]], ![[0], [2], [0, 0], [0, 3], [2, 5], [0, 2, 3, 2], [2, 4, 2, 4], [2, 4, 2, 4], [2, 4, 2, 4], [2, 4, 2, 4]]⟩, .edge 1228 ⟨![[], [0, 3], [1], [2], [0], [1, 3, 5]], ![[4], [2], [3], [1, 1, 1, 4], [1, 2, 1, 3, 5], [1, 2, 5, 3, 4], [1, 1, 3], [1, 1, 3], [1, 1, 3], [1, 1, 3]]⟩, .edge 1224 ⟨![[0], [1], [], [3, 5, 0], [4, 1], []], ![[0], [1], [0, 0], [0, 0, 4, 4], [1, 1, 4, 1], [0, 1, 1, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 1227 ⟨![[], [1], [0, 0, 0], [2], [1, 2, 3], [0]], ![[5], [1], [3], [1, 1, 1, 3, 4], [2, 1, 5, 1], [1, 1, 2, 2], [1, 4], [1, 4], [1, 4], [1, 4]]⟩, .edge 1226 ⟨![[0], [], [1, 1, 1], [0, 2, 3], [1, 4, 1], [1]], ![[0], [5], [0, 0], [0, 3], [2, 4, 2], [0, 2, 0, 5], [2, 4, 5, 4], [2, 4, 5, 4], [2, 4, 5, 4], [2, 4, 5, 4]]⟩, .edge 1229 ⟨![[], [0, 3, 4, 1], [0, 0, 0], [2], [0, 4, 1], [0]], ![[5], [1, 5], [3], [1, 1, 1, 4], [1, 2, 3, 4, 2], [1, 4, 2, 2], [1, 1, 3], [1, 1, 3], [1, 1, 3], [1, 1, 3]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 103) : Classified H :=
  classify_of_checks 103 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node103

namespace Node104

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [0, 1, 0, 1, 1, 1], [0, 0, 0, 2, 2, 0], [0, 1, 1, 2, 0, 2, 2, 2], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 103) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 104 :=
  generated_of_packed 103 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 1231 ⟨![[0], [], [1], [0, 2, 3], [2, 3, 6], [3, 1]], ![[0], [2], [0, 0], [0, 3], [5, 5], [0, 2, 2, 2, 3, 2], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩, .edge 1234 ⟨![[], [0, 3], [1], [2], [0], [3, 1, 5]], ![[4], [2], [3], [1, 1, 1, 4], [5, 5], [1, 2, 1, 2, 2, 3, 2], [1, 1, 3], [1, 1, 3], [1, 1, 3], [1, 1, 3]]⟩, .edge 1230 ⟨![[0], [1], [], [3, 5, 0], [1, 3], [4, 6]], ![[0], [1], [0, 0], [1, 1, 1, 4], [0, 0, 0, 5, 0], [0, 1, 1, 3], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]⟩, .edge 1233 ⟨![[], [1], [0, 0, 0, 4], [2], [1, 2, 3], [0]], ![[5], [1], [3], [1, 1, 1, 3, 4], [5, 2], [1, 1, 2, 2, 5, 2], [1, 4], [1, 4], [1, 4], [1, 4]]⟩, .edge 1232 ⟨![[0], [], [1, 2], [0, 2, 3], [2, 3, 6], [1]], ![[0], [5], [0, 0], [0, 3], [5, 2], [0, 2, 0, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5], [2, 2, 5, 5]]⟩, .edge 1235 ⟨![[], [0, 4, 1], [0, 0, 0, 4], [2], [0, 3, 1, 4], [0]], ![[5], [1, 5], [3], [1, 1, 1, 4], [5, 2], [1, 2, 2, 2, 5, 4], [1, 1, 3], [1, 1, 3], [1, 1, 3], [1, 1, 3]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 104) : Classified H :=
  classify_of_checks 104 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node104

namespace Node105

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [4]],
   ![[0], [1], [1, 1], [0, 0, 0, 1, 1, 1, 0, 1], [2], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 104) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 105 :=
  generated_of_packed 104 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 1236 ⟨![[0], [], [1], [0, 3, 5, 6], [2], [1, 6]], ![[0], [2], [4], [0, 0, 0, 4, 3, 4], [0, 0], [0, 0, 0, 4, 0, 4], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .edge 1238 ⟨![[], [0, 3, 4], [1], [4], [0], [1, 4, 6]], ![[4], [2], [1, 4], [1, 3, 4, 1, 1], [3], [1, 4, 4, 1], [2, 3, 5], [2, 3, 5], [2, 3, 5], [2, 3, 5]]⟩, .noncentric 136, .edge 1237 ⟨![[], [1], [0, 6], [4], [1, 3], [0]], ![[5], [1], [1, 1], [1, 1, 1, 4], [3], [1, 1, 4, 4], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .noncentric 8, .edge 1239 ⟨![[], [1, 0, 6], [0, 6], [4], [0, 1, 6], [0]], ![[5], [1, 5], [1, 4], [1, 3, 4, 1, 1], [3], [1, 4, 4, 1], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 105) : Classified H :=
  classify_of_checks 105 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node105

namespace Node106

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [4]],
   ![[0], [1], [0, 0], [0, 0, 1, 2, 1, 2], [2], [0, 1, 0, 2, 1, 2], [0, 0, 0, 1, 0, 0, 0, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 105) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 106 :=
  generated_of_packed 105 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 1240 ⟨![[0], [], [1], [3, 0, 6], [2, 3, 4], [1, 4]], ![[0], [2], [0, 0], [0, 0, 3, 0], [2, 5], [0, 3, 3, 0], [4, 4], [4, 4], [4, 4], [4, 4]]⟩, .edge 1243 ⟨![[], [0, 3, 2], [1], [2], [0], [1, 6]], ![[4], [2], [3], [1, 1, 3, 1, 4], [1, 1], [1, 1, 4, 4], [2, 5], [2, 5], [2, 5], [2, 5]]⟩, .noncentric 136, .edge 1242 ⟨![[], [1], [0, 0, 0], [2], [3, 1, 6], [0]], ![[5], [1], [3], [1, 2, 4, 2], [1, 3, 4], [1, 1, 4, 4], [2, 2, 3], [2, 2, 3], [2, 2, 3], [2, 2, 3]]⟩, .edge 1241 ⟨![[0], [], [1, 3, 2], [3, 0, 6], [1, 1, 4], [1]], ![[0], [5], [0, 0], [0, 0, 3, 0], [2, 2, 4], [0, 3, 3, 0], [4, 4], [4, 4], [4, 4], [4, 4]]⟩, .noncentric 8] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 106) : Classified H :=
  classify_of_checks 106 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node106

namespace Node107

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [2, 2], [1, 2, 2, 2, 1, 2], [0, 0], [1, 2, 2, 1, 2, 2], [0, 0, 0, 2, 0, 2, 2, 2], [0, 0, 0, 2, 0, 2, 2, 2], [0, 0, 0, 2, 0, 2, 2, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 106) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 107 :=
  generated_of_packed 106 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 1245 ⟨![[0], [], [1], [0], [], [1, 3]], ![[0], [2], [2, 2], [2, 2, 2, 5], [0, 0], [2, 2, 5, 5], [2, 5, 2, 5], [2, 5, 2, 5], [2, 5, 2, 5], [2, 5, 2, 5]]⟩, .noncentric 136, .edge 1244 ⟨![[0], [1], [], [0, 6], [1, 3, 5, 6], [2]], ![[0], [1], [5], [1, 5, 4, 5], [0, 0], [1, 5, 1, 5], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]⟩, .noncentric 136, .edge 1246 ⟨![[0], [], [1, 3], [0], [], [1]], ![[0], [5], [2, 5], [2, 5, 2, 2], [0, 0], [2, 5, 5, 2], [2, 2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2]]⟩, .noncentric 136] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 107) : Classified H :=
  classify_of_checks 107 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node107

namespace Node108

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [2, 2], [0, 0, 2, 1, 2, 1, 2, 2], [0, 0], [0, 0, 1, 2, 2, 1, 2, 2], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 107) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 108 :=
  generated_of_packed 107 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 1248 ⟨![[0], [], [1], [0, 6], [4], [1, 3, 6]], ![[0], [2], [2, 2], [2, 5, 2, 2], [4], [2, 2, 5, 5], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4]]⟩, .edge 1251 ⟨![[], [0, 4, 6], [1], [4], [0], [1, 6]], ![[4], [2], [2, 2], [1, 2, 2, 2, 1, 5], [3], [1, 2, 2, 1, 2, 5], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1247 ⟨![[0], [1], [], [0, 6], [1, 3, 5], [2]], ![[0], [1], [5], [0, 0, 4, 5, 1, 5], [0, 0], [0, 0, 1, 5, 1, 5], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]⟩, .edge 1250 ⟨![[], [1], [0, 4, 6], [4], [1, 6], [0]], ![[5], [1], [2, 5], [1, 2, 2, 2, 4, 5], [3], [1, 2, 2, 4, 2, 5], [1, 3, 4], [1, 3, 4], [1, 3, 4], [1, 3, 4]]⟩, .edge 1249 ⟨![[0], [], [1, 1, 2, 1], [0, 6], [4], [1]], ![[0], [5], [2, 5], [2, 2, 2, 4, 5], [4], [2, 5, 5, 2], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4]]⟩, .edge 1252 ⟨![[], [0, 1, 1, 1], [0, 4, 6], [4], [1, 0, 2], [0]], ![[5], [1, 5], [2, 5], [1, 2, 2, 2, 1, 2], [3], [2, 1, 2, 2, 1, 2], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 108) : Classified H :=
  classify_of_checks 108 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node108

namespace Node109

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [2, 2], [1, 2, 2, 2, 1, 2], [0, 0, 0, 1, 0, 1], [1, 2, 2, 1, 2, 2], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 108) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 109 :=
  generated_of_packed 108 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 1254 ⟨![[0], [], [1], [0, 4], [], [1, 3]], ![[0], [2], [2, 2], [2, 2, 2, 5], [0, 0, 0, 3], [2, 2, 5, 5], [0, 3], [0, 3], [0, 3], [0, 3]]⟩, .edge 1256 ⟨![[], [0, 6], [1], [4, 6], [0], [1]], ![[4], [2], [2, 2], [1, 2, 2, 2, 4, 2], [1, 1, 3], [1, 2, 2, 4, 2, 2], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1253 ⟨![[0], [1], [], [0], [1, 3, 5, 6], [2]], ![[0], [1], [5], [1, 5, 4, 5], [0, 0, 0, 1, 0, 1], [1, 5, 1, 5], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .noncentric 8, .edge 1255 ⟨![[0], [], [1, 3], [0, 4], [], [1]], ![[0], [5], [2, 5], [2, 5, 2, 2], [0, 0, 0, 3], [2, 5, 5, 2], [0, 3], [0, 3], [0, 3], [0, 3]]⟩, .edge 1257 ⟨![[], [0, 1, 1, 1], [0, 4, 6], [4, 6], [0, 2, 1, 3], [0]], ![[5], [1, 5], [2, 5], [1, 2, 2, 2, 1, 5], [1, 1, 3], [1, 2, 2, 4, 2, 2], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 109) : Classified H :=
  classify_of_checks 109 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node109

namespace Node110

def gen : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [2, 2], [0, 0, 1, 2, 2, 2, 1, 2], [1, 1], [0, 0, 2, 1, 2, 2, 1, 2], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 109) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 110 :=
  generated_of_packed 109 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 1259 ⟨![[0], [], [1], [0, 0, 0], [4], [1, 3, 6]], ![[0], [2], [2, 2], [2, 5, 2, 2], [4], [2, 2, 5, 5], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]⟩, .noncentric 136, .edge 1258 ⟨![[0], [1], [], [0], [1, 3, 5], [2]], ![[0], [1], [5], [0, 0, 1, 5, 4, 5], [1, 1], [0, 0, 4, 5, 4, 5], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩, .edge 1261 ⟨![[], [1], [0, 4, 6], [4, 6], [1, 4, 6], [0]], ![[5], [1], [2, 5], [1, 2, 2, 2, 1, 2], [1, 1], [2, 1, 2, 2, 1, 5], [1, 4], [1, 4], [1, 4], [1, 4]]⟩, .edge 1260 ⟨![[0], [], [0, 0, 1, 3], [0, 0, 0], [4], [1]], ![[0], [5], [2, 5], [2, 2, 2, 4, 5], [4], [2, 5, 5, 2], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]⟩, .noncentric 8] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 110) : Classified H :=
  classify_of_checks 110 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node110

namespace Node111

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 1, 1, 1, 0, 1], [0, 1, 0, 1, 1, 1, 2, 2], [0, 1, 1, 2, 1, 0, 2, 1], [1, 0, 1, 0], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 110) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 111 :=
  generated_of_packed 110 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1264 ⟨![[], [0], [1], [], [0, 2], [1, 2, 4]], ![[1], [2], [1, 1, 1, 4], [1, 1, 1, 4, 5, 5], [1, 1, 2, 1, 5, 4], [1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 1266 ⟨![[], [0, 2], [1], [], [0], [1, 2, 4]], ![[4], [2], [1, 1, 1, 4], [1, 1, 1, 2, 2, 4], [1, 1, 2, 1, 2, 4], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1262 ⟨![[0], [1], [], [0, 2, 4, 6], [1, 2, 3], [2, 3, 6]], ![[0], [1], [0, 1, 1, 1, 0, 1], [0, 1, 1, 1, 0, 4], [0, 1, 1, 1, 3, 1], [0, 4, 0, 4], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 1265 ⟨![[], [1], [0, 2, 4], [], [1, 2], [0]], ![[5], [1], [1, 1, 1, 4], [1, 1, 1, 4, 5, 2], [1, 1, 2, 4, 2, 4], [1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1263 ⟨![[0], [], [1, 3, 5], [0, 2, 6], [2, 5], [1]], ![[0], [5], [0, 4, 3, 4], [0, 3, 2, 5], [0, 2, 0, 2, 4], [0, 4, 3], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 1267 ⟨![[], [0, 2, 1], [0, 2, 4], [], [0, 1, 6], [0]], ![[5], [1, 5], [1, 1, 1, 4], [1, 1, 1, 2, 5, 4], [1, 1, 2, 4, 5, 4], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 111) : Classified H :=
  classify_of_checks 111 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node111

namespace Node112

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [5]],
   ![[0], [1], [2], [2, 2], [1, 1, 2, 1, 2, 1], [3], [1, 0, 1, 0], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 111) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 112 :=
  generated_of_packed 111 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 1270 ⟨![[], [0], [1], [2], [], [0, 3], [1, 3], [2]], ![[1], [2], [3], [2, 2], [1, 1, 1, 6, 1, 6], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .core, .edge 1272 ⟨![[], [0, 3], [1], [2], [], [0], [1, 3], [2]], ![[5], [2], [3], [2, 2], [1, 1, 1, 2, 1, 6], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 1268 ⟨![[0], [1], [], [2], [0, 3], [3, 1, 4], [3], [2, 6]], ![[0], [1], [3], [6], [1, 1, 1, 6, 5], [1, 1, 6], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1271 ⟨![[], [1], [0, 3], [2], [], [1, 3], [0], [2]], ![[6], [1], [3], [2, 6], [1, 1, 1, 6, 1, 6], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 1269 ⟨![[0], [], [1, 4, 5], [2], [0, 3, 6], [3, 5], [1], [2]], ![[0], [6], [3], [2, 6], [2, 2, 5], [0, 5, 4], [0, 2, 6, 4], [0, 2, 6, 4], [0, 2, 6, 4], [0, 2, 6, 4]]⟩, .edge 1273 ⟨![[], [1, 0], [0, 3], [2], [], [1, 0, 3], [0], [2]], ![[6], [1, 6], [3], [2, 6], [1, 1, 1, 2, 1, 6], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 112) : Classified H :=
  classify_of_checks 112 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node112

namespace Node113

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 2, 2, 0, 3], [0, 1, 0, 1, 1, 3, 1], [0, 1, 0, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 112) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 113 :=
  generated_of_packed 112 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 1280 ⟨![[], [0], [1], [2, 3], [], [0, 3], [1, 3], [2, 3]], ![[1], [2], [1, 1, 1, 5, 3], [1, 1, 1, 5], [2, 6], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .core, .edge 1284 ⟨![[], [0, 3], [1], [2, 3], [], [0], [1, 3], [2, 3]], ![[5], [2], [1, 1, 1, 5, 3], [1, 1, 1, 5], [2, 6], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 1275 ⟨![[0], [1], [], [2, 3], [0, 3, 6], [1, 3], [3, 4], [2, 3]], ![[0], [1], [0, 3, 6, 4, 6], [0, 6, 4, 6], [0, 6, 4], [1, 5], [0, 6, 0, 6], [0, 6, 0, 6], [0, 6, 0, 6], [0, 6, 0, 6]]⟩, .edge 1282 ⟨![[], [1], [0, 3], [2, 3], [], [1, 3], [0], [2, 3]], ![[6], [1], [1, 1, 1, 5, 3], [1, 1, 1, 5], [2, 2], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 1278 ⟨![[0], [], [5, 1], [2, 3], [0, 3, 6], [3, 5], [1], [2, 3, 6]], ![[0], [6], [0, 4, 7], [0, 3, 4, 7], [2, 5, 2], [0, 5, 4], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1286 ⟨![[], [4, 1, 0], [0, 3], [2, 3], [], [0, 1, 4], [0], [2, 3]], ![[6], [1, 6], [1, 1, 1, 5, 3], [1, 1, 1, 5], [2, 2], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 1274 ⟨![[0], [1], [2], [], [0], [1, 6], [2], []], ![[0], [1], [2], [0, 1, 0, 1, 1, 5], [2, 0, 2, 0], [0, 1, 0, 5], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5]]⟩, .edge 1281 ⟨![[], [1], [2], [0, 3], [], [1, 3], [2, 3], [0, 3]], ![[1, 1, 1, 5, 3], [1], [2], [1, 1, 1, 5], [2, 6], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 1277 ⟨![[0], [], [2], [5, 1], [0, 3, 6], [1, 1], [2, 3], [1, 3]], ![[0], [0, 4, 7], [2], [0, 3, 0, 7], [2, 6], [0, 5, 4], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 1285 ⟨![[], [1, 0], [2], [0, 3], [], [0, 1], [2, 3], [0, 3]], ![[1, 1, 1, 5, 3], [5, 3], [2], [1, 1, 1, 5], [2, 6], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 1276 ⟨![[0], [1], [], [2, 4], [0, 3, 6], [1, 3], [3, 4], [2, 3]], ![[0], [1], [0, 4, 7], [0, 3, 0, 7], [0, 6, 4], [1, 5], [0, 6, 0, 6], [0, 6, 0, 6], [0, 6, 0, 6], [0, 6, 0, 6]]⟩, .edge 1283 ⟨![[], [1], [2, 0], [0, 3], [], [1, 3], [0, 2, 6], [0, 3]], ![[1, 1, 1, 5, 3], [1], [3, 2], [1, 1, 1, 5], [2, 2], [1, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩, .edge 1279 ⟨![[0], [], [1, 2, 5], [5, 1], [0, 3, 6], [1, 1], [1, 2, 6], [1, 3]], ![[0], [0, 4, 7], [3, 5, 2], [0, 3, 0, 7], [2, 5, 2], [0, 5, 4], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 1287 ⟨![[], [1, 0], [2, 0], [0, 3], [], [0, 1], [0, 2, 6], [0, 3]], ![[1, 1, 1, 5, 3], [5, 3], [3, 2], [1, 1, 1, 5], [2, 2], [1, 1], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5], [1, 1, 5, 5]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 113) : Classified H :=
  classify_of_checks 113 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node113

namespace Node114

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [4]],
   ![[0], [1], [2], [2, 2], [3], [1, 2, 1, 1, 1, 2], [0, 1, 0, 1], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 113) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 114 :=
  generated_of_packed 113 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 1290 ⟨![[], [0], [1], [2], [], [0, 3], [1, 1, 1], [2, 6]], ![[1], [2], [3], [1, 1, 1, 5], [1, 1, 1, 5, 2, 2], [1, 5], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .core, .edge 1292 ⟨![[], [0, 3], [1], [2], [], [0], [1, 1, 1], [2, 6]], ![[5], [2], [3], [1, 1, 1, 5], [1, 1, 1, 5, 2, 2], [1, 1], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1288 ⟨![[0], [1], [], [2], [0, 3, 4], [3, 1], [3, 4], [2, 6]], ![[0], [1], [3], [1, 1, 5, 1], [1, 1, 1, 6, 5], [5, 1], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1291 ⟨![[], [1], [0, 3, 4], [2], [], [1, 3], [0], [2, 6]], ![[6], [1], [3], [1, 1, 1, 5], [1, 1, 1, 5, 2, 6], [1, 5], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1289 ⟨![[0], [], [1, 5], [2], [0, 3, 6], [3, 5], [1], [2]], ![[0], [6], [3], [0, 3, 4, 3], [2, 2, 5], [0, 5, 4], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 1293 ⟨![[], [1, 0], [0, 3, 4], [2], [], [0, 4, 1], [0], [2, 6]], ![[6], [1, 6], [3], [1, 1, 1, 5], [1, 1, 1, 5, 2, 6], [1, 1], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 160, .noncentric 160, .noncentric 160, .noncentric 160, .noncentric 160, .noncentric 160, .noncentric 160, .noncentric 160] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 114) : Classified H :=
  classify_of_checks 114 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node114

namespace Node115

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [5]],
   ![[0], [1], [2], [0, 1, 0, 1, 1, 1], [0, 1, 1, 1, 0, 1, 2, 2], [3], [0, 1, 0, 1], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 114) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 115 :=
  generated_of_packed 114 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 1300 ⟨![[], [0], [1], [2], [], [0, 3], [1, 3, 4], [2]], ![[1], [2], [3], [1, 1, 1, 5], [1, 1, 2, 2, 5, 1], [1, 5], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .core, .edge 1304 ⟨![[], [0, 3], [1], [2], [], [0], [1, 3, 4], [2]], ![[5], [2], [3], [1, 1, 1, 5], [1, 1, 2, 2, 5, 1], [1, 1], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1295 ⟨![[0], [1], [], [2], [0, 3, 4], [1, 3, 4], [3, 4, 6], [2, 6]], ![[0], [1], [3], [0, 1, 1, 1, 0, 1], [0, 1, 1, 1, 0, 5], [1, 0, 1, 0], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1302 ⟨![[], [1], [0, 3, 4], [2], [], [1, 3], [0], [2]], ![[6], [1], [3], [1, 1, 1, 5], [1, 1, 2, 1, 2, 1], [1, 5], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1298 ⟨![[0], [], [1, 4, 5], [2], [0, 3, 6], [3, 5], [1], [2]], ![[0], [6], [3], [0, 5, 4, 5], [0, 2, 6, 4], [0, 5, 4], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 1306 ⟨![[], [0, 3, 1], [0, 3, 4], [2], [], [0, 1, 6], [0], [2]], ![[6], [1, 6], [3], [1, 1, 1, 5], [1, 1, 2, 1, 5, 6], [1, 1], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1294 ⟨![[0], [1], [2], [], [0], [1], [2, 6], []], ![[0], [1], [2], [0, 1, 1, 1, 0, 1], [0, 1, 0, 1, 1, 1, 2, 2], [1, 0, 1, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1301 ⟨![[], [1], [2], [0], [], [1, 3], [2, 3, 4], [0]], ![[3], [1], [2], [1, 1, 1, 5], [1, 1, 2, 2, 5, 1], [1, 5], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1297 ⟨![[0], [], [2], [1, 1, 1], [0, 3, 6], [1, 1], [0, 2, 0], [1]], ![[0], [7], [2], [0, 2, 4, 2], [0, 2, 2, 4], [0, 5, 4], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1305 ⟨![[], [1, 0], [2], [0], [], [0, 1], [2, 3, 4], [0]], ![[3], [1, 3], [2], [1, 1, 1, 5], [1, 1, 2, 2, 5, 1], [1, 1], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1296 ⟨![[0], [1], [], [0, 2, 0], [0, 2, 2], [1, 2, 2], [2, 2, 6], [2]], ![[0], [1], [7], [0, 1, 1, 1, 0, 1], [0, 1, 1, 1, 0, 5], [1, 0, 1, 0], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 1303 ⟨![[], [1], [2, 0], [0], [], [1, 3], [0, 2, 6], [0]], ![[3], [1], [2, 3], [1, 1, 1, 5], [1, 1, 2, 1, 2, 1], [1, 5], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1299 ⟨![[0], [], [1, 1, 2, 1], [1, 1, 1], [0, 3, 6], [1, 1], [1, 2, 6], [1]], ![[0], [7], [2, 7], [0, 3, 0, 7], [0, 2, 6, 4], [0, 5, 4], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 1307 ⟨![[], [1, 0], [2, 0], [0], [], [0, 1], [0, 2, 6], [0]], ![[3], [1, 3], [2, 3], [1, 1, 1, 5], [1, 1, 2, 1, 5, 6], [1, 1], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 115) : Classified H :=
  classify_of_checks 115 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node115

namespace Node116

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [2, 2], [1, 1, 2, 1, 2, 1], [0, 1, 1, 2, 1, 0, 2, 1], [0, 1, 0, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 115) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 116 :=
  generated_of_packed 115 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1310 ⟨![[], [0], [1], [], [2, 0], [2, 3, 1, 4]], ![[1], [2], [2, 2], [1, 1, 2, 1, 2, 1], [1, 1, 2, 1, 5, 4], [4, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 1312 ⟨![[], [2, 0], [1], [], [0], [2, 3, 1, 4]], ![[4], [2], [2, 2], [1, 1, 2, 1, 5, 1], [1, 1, 2, 1, 2, 4], [4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1308 ⟨![[0], [1], [], [0, 2, 3, 4, 6], [2, 1, 3], [2]], ![[0], [1], [5], [1, 1, 1, 5, 4], [0, 1, 1, 1, 4, 3], [1, 1, 5], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩, .edge 1311 ⟨![[], [1], [0, 0, 0, 2], [], [2, 1], [0]], ![[5], [1], [2, 5], [1, 1, 2, 4, 5, 1], [1, 1, 2, 4, 2, 4], [4, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1309 ⟨![[0], [], [1, 3, 5], [0, 2], [2, 5], [1]], ![[0], [5], [0, 3], [2, 2, 4], [0, 2, 0, 2, 4], [0, 3, 4], [0, 3, 5, 2], [0, 3, 5, 2], [0, 3, 5, 2], [0, 3, 5, 2]]⟩, .edge 1313 ⟨![[], [0, 1, 2, 3], [0, 0, 0, 2], [], [3, 0, 1], [0]], ![[5], [1, 5], [2, 5], [1, 1, 2, 4, 2, 1], [1, 1, 2, 4, 5, 4], [4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 116) : Classified H :=
  classify_of_checks 116 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node116

namespace Node117

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [2, 2], [0, 1, 1, 1, 2, 0, 2, 1, 2, 2], [1, 2, 1, 1, 1, 2], [1, 0, 1, 0], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 116) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 117 :=
  generated_of_packed 116 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1316 ⟨![[], [0], [1], [], [2, 0, 4], [2, 3, 1, 4]], ![[1], [2], [2, 2], [1, 1, 1, 2, 1, 2, 2, 5], [1, 1, 1, 2, 2, 4], [1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 1318 ⟨![[], [2, 0, 4], [1], [], [0], [2, 3, 1, 4]], ![[4], [2], [2, 2], [1, 1, 1, 2, 1, 2, 2, 2], [1, 1, 1, 2, 2, 4], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1314 ⟨![[0], [1], [], [0, 1, 1, 3, 5], [0, 1, 0], [2]], ![[0], [1], [5], [0, 1, 1, 1, 4, 3], [1, 1, 1, 5, 4], [1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1317 ⟨![[], [1], [0, 0, 0, 2], [], [2, 1, 4], [0]], ![[5], [1], [2, 5], [1, 1, 1, 2, 2, 2, 4, 5], [1, 1, 1, 2, 5, 4], [1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1315 ⟨![[0], [], [5, 1], [0, 2, 4], [1, 4, 1], [1]], ![[0], [5], [2, 5], [0, 2, 0, 2, 5, 5], [2, 2, 4], [0, 4, 3], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 1319 ⟨![[], [0, 1, 2], [0, 0, 0, 2], [], [0, 4, 1], [0]], ![[5], [1, 5], [2, 5], [1, 1, 1, 2, 2, 2, 4, 2], [1, 1, 1, 2, 5, 4], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 117) : Classified H :=
  classify_of_checks 117 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node117

namespace Node118

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 1, 2, 1, 2, 2, 0, 2], [0, 1, 2, 1, 0, 2], [1, 2, 1, 2, 2, 2], [1, 1, 2, 2], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 117) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 118 :=
  generated_of_packed 117 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1322 ⟨![[], [0], [1], [], [0, 0, 0, 6], [1, 2, 4]], ![[1], [2], [1, 2, 1, 2, 2, 5], [1, 5, 1, 2], [1, 2, 1, 2, 2, 2], [1, 1, 2, 2], [1, 4], [1, 4], [1, 4], [1, 4]]⟩, .core, .edge 1324 ⟨![[], [0, 2, 3, 5], [1], [], [0], [1, 2, 4]], ![[4], [2], [1, 2, 2, 5, 4, 5], [1, 2, 4, 2], [1, 2, 2, 5, 4, 2], [1, 2, 2, 4], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1320 ⟨![[0], [1], [], [0, 2, 4, 6], [1, 1, 1, 4], [1, 1, 5]], ![[0], [1], [0, 1, 1, 1, 3, 4], [0, 1, 4, 3, 5], [1, 4], [1, 1, 5], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 1323 ⟨![[], [1], [0, 2, 4], [], [1, 1, 1, 6], [0]], ![[5], [1], [1, 2, 2, 5, 4, 2], [1, 5, 4, 5], [1, 2, 2, 5, 4, 5], [1, 1, 2, 5], [1, 4], [1, 4], [1, 4], [1, 4]]⟩, .edge 1321 ⟨![[0], [], [4, 1], [0, 2, 3, 5], [1, 1, 4, 5], [1]], ![[0], [5], [0, 2, 2, 5, 3, 2], [0, 5, 3, 5], [2, 2, 5, 2], [2, 4, 5], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4]]⟩, .edge 1325 ⟨![[], [0, 0, 1, 0], [0, 2, 4], [], [0, 1, 4, 5], [0]], ![[5], [1, 5], [1, 2, 1, 2, 5, 5], [1, 2, 1, 5], [1, 2, 1, 2, 5, 2], [1, 2, 5, 4], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 118) : Classified H :=
  classify_of_checks 118 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node118

namespace Node119

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 0, 2, 1, 2, 0], [2, 1, 1, 2], [1, 2, 1, 3, 2], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 118) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 119 :=
  generated_of_packed 118 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 1328 ⟨![[], [0], [1], [1, 1, 2, 4], [], [0, 3], [1, 1, 1], [1, 1, 2, 4]], ![[1], [2], [1, 2, 1, 3, 2], [1, 1, 1, 5], [2, 1, 6, 1], [2, 1, 1, 2], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .core, .edge 1330 ⟨![[], [0, 3], [1], [1, 1, 2, 4], [], [0], [1, 1, 1], [1, 1, 2, 4]], ![[5], [2], [1, 2, 3, 5, 6], [1, 1, 1, 5], [2, 1, 2, 5], [2, 1, 5, 2], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1326 ⟨![[0], [1], [], [2, 3, 4, 5], [0, 3, 5], [1, 3, 4], [3, 5], [1, 1, 2, 4, 5]], ![[0], [1], [1, 5, 6, 7], [5, 5], [5, 1], [5, 5, 6], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1329 ⟨![[], [1], [0, 3, 5], [2, 3, 4, 5], [], [1, 3], [0], [2, 3, 4, 5]], ![[6], [1], [1, 2, 3, 5, 6], [1, 1, 1, 5], [2, 5, 2, 1], [2, 1, 1, 6], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1327 ⟨![[0], [], [1, 4, 6], [1, 2, 1], [0, 3], [3, 6], [1], [1, 2, 1]], ![[0], [6], [2, 3, 2], [0, 4], [0, 6, 4, 6], [2, 5, 6], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 1331 ⟨![[], [1, 0], [0, 3, 5], [1, 2, 1], [], [1, 0, 3], [0], [1, 2, 1]], ![[6], [1, 6], [1, 2, 1, 3, 2], [1, 1, 1, 5], [2, 5, 6, 5], [2, 1, 5, 6], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .noncentric 96, .noncentric 96, .noncentric 96, .noncentric 96, .noncentric 96, .noncentric 96, .noncentric 96, .noncentric 96] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 119) : Classified H :=
  classify_of_checks 119 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node119

namespace Node120

def gen : Fin 5 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [3], [5]],
   ![[0], [1], [2], [3], [0, 0, 1, 3, 1], [4], [1, 1, 3], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 119) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 120 :=
  generated_of_packed 119 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .edge 1346 ⟨![[], [0], [1], [0, 0, 3], [2], [5], [0, 4], [0, 0, 1], [0, 3, 0], [2]], ![[1], [2], [4], [1, 1, 3], [1, 1, 1, 6], [5], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .core, .edge 1354 ⟨![[], [0, 4, 5], [1], [1, 1, 3, 5], [2], [5], [0], [1, 1, 1, 5], [3, 4, 5], [2]], ![[6], [2], [4], [1, 3, 6], [1, 1, 2, 2], [5], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1335 ⟨![[0], [1], [], [1, 1, 3], [2], [0, 1, 1], [1, 4], [4, 6], [1, 1, 3], [2, 6]], ![[0], [1], [4], [1, 1, 3], [4, 7, 9], [0, 0], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 1350 ⟨![[], [1], [0, 4, 6], [1, 1, 3], [2], [5], [1, 4], [0], [1, 3, 1], [2]], ![[7], [1], [4], [1, 1, 3], [1, 1, 1, 6], [5], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 1342 ⟨![[0], [], [1, 5, 6], [1, 3, 1], [2], [0, 4], [1, 1, 6], [1], [1, 1, 3], [2]], ![[0], [7], [4], [3, 6], [0, 0, 0, 5], [0, 0], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 1358 ⟨![[], [1, 0], [0, 4, 6], [1, 3, 1], [2], [5], [0, 1, 6], [0], [1, 1, 3], [2]], ![[7], [1, 7], [4], [1, 3, 6], [1, 1, 2, 7], [5], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1332 ⟨![[0], [1], [2], [], [3], [0, 6], [1, 6], [2], [], [3]], ![[0], [1], [2], [4], [0, 0, 1, 6], [0, 0], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 1347 ⟨![[], [1], [2], [0, 4], [3], [5], [1, 4], [1, 1, 2], [0, 1, 1], [3]], ![[1, 1, 8], [1], [2], [4], [1, 1, 1, 6], [5], [1, 5, 6], [1, 5, 6], [1, 5, 6], [1, 5, 6]]⟩, .edge 1339 ⟨![[0], [], [2], [1, 6], [3], [0, 4], [1, 1, 6], [2, 4], [0, 1, 0], [3]], ![[0], [6, 8], [2], [4], [0, 0, 0, 5], [0, 0], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 1355 ⟨![[], [0, 0, 1, 0], [2], [0, 4], [3], [5], [0, 1, 6], [0, 0, 2, 4], [0, 0, 0, 4], [3]], ![[1, 6, 8], [3, 1], [2], [4], [1, 1, 2, 2], [5], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1336 ⟨![[0], [1], [], [2, 5], [3], [0, 1, 1], [1, 4], [2, 2], [1, 1, 2], [3, 6]], ![[0], [1], [0, 0, 3], [4], [4, 7, 9], [0, 0], [4, 9], [4, 9], [4, 9], [4, 9]]⟩, .edge 1351 ⟨![[], [1], [0, 0, 2, 0], [0, 4], [3], [5], [1, 4], [0, 2], [0, 1, 1], [3]], ![[1, 1, 8], [1], [3, 2, 5], [4], [1, 1, 1, 6], [5], [1, 5, 6], [1, 5, 6], [1, 5, 6], [1, 5, 6]]⟩, .edge 1343 ⟨![[0], [], [1, 1, 2, 1], [1, 6], [3], [0, 4], [1, 1, 6], [1, 2], [0, 1, 0], [3]], ![[0], [6, 8], [2, 6, 8], [4], [0, 0, 0, 5], [0, 0], [0, 5, 6], [0, 5, 6], [0, 5, 6], [0, 5, 6]]⟩, .edge 1359 ⟨![[], [0, 0, 1, 0], [0, 0, 2, 0], [0, 4], [3], [5], [0, 1, 6], [0, 2], [0, 0, 0, 4], [3]], ![[1, 6, 8], [3, 1], [3, 2, 5], [4], [1, 1, 2, 7], [5], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1333 ⟨![[0], [1], [2], [1, 1, 3], [], [0], [1], [2, 6], [1, 1, 3], []], ![[0], [1], [2], [1, 1, 3], [2, 7], [0, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 1348 ⟨![[], [1], [2], [1, 1, 3], [0, 5], [5], [1, 4], [1, 1, 2], [1, 3, 1], [0]], ![[9], [1], [2], [1, 1, 3], [1, 1, 1, 6], [5], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 1340 ⟨![[0], [], [2], [1, 1, 3], [1, 1, 1], [0, 4], [1, 1], [2, 4], [1, 3, 1], [1]], ![[0], [9], [2], [3, 6], [0, 0, 0, 5], [0, 0], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 1356 ⟨![[], [1, 0, 5], [2], [1, 1, 3], [0, 5], [5], [0, 1], [1, 1, 2], [1, 3, 1], [0]], ![[9], [1, 9], [2], [1, 3, 6], [1, 1, 2, 2], [5], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1337 ⟨![[0], [1], [], [1, 1, 3], [2, 4], [0, 1, 1], [1, 4], [4, 6], [1, 1, 3], [2]], ![[0], [1], [9], [1, 1, 3], [4, 4], [0, 0], [4, 4, 7], [4, 4, 7], [4, 4, 7], [4, 4, 7]]⟩, .edge 1352 ⟨![[], [1], [0, 2, 4], [1, 1, 3], [0, 5], [5], [1, 4], [0, 2, 6], [1, 3, 1], [0]], ![[9], [1], [2, 9], [1, 1, 3], [1, 1, 1, 6], [5], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 1344 ⟨![[0], [], [1, 2, 5], [1, 1, 3], [1, 1, 1], [0, 4], [1, 1], [1, 2, 6], [1, 3, 1], [1]], ![[0], [9], [2, 9], [3, 6], [0, 0, 0, 5], [0, 0], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 1360 ⟨![[], [1, 0, 5], [0, 2, 4], [1, 1, 3], [0, 5], [5], [0, 1], [0, 2, 6], [1, 3, 1], [0]], ![[9], [1, 9], [2, 9], [1, 3, 6], [1, 1, 2, 7], [5], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1334 ⟨![[0], [1], [2], [], [1, 1, 3], [0, 6], [1, 6], [2], [], [1, 1, 3]], ![[0], [1], [2], [1, 1, 4], [0, 0, 1, 6], [0, 0], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 1349 ⟨![[], [1], [2], [0, 4], [0, 3, 5], [5], [1, 4], [1, 1, 2], [0, 1, 1], [0, 3]], ![[1, 1, 8], [1], [2], [1, 1, 3, 9], [1, 1, 1, 6], [5], [1, 5, 6], [1, 5, 6], [1, 5, 6], [1, 5, 6]]⟩, .edge 1341 ⟨![[0], [], [2], [1, 6], [0, 1, 0, 3], [0, 4], [1, 1, 6], [2, 4], [0, 1, 0], [1, 3]], ![[0], [6, 8], [2], [3, 4], [0, 0, 0, 5], [0, 0], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 1357 ⟨![[], [0, 0, 1, 0], [2], [0, 4], [0, 3, 5], [5], [0, 1, 6], [0, 0, 2, 4], [0, 0, 0, 4], [0, 3]], ![[1, 6, 8], [3, 1], [2], [1, 3, 1, 4], [1, 1, 2, 2], [5], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1338 ⟨![[0], [1], [], [2, 5], [2, 3, 4], [0, 1, 1], [1, 4], [2, 2], [1, 1, 2], [2, 3]], ![[0], [1], [0, 0, 3], [0, 0, 4, 3], [4, 4], [0, 0], [4, 4, 7], [4, 4, 7], [4, 4, 7], [4, 4, 7]]⟩, .edge 1353 ⟨![[], [1], [0, 0, 2, 0], [0, 4], [0, 3, 5], [5], [1, 4], [0, 2], [0, 1, 1], [0, 3]], ![[1, 1, 8], [1], [3, 2, 5], [1, 1, 3, 9], [1, 1, 1, 6], [5], [1, 5, 6], [1, 5, 6], [1, 5, 6], [1, 5, 6]]⟩, .edge 1345 ⟨![[0], [], [1, 1, 2, 1], [1, 6], [0, 1, 0, 3], [0, 4], [1, 1, 6], [1, 2], [0, 1, 0], [1, 3]], ![[0], [6, 8], [2, 6, 8], [3, 4], [0, 0, 0, 5], [0, 0], [0, 5, 6], [0, 5, 6], [0, 5, 6], [0, 5, 6]]⟩, .edge 1361 ⟨![[], [0, 0, 1, 0], [0, 0, 2, 0], [0, 4], [0, 3, 5], [5], [0, 1, 6], [0, 2], [0, 0, 0, 4], [0, 3]], ![[1, 6, 8], [3, 1], [3, 2, 5], [1, 3, 1, 4], [1, 1, 2, 7], [5], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 5 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 120) : Classified H :=
  classify_of_checks 120 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node120

namespace Node121

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 1, 0, 2, 1, 2, 2, 2], [0, 0, 1, 2, 1, 2, 2, 2], [0, 0, 0, 2, 0, 1, 2, 1], [1, 2, 2, 2, 1, 2], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 120) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 121 :=
  generated_of_packed 120 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1364 ⟨![[], [0], [1], [3, 5, 6], [0, 2, 3], [1, 2, 3]], ![[1], [2], [1, 2, 1, 2, 2, 3, 5], [1, 2, 1, 2, 2, 2, 3], [1, 2, 4, 2], [1, 2, 1, 2, 5, 5], [1, 3, 4], [1, 3, 4], [1, 3, 4], [1, 3, 4]]⟩, .core, .edge 1366 ⟨![[], [0, 2, 5, 6], [1], [3, 5, 6], [0], [1, 2, 3]], ![[4], [2], [1, 2, 1, 2, 2, 5], [1, 2, 1, 2, 2, 2], [1, 2, 4, 2], [1, 2, 2, 2, 4, 5], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1362 ⟨![[0], [1], [], [2, 0, 3], [2, 1], [0, 2, 0, 4]], ![[0], [1], [0, 1, 0, 4], [0, 0, 1, 4], [0, 0, 0, 1, 0, 5, 4], [4, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 1365 ⟨![[], [1], [1, 1, 0], [3, 5, 6], [1, 2, 3], [0]], ![[5], [1], [1, 2, 2, 5, 4, 2], [1, 2, 1, 2, 5, 2], [1, 2, 1, 5], [1, 2, 2, 2, 4, 2], [1, 3, 4], [1, 3, 4], [1, 3, 4], [1, 3, 4]]⟩, .edge 1363 ⟨![[0], [], [1, 5], [0, 2, 3], [2, 5], [1]], ![[0], [5], [2, 2, 2, 5, 4], [0, 0, 2, 2, 5, 2], [0, 0, 2, 4, 2], [2, 2, 2, 5], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4]]⟩, .edge 1367 ⟨![[], [0, 0, 1, 0], [2, 5, 0], [3, 5, 6], [0, 0, 0, 5, 1], [0]], ![[5], [1, 5], [1, 2, 1, 2, 5, 5], [1, 2, 1, 2, 3, 5, 2], [1, 2, 1, 3, 5], [1, 2, 1, 2, 2, 5], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 121) : Classified H :=
  classify_of_checks 121 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node121

namespace Node122

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0, 1, 1], [0, 0, 0, 1, 0, 1], [2, 1, 1, 2], [1, 0, 1, 0], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 121) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 122 :=
  generated_of_packed 121 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1370 ⟨![[], [0], [1], [0, 0, 2], [0, 2, 5], [1, 2, 3]], ![[1], [2], [1, 1, 3], [4, 1], [1, 1, 5, 5], [1, 3, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 1372 ⟨![[], [2, 0, 3], [1], [0, 0, 3], [0], [1, 2, 3]], ![[4], [2], [1, 3, 4], [3, 4, 4], [1, 1, 2, 5], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1368 ⟨![[0], [1], [], [2, 0, 3], [1, 2, 4, 5], [0, 2, 0, 4]], ![[0], [1], [0, 0, 1, 1], [0, 1, 1, 3], [4, 4, 5], [0, 4, 0, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1371 ⟨![[], [1], [2, 5, 0], [1, 1, 2], [1, 2, 5], [0]], ![[5], [1], [1, 1, 3], [4, 1], [1, 1, 5, 2], [1, 3, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1369 ⟨![[0], [], [3, 1, 4], [0, 1, 1], [0, 0, 2], [1]], ![[0], [5], [0, 0, 4], [2, 2, 4], [2, 4, 5], [0, 4, 3], [0, 2, 3, 2], [0, 2, 3, 2], [0, 2, 3, 2], [0, 2, 3, 2]]⟩, .edge 1373 ⟨![[], [0, 2, 1], [0, 1, 1], [3, 5, 6], [0, 1, 3], [0]], ![[5], [1, 5], [1, 3, 4], [3, 4, 4], [1, 2, 5, 4], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 122) : Classified H :=
  classify_of_checks 122 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node122

namespace Node123

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 2, 0, 2, 1, 1], [0, 2, 1, 2, 0, 1], [2, 1, 1, 2], [1, 0, 1, 0], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 122) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 123 :=
  generated_of_packed 122 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1376 ⟨![[], [0], [1], [], [0, 0, 0, 5], [1, 2, 4]], ![[1], [2], [1, 1, 5, 2], [1, 5, 4, 5], [1, 1, 5, 5], [1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 1378 ⟨![[], [1, 0, 1, 6], [1], [], [0], [1, 2, 4]], ![[4], [2], [1, 2, 5, 4], [1, 2, 1, 5], [1, 2, 2, 4], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1374 ⟨![[0], [1], [], [0, 2, 4, 6], [2, 5, 1], [2, 3, 6]], ![[0], [1], [0, 1, 0, 4], [0, 1, 1, 3], [4, 4, 5], [1, 0, 1, 0], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5], [0, 5, 0, 5]]⟩, .edge 1377 ⟨![[], [1], [0, 2, 4], [], [1, 1, 1, 5], [0]], ![[5], [1], [1, 1, 5, 5], [1, 5, 1, 2], [1, 1, 5, 2], [1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1375 ⟨![[0], [], [0, 1, 0, 4], [1, 0, 5, 1], [2, 3, 4], [1]], ![[0], [5], [0, 2, 3, 5, 4], [0, 2, 2, 3], [2, 4, 5], [0, 4, 3], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 1379 ⟨![[], [0, 1, 2, 4], [0, 2, 4], [], [0, 1, 3, 5], [0]], ![[5], [1, 5], [1, 2, 2, 4], [1, 2, 4, 2], [1, 2, 5, 4], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 123) : Classified H :=
  classify_of_checks 123 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node123

namespace Node124

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 1, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 1, 0, 1, 1, 2, 1, 2], [1, 1, 2, 2], [0, 1, 0, 1, 1, 2, 1, 2, 2, 2], [1, 0, 1, 0], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 123) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 124 :=
  generated_of_packed 123 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 1382 ⟨![[], [0], [1], [], [0, 0, 0, 5], [1, 2, 3, 5]], ![[1], [2], [1, 1, 1, 2, 4, 2], [1, 1, 2, 2], [1, 1, 1, 2, 2, 2, 4, 2], [1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .core, .edge 1384 ⟨![[], [0, 1, 1, 3, 5], [1], [], [0], [1, 2, 3, 5]], ![[4], [2], [1, 1, 1, 2, 4, 5], [1, 2, 2, 4], [1, 1, 1, 2, 2, 2, 4, 5], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1380 ⟨![[0], [1], [], [0, 2, 3, 5], [2, 3, 5, 1], [2, 4]], ![[0], [1], [0, 1, 0, 1, 1, 4, 5], [1, 1, 5], [0, 1, 0, 1, 1, 4], [0, 4, 0, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1383 ⟨![[], [1], [0, 2, 3, 5], [], [0, 2, 0, 1], [0]], ![[5], [1], [1, 1, 1, 2, 1, 5], [1, 1, 2, 5], [1, 1, 1, 2, 1, 2, 2, 2], [1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .edge 1381 ⟨![[0], [], [4, 1, 5], [1, 0, 1, 3], [2, 3, 4], [1]], ![[0], [5], [0, 5, 0, 2], [2, 5, 4], [0, 2, 2, 2, 0, 2], [0, 4, 3], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4], [0, 4, 0, 4]]⟩, .edge 1385 ⟨![[], [0, 2, 1], [0, 1, 3, 1], [], [1, 0, 2], [0]], ![[5], [1, 5], [1, 1, 1, 2, 1, 2], [1, 2, 1, 5], [1, 1, 1, 2, 1, 2, 2, 5], [1, 1], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 3 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 124) : Classified H :=
  classify_of_checks 124 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node124

end ReeTwo.SylowModel.SmallEvenMaximalLower
