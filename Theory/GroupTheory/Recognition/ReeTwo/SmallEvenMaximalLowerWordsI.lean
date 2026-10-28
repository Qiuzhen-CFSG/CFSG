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

namespace Node200

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 1, 0, 1, 1, 1, 3], [1, 0, 1, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 199) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 200 :=
  generated_of_packed 199 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 1997 ⟨![[], [0], [1], [2, 3, 5], [], [0, 3], [1, 5], [2, 3, 5]], ![[1], [2], [1, 1, 1, 3, 5], [1, 1, 1, 5], [1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .core, .edge 1998 ⟨![[], [0, 3], [1], [2, 3, 5], [], [0], [1, 5], [2, 3, 5]], ![[5], [2], [1, 1, 1, 3, 5], [1, 1, 1, 5], [1, 1], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 96, .noncentric 96, .noncentric 96, .noncentric 96, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 96, .noncentric 96, .noncentric 96, .noncentric 96] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 200) : Classified H :=
  classify_of_checks 200 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node200

namespace Node201

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [4], [5]],
   ![[0], [1], [0, 0], [0, 0, 0, 1, 0, 1], [2], [3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 200) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 201 :=
  generated_of_packed 200 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1999 ⟨![[0], [], [1], [2], [0, 4], [], [1], [2]], ![[0], [2], [3], [0, 0], [0, 0, 0, 4], [0, 0, 4, 4], [0, 0, 4, 4], [0, 0, 4, 4], [0, 0, 4, 4], [0, 0, 4, 4]]⟩, .edge 2000 ⟨![[], [0, 0, 0], [1], [2], [3], [0], [1], [2, 5]], ![[5], [2], [3], [4], [1, 1, 4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 201) : Classified H :=
  classify_of_checks 201 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node201

namespace Node202

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [4]],
   ![[0], [1], [0, 0], [0, 0, 0, 1, 1, 1, 0, 1], [2], [1, 1, 2], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 201) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 202 :=
  generated_of_packed 201 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .core, .edge 2001 ⟨![[0], [], [1, 4], [3, 0], [4], [1, 4]], ![[0], [2, 4], [0, 0], [0, 0, 3, 0], [4], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 2002 ⟨![[], [0, 2, 3], [1, 4], [2], [0], [1, 4]], ![[4], [1, 2, 4], [3], [1, 1, 1, 4, 3], [1, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4], [1, 1, 4, 4]]⟩, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 202) : Classified H :=
  classify_of_checks 202 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node202

namespace Node203

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [2, 2], [0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 202) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 203 :=
  generated_of_packed 202 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2004 ⟨![[0], [], [1], [2], [0], [], [1, 4], [0, 0, 2]], ![[0], [2], [3], [2, 2], [0, 3, 0, 3], [0, 3, 0, 7], [0, 3, 0, 7], [0, 3, 0, 7], [0, 3, 0, 7], [0, 3, 0, 7]]⟩, .edge 2011 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1], [0, 2, 0]], ![[5], [2], [3], [2, 2], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 2048, .edge 2009 ⟨![[], [1], [0, 4, 5], [2], [4, 5], [1], [0], [2, 3, 5]], ![[6], [1], [3], [2, 6], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2006 ⟨![[0], [], [1, 4], [2], [0], [], [1], [0, 0, 2]], ![[0], [6], [3], [2, 6], [0, 3, 0, 3], [0, 3, 0, 7], [0, 3, 0, 7], [0, 3, 0, 7], [0, 3, 0, 7], [0, 3, 0, 7]]⟩, .edge 2013 ⟨![[], [0, 0, 1, 0], [0, 4, 5], [2], [4, 5], [1, 0, 3], [0], [1, 2, 1]], ![[6], [1, 6], [3], [2, 6], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2003 ⟨![[0], [1], [2], [], [0, 3, 5], [0, 0, 1], [2], [3]], ![[0], [1], [2], [7], [0, 4, 7], [0, 0, 0, 4, 7], [0, 0, 0, 4, 7], [0, 0, 0, 4, 7], [0, 0, 0, 4, 7], [0, 0, 0, 4, 7]]⟩, .edge 2008 ⟨![[], [1], [2], [0, 3, 4], [4, 5], [1], [2], [0]], ![[7], [1], [2], [2, 2], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 2005 ⟨![[0], [], [2], [0, 0, 1], [0], [], [2, 4], [1]], ![[0], [7], [2], [2, 2], [0, 3, 0, 7], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 2012 ⟨![[], [0, 1, 3], [2], [0, 3, 4], [4, 5], [1, 0, 5], [2], [0]], ![[7], [1, 7], [2], [2, 2], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .noncentric 24, .edge 2010 ⟨![[], [1], [2, 0, 4], [0, 3, 4], [4, 5], [1], [0, 2, 3], [0]], ![[7], [1], [2, 7], [2, 6], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 2007 ⟨![[0], [], [0, 1, 0, 2], [0, 0, 1], [0], [], [1, 2, 3], [1]], ![[0], [7], [2, 7], [2, 6], [0, 3, 0, 7], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 2014 ⟨![[], [0, 1, 3], [2, 0, 4], [0, 3, 4], [4, 5], [1, 0, 5], [0, 2, 3], [0]], ![[7], [1, 7], [2, 7], [2, 6], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 203) : Classified H :=
  classify_of_checks 203 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node203

namespace Node204

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [2, 2], [0, 0, 0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 203) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 204 :=
  generated_of_packed 203 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2018 ⟨![[0], [], [1], [2], [0], [], [1, 4], [2]], ![[0], [2], [3], [2, 2], [2, 2, 2, 6], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 2025 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1], [2, 4]], ![[5], [2], [3], [2, 2], [3, 7], [3, 4, 7], [3, 4, 7], [3, 4, 7], [3, 4, 7], [3, 4, 7]]⟩, .edge 2016 ⟨![[0], [1], [], [2], [0], [1, 4], [3], [2, 5]], ![[0], [1], [3], [6], [1, 5], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2023 ⟨![[], [1], [0, 4, 5], [2], [4, 5], [1], [0], [2, 4]], ![[6], [1], [3], [2, 6], [3, 7], [3, 4, 7], [3, 4, 7], [3, 4, 7], [3, 4, 7], [3, 4, 7]]⟩, .edge 2020 ⟨![[0], [], [1, 4], [2], [0], [], [1], [2]], ![[0], [6], [3], [2, 6], [2, 2, 2, 6], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 2027 ⟨![[], [0, 0, 1, 0], [0, 4, 5], [2], [4, 5], [1, 0, 3], [0], [2, 4]], ![[6], [1, 6], [3], [2, 6], [3, 7], [3, 4, 7], [3, 4, 7], [3, 4, 7], [3, 4, 7], [3, 4, 7]]⟩, .edge 2015 ⟨![[0], [1], [2], [], [0, 4], [1], [2, 5], []], ![[0], [1], [2], [2, 2], [0, 0, 0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2022 ⟨![[], [1], [2], [0, 5], [4, 5], [1], [2], [0]], ![[7], [1], [2], [2, 2], [3, 3, 4], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2019 ⟨![[0], [], [2], [1], [0], [], [2, 4], [1]], ![[0], [3], [2], [2, 2], [2, 2, 2, 6], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 2026 ⟨![[], [1, 0, 5], [2], [0, 5], [4, 5], [0, 1], [2], [0]], ![[7], [1, 7], [2], [2, 2], [3, 3, 4], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2017 ⟨![[0], [1], [], [2, 2, 2], [0], [1, 4], [3], [2]], ![[0], [1], [7], [6], [1, 5], [3, 3, 6], [3, 3, 6], [3, 3, 6], [3, 3, 6], [3, 3, 6]]⟩, .edge 2024 ⟨![[], [1], [0, 2, 4], [0, 5], [4, 5], [1], [0, 2, 5], [0]], ![[7], [1], [2, 7], [2, 6], [3, 3, 4], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2021 ⟨![[0], [], [2, 1], [1], [0], [], [1, 2, 5], [1]], ![[0], [3], [2, 3], [2, 6], [2, 2, 2, 6], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 2028 ⟨![[], [1, 0, 5], [0, 2, 4], [0, 5], [4, 5], [0, 1], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [2, 6], [3, 3, 4], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 204) : Classified H :=
  classify_of_checks 204 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node204

namespace Node205

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [2, 2], [0, 2, 0, 2], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 204) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 205 :=
  generated_of_packed 204 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2030 ⟨![[0], [], [1], [2], [0], [], [0, 0, 1], [2]], ![[0], [2], [3], [2, 2], [0, 2, 0, 2], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 2036 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [0, 1, 0], [2, 4]], ![[5], [2], [3], [2, 2], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2029 ⟨![[0], [1], [], [2], [0, 3, 5], [0, 0, 1], [3], [2, 5]], ![[0], [1], [3], [6], [0, 4, 6], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2034 ⟨![[], [1], [0, 3, 4], [2], [4, 5], [1], [0], [2, 4]], ![[6], [1], [3], [2, 6], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2031 ⟨![[0], [], [0, 0, 1], [2], [0], [], [1], [2]], ![[0], [6], [3], [2, 6], [0, 2, 0, 6], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2038 ⟨![[], [0, 1, 3], [0, 3, 4], [2], [4, 5], [1, 0, 5], [0], [2, 4]], ![[6], [1, 6], [3], [2, 6], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .noncentric 2048, .edge 2033 ⟨![[], [1], [2], [0, 5], [4, 5], [1], [0, 2, 0], [0]], ![[7], [1], [2], [2, 2], [2, 4, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 2812, .edge 2037 ⟨![[], [1, 0, 5], [2], [0, 5], [4, 5], [0, 1], [0, 2, 0], [0]], ![[7], [1, 7], [2], [2, 2], [2, 4, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 2064, .edge 2035 ⟨![[], [1], [2, 0, 5], [0, 5], [4, 5], [1], [0, 2, 5], [0]], ![[7], [1], [2, 7], [2, 6], [2, 2], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2032 ⟨![[0], [], [2, 1], [1], [0], [], [1, 2, 5], [1]], ![[0], [3], [2, 3], [2, 6], [0, 2, 0, 6], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .noncentric 2988] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 205) : Classified H :=
  classify_of_checks 205 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node205

namespace Node206

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 2, 3, 0, 2, 3], [0, 0, 0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 205) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 206 :=
  generated_of_packed 205 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 100, .noncentric 36, .edge 2039 ⟨![[0], [1], [], [2], [0, 3, 5], [1, 5], [], [2]], ![[0], [1], [3], [0, 3, 4, 3], [0, 0, 1, 5], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2044 ⟨![[], [1], [0, 0, 0], [2], [4, 5], [1], [0], [2, 4]], ![[6], [1], [3], [2, 2, 3, 7], [3, 7], [3, 4, 7], [3, 4, 7], [3, 4, 7], [3, 4, 7], [3, 4, 7]]⟩, .edge 2041 ⟨![[0], [], [1, 5], [2], [0], [], [1], [2]], ![[0], [6], [3], [0, 0, 0, 2, 0, 2], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2047 ⟨![[], [0, 1, 4], [0, 0, 0], [2], [4, 5], [0, 1, 5], [0], [2, 4]], ![[6], [1, 6], [3], [1, 2, 5, 6], [3, 7], [3, 4, 7], [3, 4, 7], [3, 4, 7], [3, 4, 7], [3, 4, 7]]⟩, .noncentric 24, .edge 2043 ⟨![[], [1], [2], [0, 5], [4, 5], [1], [2, 3, 5], [0]], ![[7], [1], [2], [1, 2, 1, 6], [3, 3, 4], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2040 ⟨![[0], [], [2], [1], [0], [], [2, 5], [1]], ![[0], [3], [2], [0, 0, 0, 2, 0, 6], [0, 0, 2, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2046 ⟨![[], [1, 0, 5], [2], [0, 5], [4, 5], [0, 1], [2, 3, 5], [0]], ![[7], [1, 7], [2], [1, 2, 5, 2], [3, 3, 4], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .noncentric 8, .edge 2045 ⟨![[], [1], [2, 0, 5], [0, 5], [4, 5], [1], [0, 2], [0]], ![[7], [1], [2, 7], [1, 2, 1, 2, 4], [3, 3, 4], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2042 ⟨![[0], [], [2, 1], [1], [0], [], [1, 2], [1]], ![[0], [3], [2, 3], [0, 0, 0, 2, 0, 2], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2048 ⟨![[], [1, 0, 5], [2, 0, 5], [0, 5], [4, 5], [0, 1], [0, 2], [0]], ![[7], [1, 7], [2, 7], [1, 2, 5, 6], [3, 3, 4], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 206) : Classified H :=
  classify_of_checks 206 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node206

namespace Node207

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [2, 2], [0, 0, 0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 206) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 207 :=
  generated_of_packed 206 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2052 ⟨![[0], [], [1], [2], [0, 3, 5], [0, 0, 3], [1, 4], [2, 5]], ![[0], [2], [3], [2, 2], [0, 0, 3, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2059 ⟨![[], [0, 3, 4], [1], [2], [4, 5], [0], [1], [2, 4]], ![[5], [2], [3], [2, 2], [3, 7], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2050 ⟨![[0], [1], [], [2], [0], [1, 4], [3], [2, 5]], ![[0], [1], [3], [6], [0, 0, 3, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2057 ⟨![[], [1], [0, 4, 5], [2], [4, 5], [1, 3, 5], [0], [2, 4]], ![[6], [1], [3], [2, 6], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2054 ⟨![[0], [], [1, 3, 5], [2], [0, 3, 5], [0, 0, 3], [1], [2, 5]], ![[0], [6], [3], [2, 6], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2061 ⟨![[], [0, 1], [0, 4, 5], [2], [4, 5], [1, 0, 5], [0], [2, 4]], ![[6], [1, 6], [3], [2, 6], [3, 7], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2049 ⟨![[0], [1], [2], [], [0, 4], [1, 5], [2, 5], []], ![[0], [1], [2], [2, 2], [0, 0, 0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2056 ⟨![[], [1], [2], [0, 5], [4, 5], [0, 1, 0], [2], [0]], ![[7], [1], [2], [2, 2], [1, 5], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2053 ⟨![[0], [], [2], [1, 1, 1], [0, 3, 5], [0, 0, 3], [2, 4], [1]], ![[0], [7], [2], [2, 2], [0, 2, 2, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2060 ⟨![[], [1, 0, 5], [2], [0, 5], [4, 5], [0, 1, 5], [2], [0]], ![[7], [1, 7], [2], [2, 2], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2051 ⟨![[0], [1], [], [2, 2, 2], [0], [1, 4], [3], [2]], ![[0], [1], [7], [6], [1, 1, 1, 5], [1, 5, 6], [1, 5, 6], [1, 5, 6], [1, 5, 6], [1, 5, 6]]⟩, .edge 2058 ⟨![[], [1], [0, 2, 4], [0, 5], [4, 5], [0, 1, 0], [0, 2, 5], [0]], ![[7], [1], [2, 7], [2, 6], [1, 5], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2055 ⟨![[0], [], [1, 2, 3], [1, 1, 1], [0, 2, 2], [0, 0, 3], [1, 2, 5], [1]], ![[0], [7], [2, 7], [2, 6], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2062 ⟨![[], [1, 0, 5], [0, 2, 4], [0, 5], [4, 5], [0, 1, 5], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [2, 6], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 207) : Classified H :=
  classify_of_checks 207 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node207

namespace Node208

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [2, 2], [0, 0, 0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 207) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 208 :=
  generated_of_packed 207 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2066 ⟨![[0], [], [1], [2], [0, 4], [], [0, 0, 1], [2, 4]], ![[0], [2], [3], [2, 2], [0, 0, 0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2073 ⟨![[], [0, 5], [1], [2], [4, 5], [0], [1], [1, 2, 1, 4]], ![[5], [2], [3], [2, 2], [3, 7], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2064 ⟨![[0], [1], [], [2], [0], [0, 0, 1], [3], [2, 5]], ![[0], [1], [3], [6], [0, 1, 0, 5], [3, 3, 6], [3, 3, 6], [3, 3, 6], [3, 3, 6], [3, 3, 6]]⟩, .edge 2071 ⟨![[], [1], [0, 4, 5], [2], [4, 5], [1, 4], [0], [0, 0, 2]], ![[6], [1], [3], [2, 6], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2068 ⟨![[0], [], [0, 0, 1], [2], [0, 4], [], [1], [2, 4]], ![[0], [6], [3], [2, 6], [0, 0, 0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2075 ⟨![[], [0, 0, 1, 0], [0, 4, 5], [2], [4, 5], [0, 0, 0, 1], [0], [0, 0, 2]], ![[6], [1, 6], [3], [2, 6], [3, 7], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2063 ⟨![[0], [1], [2], [], [0, 0, 0, 3], [1, 4], [2, 5], [3, 5]], ![[0], [1], [2], [0, 4], [1, 5], [0, 4, 7], [0, 4, 7], [0, 4, 7], [0, 4, 7], [0, 4, 7]]⟩, .edge 2070 ⟨![[], [1], [2], [0, 3], [4, 5], [1, 4], [2], [0]], ![[7], [1], [2], [2, 2], [1, 5], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2067 ⟨![[0], [], [2], [1, 4], [0, 4], [], [0, 0, 2], [1]], ![[0], [7], [2], [2, 2], [0, 0, 0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2074 ⟨![[], [1, 0, 5], [2], [0, 3], [4, 5], [1, 0], [2], [0]], ![[7], [1, 7], [2], [2, 2], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2065 ⟨![[0], [1], [], [2, 3, 5], [0], [0, 0, 1], [3], [2]], ![[0], [1], [7], [6], [0, 1, 0, 5], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7]]⟩, .edge 2072 ⟨![[], [1], [2, 0, 5], [0, 3], [4, 5], [1, 4], [0, 2, 3], [0]], ![[7], [1], [2, 7], [2, 6], [1, 5], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2069 ⟨![[0], [], [1, 1, 1, 2], [1, 4], [0, 4], [], [1, 2, 3], [1]], ![[0], [7], [2, 7], [2, 6], [0, 0, 0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2076 ⟨![[], [1, 0, 5], [2, 0, 5], [0, 3], [4, 5], [1, 0], [0, 2, 3], [0]], ![[7], [1, 7], [2, 7], [2, 6], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 208) : Classified H :=
  classify_of_checks 208 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node208

namespace Node209

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [2, 2], [0, 0, 0, 1, 0, 1], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 208) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 209 :=
  generated_of_packed 208 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2080 ⟨![[0], [], [1], [2], [0, 4], [], [1, 4, 5], [2]], ![[0], [2], [3], [2, 2], [0, 0, 0, 4], [0, 2, 2, 4], [0, 2, 2, 4], [0, 2, 2, 4], [0, 2, 2, 4], [0, 2, 2, 4]]⟩, .edge 2087 ⟨![[], [0, 0, 0], [1], [2], [0, 0, 4], [0], [0, 0, 1], [2, 4, 5]], ![[5], [2], [3], [2, 2], [1, 1, 4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2078 ⟨![[0], [1], [], [2], [0, 3, 5], [1, 4, 5], [3], [2, 5]], ![[0], [1], [3], [6], [0, 4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2085 ⟨![[], [1], [0, 4], [2], [0, 0, 5], [1, 4], [0], [2, 4, 5]], ![[6], [1], [3], [2, 6], [1, 5], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2082 ⟨![[0], [], [1, 4, 5], [2], [0, 4], [], [1], [2]], ![[0], [6], [3], [2, 6], [0, 0, 0, 4], [0, 2, 6, 4], [0, 2, 6, 4], [0, 2, 6, 4], [0, 2, 6, 4], [0, 2, 6, 4]]⟩, .edge 2089 ⟨![[], [0, 1, 4], [0, 4], [2], [1, 1], [0, 1, 1, 1], [0], [2, 4, 5]], ![[6], [1, 6], [3], [2, 6], [1, 1, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2077 ⟨![[0], [1], [2], [], [0, 4, 5], [1], [2, 5], []], ![[0], [1], [2], [0, 4], [0, 0, 2, 6], [0, 2, 6, 4], [0, 2, 6, 4], [0, 2, 6, 4], [0, 2, 6, 4], [0, 2, 6, 4]]⟩, .edge 2084 ⟨![[], [1], [2], [0, 3], [3, 4, 5], [1, 4], [2, 3, 5], [0]], ![[7], [1], [2], [2, 2], [1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2081 ⟨![[0], [], [2], [1], [0, 4], [], [2, 4, 5], [1]], ![[0], [3], [2], [2, 2], [0, 0, 0, 4], [0, 2, 2, 4], [0, 2, 2, 4], [0, 2, 2, 4], [0, 2, 2, 4], [0, 2, 2, 4]]⟩, .edge 2088 ⟨![[], [1, 0, 3], [2], [0, 3], [3, 4, 5], [0, 1], [2, 3, 5], [0]], ![[7], [1, 7], [2], [2, 2], [1, 1, 4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2079 ⟨![[0], [1], [], [2, 2, 2], [0, 2, 2], [1, 4, 5], [3], [2]], ![[0], [1], [7], [6], [0, 4], [3, 3, 6], [3, 3, 6], [3, 3, 6], [3, 3, 6], [3, 3, 6]]⟩, .edge 2086 ⟨![[], [1], [2, 0, 3], [0, 3], [2, 2, 4], [1, 4], [0, 2, 5], [0]], ![[7], [1], [2, 7], [2, 6], [1, 5], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2083 ⟨![[0], [], [2, 1], [1], [0, 4], [], [1, 2, 5], [1]], ![[0], [3], [2, 3], [2, 6], [0, 0, 0, 4], [0, 2, 6, 4], [0, 2, 6, 4], [0, 2, 6, 4], [0, 2, 6, 4], [0, 2, 6, 4]]⟩, .edge 2090 ⟨![[], [1, 0, 3], [2, 0, 3], [0, 3], [2, 2, 4], [0, 1], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [2, 6], [1, 1, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 209) : Classified H :=
  classify_of_checks 209 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node209

namespace Node210

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [4], [5]],
   ![[0], [1], [0, 0, 1, 2, 1, 2], [0, 0], [2], [3], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 209) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 210 :=
  generated_of_packed 209 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 2093 ⟨![[], [0], [1], [2], [4], [0, 3], [1, 5], [2, 5]], ![[1], [2], [3], [1, 1, 1, 5], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .core, .edge 2095 ⟨![[], [0, 3, 4], [1], [2], [4], [0], [1, 5], [2, 5]], ![[5], [2], [3], [1, 1, 1, 4, 5], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .edge 2091 ⟨![[0], [1], [], [2], [0, 5], [1, 5], [], [2]], ![[0], [1], [3], [0, 0, 1, 5], [0, 0], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2094 ⟨![[], [1], [0, 0, 0, 2], [0, 0, 0], [4], [1, 3], [0, 2], [0]], ![[7], [1], [2, 7], [1, 1, 1, 5], [4], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2092 ⟨![[0], [], [1, 1, 1, 2], [1, 1, 1], [0, 3], [1, 1, 5], [1, 2], [1]], ![[0], [7], [2, 7], [0, 0, 0, 4], [0, 0], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2096 ⟨![[], [0, 0, 1, 0], [0, 0, 0, 2], [0, 0, 0], [4], [0, 1, 5], [0, 2], [0]], ![[7], [1, 7], [2, 7], [1, 2, 2, 5], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 210) : Classified H :=
  classify_of_checks 210 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node210

namespace Node211

def gen : Fin 3 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 3 10 :=
  ⟨![[0], [1], [2]],
   ![[0], [1], [2], [0, 0], [0, 0, 0, 1, 0, 1, 1, 2, 1], [1, 0, 1, 0], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 210) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 211 :=
  generated_of_packed 210 gen generationWords generation_checked

def pivot (σ : Fin 3 → Bool) : Fin 3 :=
  ![0, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 3 → Bool) : BranchData 3 :=
  ![.core, .edge 2097 ⟨![[], [0], [1, 2, 5], [3], [0, 2, 5], [1, 2, 5]], ![[1], [1, 1, 1, 4, 2], [1, 1, 1, 2, 4, 2], [3], [1, 3, 4], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2]]⟩, .core, .edge 2098 ⟨![[], [0, 2, 3], [1, 2, 5], [3], [0], [1, 2, 5]], ![[4], [1, 1, 1, 2, 4, 3], [1, 1, 1, 4, 3], [3], [1, 1], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2]]⟩, .noncentric 480, .noncentric 480, .noncentric 480, .noncentric 480] ⟨signatureIndex σ % 8, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 3 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 211) : Classified H :=
  classify_of_checks 211 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node211

namespace Node212

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [1, 2, 3, 1, 2, 3], [0, 2, 3, 0, 2, 3], [0, 2, 3, 0, 2, 3], [0, 2, 3, 0, 2, 3], [0, 2, 3, 0, 2, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 211) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 212 :=
  generated_of_packed 211 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 2056, .edge 2102 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1], [2, 3]], ![[5], [2], [3], [3, 3], [2, 3, 2, 7], [2, 3, 2, 4, 7], [2, 3, 2, 4, 7], [2, 3, 2, 4, 7], [2, 3, 2, 4, 7], [2, 3, 2, 4, 7]]⟩, .edge 2100 ⟨![[0], [1], [], [2], [0], [1], [], [2, 4]], ![[0], [1], [3], [3, 3], [1, 3, 1, 7], [0, 3, 0, 7], [0, 3, 0, 7], [0, 3, 0, 7], [0, 3, 0, 7], [0, 3, 0, 7]]⟩, .noncentric 2056, .noncentric 2056, .edge 2104 ⟨![[], [0, 0, 0, 1], [0, 0, 0], [2], [0, 0], [0, 1], [0], [2, 3]], ![[6], [1, 6], [3], [3, 3], [2, 3, 6, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩, .edge 2099 ⟨![[0], [1], [2], [], [0, 3], [1, 3], [2, 4], [3]], ![[0], [1], [2], [7], [2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .noncentric 2056, .noncentric 2056, .edge 2103 ⟨![[], [0, 0, 0, 1], [2], [0, 0, 0, 3], [0, 0], [0, 1], [2], [0]], ![[7], [1, 7], [2], [3, 7], [2, 3, 2, 3, 4], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩, .edge 2101 ⟨![[0], [1], [], [2, 4], [0], [1], [], [2]], ![[0], [1], [7], [3, 7], [1, 3, 1, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .noncentric 2056, .noncentric 2056, .edge 2105 ⟨![[], [0, 0, 0, 1], [0, 0, 2, 0], [0, 0, 0, 3], [0, 0], [0, 1], [2, 0], [0]], ![[7], [1, 7], [2, 7], [3, 7], [2, 3, 6, 7], [2, 3, 2, 7], [2, 3, 2, 7], [2, 3, 2, 7], [2, 3, 2, 7], [2, 3, 2, 7]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 212) : Classified H :=
  classify_of_checks 212 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node212

namespace Node213

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 212) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 213 :=
  generated_of_packed 212 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 2048, .noncentric 2048, .edge 2107 ⟨![[0], [1], [], [2], [0], [1], [], [0, 0, 2]], ![[0], [1], [3], [3, 3], [0, 3, 0, 3], [0, 3, 0, 7], [0, 3, 0, 7], [0, 3, 0, 7], [0, 3, 0, 7], [0, 3, 0, 7]]⟩, .edge 2110 ⟨![[], [1], [0, 0, 0], [2], [0, 0], [1], [0], [0, 2, 0]], ![[6], [1], [3], [3, 3], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 2048, .noncentric 2048, .edge 2106 ⟨![[0], [1], [2], [], [0, 3, 5], [1], [0, 0, 2], [3]], ![[0], [1], [2], [7], [0, 4, 7], [0, 0, 0, 4, 7], [0, 0, 0, 4, 7], [0, 0, 0, 4, 7], [0, 0, 0, 4, 7], [0, 0, 0, 4, 7]]⟩, .edge 2109 ⟨![[], [1], [2], [0, 3, 4], [4, 5], [1], [2], [0]], ![[7], [1], [2], [3, 7], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .noncentric 2048, .noncentric 2048, .edge 2108 ⟨![[0], [1], [], [0, 0, 2], [0], [1], [], [2]], ![[0], [1], [7], [3, 7], [0, 3, 0, 7], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 2111 ⟨![[], [1], [0, 2, 3], [0, 3, 4], [4, 5], [1], [2, 0, 5], [0]], ![[7], [1], [2, 7], [3, 7], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .noncentric 2048, .noncentric 2048] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 213) : Classified H :=
  classify_of_checks 213 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node213

namespace Node214

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 3, 1, 3], [0, 3, 0, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 213) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 214 :=
  generated_of_packed 213 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2113 ⟨![[0], [], [1], [2], [0], [], [1], [2, 3]], ![[0], [2], [3], [3, 7], [0, 3, 0, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩, .noncentric 24, .noncentric 24, .edge 2115 ⟨![[], [1], [0, 0, 0], [2], [0, 0], [1], [0], [2, 5]], ![[6], [1], [3], [1, 3, 1, 3], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 24, .edge 2117 ⟨![[], [0, 0, 0, 1], [0, 0, 0], [2], [0, 0], [0, 1], [0], [2, 5]], ![[6], [1, 6], [3], [1, 3, 5, 7], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2112 ⟨![[0], [1], [2], [], [0, 5], [1, 3], [2, 5], []], ![[0], [1], [2], [1, 5], [0, 4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 24, .edge 2114 ⟨![[0], [], [2], [1, 3], [0], [], [2], [1]], ![[0], [7], [2], [3, 3], [0, 3, 0, 7], [2, 3, 2, 7], [2, 3, 2, 7], [2, 3, 2, 7], [2, 3, 2, 7], [2, 3, 2, 7]]⟩, .noncentric 24, .noncentric 24, .edge 2116 ⟨![[], [1], [0, 2, 4], [0, 4], [4, 5], [1], [0, 2, 5], [0]], ![[7], [1], [2, 7], [1, 3, 1, 7], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .noncentric 24, .edge 2118 ⟨![[], [1, 0, 4], [0, 2, 4], [0, 4], [4, 5], [0, 1, 3], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [1, 3, 1, 3], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 214) : Classified H :=
  classify_of_checks 214 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node214

namespace Node215

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 214) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 215 :=
  generated_of_packed 214 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2121 ⟨![[0], [], [1], [2], [0], [], [1], [2, 3]], ![[0], [2], [3], [3, 3], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2128 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 3, 5], [2, 3]], ![[5], [2], [3], [3, 3], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2120 ⟨![[0], [1], [], [2], [0, 3, 5], [1], [0, 0, 3], [2, 4]], ![[0], [1], [3], [3, 3], [0, 3, 3, 4], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 2126 ⟨![[], [1], [0, 3, 4], [2], [4, 5], [1], [0], [2, 3]], ![[6], [1], [3], [3, 3], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2123 ⟨![[0], [], [1], [2], [0], [], [1], [2, 3]], ![[0], [2], [3], [3, 3], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2130 ⟨![[], [0, 1, 3], [0, 3, 4], [2], [4, 5], [1, 0, 4], [0], [2, 3]], ![[6], [1, 6], [3], [3, 3], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2119 ⟨![[0], [1], [2], [], [0, 3], [1, 3], [2, 4], [3]], ![[0], [1], [2], [7], [0, 2, 6, 4], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7]]⟩, .edge 2125 ⟨![[], [1], [2], [0, 2, 2], [0, 0], [1], [2, 3, 5], [0]], ![[7], [1], [2], [3, 7], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2122 ⟨![[0], [], [2], [1, 3], [0], [], [2], [1]], ![[0], [7], [2], [3, 7], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2129 ⟨![[], [0, 0, 0, 1], [2], [0, 2, 2], [0, 0], [0, 1], [2, 3, 5], [0]], ![[7], [1, 7], [2], [3, 7], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .noncentric 24, .edge 2127 ⟨![[], [1], [0, 2], [0, 0, 0, 3], [0, 0], [1], [0, 2, 3, 4], [0]], ![[7], [1], [2, 7], [3, 7], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2124 ⟨![[0], [], [2, 1], [1, 3], [0], [], [2, 1], [1]], ![[0], [7], [2, 7], [3, 7], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2131 ⟨![[], [0, 0, 0, 1], [0, 2], [0, 0, 0, 3], [0, 0], [0, 1], [0, 1, 2, 1], [0]], ![[7], [1, 7], [2, 7], [3, 7], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 215) : Classified H :=
  classify_of_checks 215 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node215

namespace Node216

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 3, 0, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 215) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 216 :=
  generated_of_packed 215 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2134 ⟨![[0], [], [1], [2], [0], [], [1, 3], [2]], ![[0], [2], [3], [3, 3], [2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 2141 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 3], [1, 2, 1]], ![[5], [2], [3], [3, 3], [2, 6], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2133 ⟨![[0], [1], [], [2], [0, 3], [1, 3], [3, 4], [0, 0, 2]], ![[0], [1], [3], [1, 5], [1, 5, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 2139 ⟨![[], [1], [0, 3, 4, 5], [2], [4, 5], [1], [0], [2, 3, 5]], ![[6], [1], [3], [3, 3], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2136 ⟨![[0], [], [1, 3], [2], [0], [], [1], [2]], ![[0], [6], [3], [3, 3], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 2143 ⟨![[], [0, 1, 5], [0, 3, 4, 5], [2], [4, 5], [0, 1, 4], [0], [2, 3, 5]], ![[6], [1, 6], [3], [3, 3], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2132 ⟨![[0], [1], [2], [], [0, 3, 5], [1], [0, 0, 2], [3]], ![[0], [1], [2], [7], [0, 4, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7]]⟩, .edge 2138 ⟨![[], [1], [2], [0, 2, 2], [4, 5], [1], [2, 3], [0]], ![[7], [1], [2], [3, 7], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2135 ⟨![[0], [], [2], [1], [0], [], [2, 3], [1]], ![[0], [3], [2], [3, 3], [2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 2142 ⟨![[], [1, 0, 4], [2], [0, 2, 2], [4, 5], [0, 1, 3], [2, 3], [0]], ![[7], [1, 7], [2], [3, 7], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .noncentric 24, .edge 2140 ⟨![[], [1], [0, 2], [0, 3, 4], [4, 5], [1], [2, 0, 3, 5], [0]], ![[7], [1], [2, 7], [3, 7], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2137 ⟨![[0], [], [2, 1, 3], [1], [0], [], [2, 1], [1]], ![[0], [3], [2, 3], [3, 3], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 2144 ⟨![[], [1, 0, 4], [0, 2], [0, 3, 4], [4, 5], [0, 1, 3], [2, 0, 3, 5], [0]], ![[7], [1, 7], [2, 7], [3, 7], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 216) : Classified H :=
  classify_of_checks 216 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node216

namespace Node217

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 1], [0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 216) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 217 :=
  generated_of_packed 216 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 2056, .edge 2153 ⟨![[], [0, 3, 4], [1], [2], [4, 5], [0], [1], [2, 3]], ![[5], [2], [3], [1, 5], [1, 1], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 2145 ⟨![[0], [1], [], [2], [0], [0, 0, 1], [], [2, 4]], ![[0], [1], [3], [1, 1], [0, 1, 0, 1], [0, 1, 0, 5], [0, 1, 0, 5], [0, 1, 0, 5], [0, 1, 0, 5], [0, 1, 0, 5]]⟩, .edge 2151 ⟨![[], [1], [0, 0, 0], [2], [0, 0], [0, 1, 0], [0], [2, 3]], ![[6], [1], [3], [1, 1], [1, 4, 5], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2148 ⟨![[0], [], [1, 1, 1], [2], [0, 3, 5], [3], [1], [2, 3]], ![[0], [6], [3], [5], [0, 4, 5], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2155 ⟨![[], [0, 0, 1, 0], [0, 0, 0], [2], [0, 0], [0, 0, 0, 1], [0], [2, 3]], ![[6], [1, 6], [3], [1, 5], [1, 1], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .noncentric 2048, .edge 2150 ⟨![[], [1], [2], [0, 0, 0, 3], [0, 0], [1, 3, 5], [2], [0]], ![[7], [1], [2], [1, 1], [1, 4, 5], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2147 ⟨![[0], [], [2], [1], [0, 3, 5], [3], [0, 0, 2], [1]], ![[0], [3], [2], [5], [0, 4, 5], [0, 0, 0, 4, 5], [0, 0, 0, 4, 5], [0, 0, 0, 4, 5], [0, 0, 0, 4, 5], [0, 0, 0, 4, 5]]⟩, .edge 2154 ⟨![[], [0, 0, 1, 0], [2], [0, 0, 0, 3], [0, 0], [0, 1], [2], [0]], ![[7], [1, 7], [2], [1, 5], [1, 1], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 2146 ⟨![[0], [1], [], [2, 4], [0], [0, 0, 1], [], [2]], ![[0], [1], [7], [1, 1], [0, 1, 0, 1], [0, 1, 0, 5], [0, 1, 0, 5], [0, 1, 0, 5], [0, 1, 0, 5], [0, 1, 0, 5]]⟩, .edge 2152 ⟨![[], [1], [0, 0, 2, 0], [0, 0, 0, 3], [0, 0], [1, 3, 5], [2, 0], [0]], ![[7], [1], [2, 7], [1, 1], [1, 4, 5], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2149 ⟨![[0], [], [1, 2, 5], [1], [0, 3, 5], [3], [0, 0, 2, 1], [1]], ![[0], [3], [2, 3], [5], [0, 4, 5], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2156 ⟨![[], [0, 0, 1, 0], [0, 0, 2, 0], [0, 0, 0, 3], [0, 0], [0, 1], [2, 0], [0]], ![[7], [1, 7], [2, 7], [1, 5], [1, 1], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 217) : Classified H :=
  classify_of_checks 217 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node217

namespace Node218

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 217) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 218 :=
  generated_of_packed 217 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 2048, .edge 2165 ⟨![[], [0, 0, 0], [1], [2], [4, 5], [0], [1], [2, 3, 5]], ![[5], [2], [3], [3, 3], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2157 ⟨![[0], [1], [], [2], [0], [1, 4], [], [0, 0, 2]], ![[0], [1], [3], [3, 3], [1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5]]⟩, .edge 2163 ⟨![[], [1], [0, 0, 0], [2], [0, 0], [1, 3], [0], [0, 2, 0]], ![[6], [1], [3], [1, 5], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2160 ⟨![[0], [], [1, 4], [2], [0, 3], [], [1], [2]], ![[0], [6], [3], [3, 3], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 2167 ⟨![[], [0, 0, 1, 0], [0, 0, 0], [2], [0, 0], [0, 1, 4], [0], [0, 2, 0]], ![[6], [1, 6], [3], [3, 3], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 2056, .edge 2162 ⟨![[], [1], [2], [0, 3, 4], [4, 5], [1, 3], [2], [0]], ![[7], [1], [2], [1, 5], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 2159 ⟨![[0], [], [2], [1], [0, 3], [], [2, 4], [1]], ![[0], [3], [2], [3, 3], [2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 2166 ⟨![[], [1, 0, 4], [2], [0, 3, 4], [4, 5], [0, 1, 3], [2], [0]], ![[7], [1, 7], [2], [3, 7], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 2158 ⟨![[0], [1], [], [0, 0, 2], [0], [1, 4], [], [2]], ![[0], [1], [7], [3, 7], [1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5]]⟩, .edge 2164 ⟨![[], [1], [0, 2, 3], [0, 3, 4], [4, 5], [1, 3], [2, 0, 5], [0]], ![[7], [1], [2, 7], [1, 5], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 2161 ⟨![[0], [], [2, 1, 3], [1], [0, 3], [], [0, 1, 2, 0], [1]], ![[0], [3], [2, 3], [3, 3], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 2168 ⟨![[], [1, 0, 4], [0, 2, 3], [0, 3, 4], [4, 5], [0, 1, 3], [2, 0, 5], [0]], ![[7], [1, 7], [2, 7], [3, 7], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 218) : Classified H :=
  classify_of_checks 218 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node218

namespace Node219

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 1], [0, 1, 0, 1], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 218) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 219 :=
  generated_of_packed 218 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2170 ⟨![[0], [], [1], [2], [0, 3, 5], [3], [0, 0, 1], [2, 3]], ![[0], [2], [3], [5], [0, 4, 5], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩, .edge 2176 ⟨![[], [0, 3, 4], [1], [2], [4, 5], [0], [1], [2, 5]], ![[5], [2], [3], [1, 5], [1, 1], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 56, .edge 2174 ⟨![[], [1], [0, 0, 0], [2], [0, 0], [0, 1, 0], [0], [2, 5]], ![[6], [1], [3], [1, 1], [1, 4, 5], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2171 ⟨![[0], [], [1, 1, 1], [2], [0, 3, 5], [3], [1], [2, 3]], ![[0], [6], [3], [5], [0, 4, 5], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2177 ⟨![[], [0, 0, 1, 0], [0, 0, 0], [2], [0, 0], [0, 0, 0, 1], [0], [2, 5]], ![[6], [1, 6], [3], [1, 5], [1, 1], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 2048, .edge 2173 ⟨![[], [1], [2], [0, 4], [4, 5], [1, 3, 5], [2], [0]], ![[7], [1], [2], [1, 1], [3, 3], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .noncentric 2056, .noncentric 80, .edge 2169 ⟨![[0], [1], [], [2, 5], [0], [0, 0, 1], [], [2]], ![[0], [1], [7], [1, 1], [0, 0, 3, 3], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2175 ⟨![[], [1], [0, 2, 4], [0, 4], [4, 5], [1, 3, 5], [0, 2, 5], [0]], ![[7], [1], [2, 7], [1, 1], [3, 3], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2172 ⟨![[0], [], [2, 1], [1], [0, 3, 5], [3], [1, 2, 5], [1]], ![[0], [3], [2, 3], [5], [0, 4, 5], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2178 ⟨![[], [0, 1, 4], [0, 2, 4], [0, 4], [4, 5], [0, 1, 3], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [1, 5], [1, 1], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 219) : Classified H :=
  classify_of_checks 219 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node219

namespace Node220

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 1], [0, 1, 0, 1], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 219) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 220 :=
  generated_of_packed 219 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2181 ⟨![[0], [], [1], [2], [0, 3, 5], [3], [0, 0, 1], [2, 3]], ![[0], [2], [3], [5], [0, 4, 5], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2186 ⟨![[], [0, 3, 4], [1], [2], [4, 5], [0], [1, 3, 5], [2, 3]], ![[5], [2], [3], [1, 5], [1, 1], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 2179 ⟨![[0], [1], [], [2], [0, 3, 5], [0, 0, 1], [0, 0, 3], [2, 4]], ![[0], [1], [3], [1, 1], [0, 1, 0, 1], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 2184 ⟨![[], [1], [0, 3, 4], [2], [4, 5], [1, 3, 5], [0], [2, 3]], ![[6], [1], [3], [1, 1], [1, 4, 5], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .noncentric 2056, .edge 2188 ⟨![[], [0, 1, 4], [0, 3, 4], [2], [4, 5], [0, 1, 3], [0], [2, 3]], ![[6], [1, 6], [3], [1, 5], [1, 1], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .noncentric 2048, .edge 2183 ⟨![[], [1], [2], [0, 2, 2], [0, 0], [1, 3, 5], [2, 3, 5], [0]], ![[7], [1], [2], [1, 1], [2, 6], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2182 ⟨![[0], [], [2], [1], [0, 3, 5], [3], [0, 0, 2], [1]], ![[0], [3], [2], [5], [0, 4, 5], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2187 ⟨![[], [0, 0, 1, 0], [2], [0, 2, 2], [0, 0], [0, 1], [1, 2, 1], [0]], ![[7], [1, 7], [2], [1, 5], [1, 1], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 2180 ⟨![[0], [1], [], [2, 3, 5], [0, 3, 5], [0, 0, 1], [0, 0, 3], [2]], ![[0], [1], [7], [1, 1], [0, 0, 3, 3], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2185 ⟨![[], [1], [0, 2], [0, 0, 0, 3], [0, 0], [1, 3, 5], [0, 2, 3, 4], [0]], ![[7], [1], [2, 7], [1, 1], [1, 4, 5], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .noncentric 24, .edge 2189 ⟨![[], [0, 0, 1, 0], [0, 2], [0, 0, 0, 3], [0, 0], [0, 1], [0, 2, 3, 4], [0]], ![[7], [1, 7], [2, 7], [1, 5], [1, 1], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 220) : Classified H :=
  classify_of_checks 220 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node220

namespace Node221

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 3, 0, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 220) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 221 :=
  generated_of_packed 220 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2192 ⟨![[0], [], [1], [2], [0, 3], [], [1, 1, 1], [2]], ![[0], [2], [3], [3, 3], [0, 3, 0, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2197 ⟨![[], [0, 0, 0], [1], [2], [4, 5], [0], [1, 3], [1, 2, 1]], ![[5], [2], [3], [3, 3], [2, 6], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2190 ⟨![[0], [1], [], [2], [0, 3], [1, 3, 4], [3, 4], [0, 0, 2]], ![[0], [1], [3], [3, 3], [3, 3, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6], [0, 4, 6]]⟩, .edge 2195 ⟨![[], [1], [0, 3, 4, 5], [2], [4, 5], [1, 3], [0], [2, 3, 5]], ![[6], [1], [3], [1, 5], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .noncentric 2048, .edge 2199 ⟨![[], [1, 0, 5], [0, 3, 4, 5], [2], [4, 5], [0, 1], [0], [2, 3, 5]], ![[6], [1, 6], [3], [3, 3], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .noncentric 2056, .edge 2194 ⟨![[], [1], [2], [0, 2, 2], [4, 5], [1, 3], [2, 3], [0]], ![[7], [1], [2], [1, 5], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2193 ⟨![[0], [], [2], [1], [0, 3], [], [2, 2, 2], [1]], ![[0], [3], [2], [3, 3], [0, 3, 4, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2198 ⟨![[], [1, 0, 4], [2], [0, 2, 2], [4, 5], [0, 1, 3], [2, 3], [0]], ![[7], [1, 7], [2], [3, 7], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2191 ⟨![[0], [1], [], [2, 3, 5], [0, 3], [1, 3, 4], [3, 4], [2]], ![[0], [1], [7], [3, 7], [3, 6, 7], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2196 ⟨![[], [1], [0, 2], [0, 3, 4], [4, 5], [1, 3], [2, 0, 3, 5], [0]], ![[7], [1], [2, 7], [1, 5], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .noncentric 24, .edge 2200 ⟨![[], [1, 0, 4], [0, 2], [0, 3, 4], [4, 5], [0, 1, 3], [2, 0, 3, 5], [0]], ![[7], [1, 7], [2, 7], [3, 7], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 221) : Classified H :=
  classify_of_checks 221 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node221

namespace Node222

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 221) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 222 :=
  generated_of_packed 221 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2204 ⟨![[0], [], [1], [2], [0], [], [1], [2, 3]], ![[0], [2], [3], [3, 3], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2210 ⟨![[], [0, 4], [1], [2], [4], [0], [1, 4, 5], [2, 3]], ![[5], [2], [3], [3, 3], [4], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2202 ⟨![[0], [1], [], [2], [0, 4, 5], [1], [], [2, 4]], ![[0], [1], [3], [3, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2208 ⟨![[], [1], [0, 5], [2], [4], [1], [0], [2, 3]], ![[6], [1], [3], [3, 3], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2206 ⟨![[0], [], [1], [2], [0], [], [1], [2, 3]], ![[0], [2], [3], [3, 3], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2211 ⟨![[], [0, 1, 4], [0, 5], [2], [4], [0, 1], [0], [2, 3]], ![[6], [1, 6], [3], [3, 3], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2201 ⟨![[0], [1], [2], [], [0, 3], [1, 3], [2, 4], [3]], ![[0], [1], [2], [7], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .noncentric 24, .edge 2205 ⟨![[0], [], [2], [1, 3], [0], [], [2], [1]], ![[0], [7], [2], [3, 7], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .noncentric 80, .edge 2203 ⟨![[0], [1], [], [2, 4], [0, 4, 5], [1], [], [2]], ![[0], [1], [7], [3, 7], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2209 ⟨![[], [1], [2, 0, 4], [0, 2, 2], [4], [1], [0, 2, 2, 2], [0]], ![[7], [1], [2, 7], [3, 7], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2207 ⟨![[0], [], [2, 1], [1, 3], [0], [], [2, 1], [1]], ![[0], [7], [2, 7], [3, 7], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .noncentric 2372] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 222) : Classified H :=
  classify_of_checks 222 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node222

namespace Node223

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 3, 0, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 222) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 223 :=
  generated_of_packed 222 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2214 ⟨![[0], [], [1], [2], [0, 3], [], [1], [2]], ![[0], [2], [3], [3, 3], [0, 3, 0, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2220 ⟨![[], [0, 0, 0], [1], [2], [4, 5], [0], [1, 4], [2, 3, 5]], ![[5], [2], [3], [3, 3], [2, 6], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2212 ⟨![[0], [1], [], [2], [0, 4], [1], [], [0, 0, 2]], ![[0], [1], [3], [3, 3], [0, 0, 0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2218 ⟨![[], [1], [0, 5], [2], [4, 5], [1, 3], [0], [2, 3, 5]], ![[6], [1], [3], [1, 5], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2216 ⟨![[0], [], [1], [2], [0, 3], [], [1], [2]], ![[0], [2], [3], [3, 3], [0, 3, 0, 3], [0, 2, 4, 2], [0, 2, 4, 2], [0, 2, 4, 2], [0, 2, 4, 2], [0, 2, 4, 2]]⟩, .edge 2222 ⟨![[], [1, 0, 5], [0, 5], [2], [4, 5], [0, 1], [0], [2, 3, 5]], ![[6], [1, 6], [3], [3, 3], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .noncentric 2056, .noncentric 24, .edge 2215 ⟨![[0], [], [2], [1], [0, 3], [], [2], [1]], ![[0], [3], [2], [3, 3], [0, 3, 4, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2221 ⟨![[], [1, 0, 4], [2], [0, 3, 4], [4, 5], [0, 1, 3], [2, 4], [0]], ![[7], [1, 7], [2], [3, 7], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2213 ⟨![[0], [1], [], [0, 0, 2], [0, 4], [1], [], [2]], ![[0], [1], [7], [3, 7], [0, 0, 0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2219 ⟨![[], [1], [2, 0, 4], [0, 3, 4], [4, 5], [1, 3], [0, 2, 2, 2], [0]], ![[7], [1], [2, 7], [1, 5], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2217 ⟨![[0], [], [2, 1, 3], [1], [0, 3], [], [2, 1, 3], [1]], ![[0], [3], [2, 3], [3, 3], [0, 3, 4, 3], [0, 2, 4, 2], [0, 2, 4, 2], [0, 2, 4, 2], [0, 2, 4, 2], [0, 2, 4, 2]]⟩, .edge 2223 ⟨![[], [1, 0, 4], [2, 0, 4], [0, 3, 4], [4, 5], [0, 1, 3], [0, 1, 2, 1], [0]], ![[7], [1, 7], [2, 7], [3, 7], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 223) : Classified H :=
  classify_of_checks 223 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node223

namespace Node224

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 3, 1, 3], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 223) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 224 :=
  generated_of_packed 223 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 64, .edge 2232 ⟨![[], [0, 4], [1], [2], [4], [0], [1, 4, 5], [2, 5]], ![[5], [2], [3], [1, 3, 5, 7], [4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2225 ⟨![[0], [1], [], [2], [0, 4, 5], [1], [], [2, 5]], ![[0], [1], [3], [1, 3, 1, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2230 ⟨![[], [1], [0, 5], [2], [4], [1], [0], [2, 5]], ![[6], [1], [3], [1, 3, 1, 3], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2228 ⟨![[0], [], [1], [2], [0], [], [1], [2, 3]], ![[0], [2], [3], [3, 7], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .noncentric 68, .edge 2224 ⟨![[0], [1], [2], [], [0, 5], [1, 3], [2, 5], []], ![[0], [1], [2], [1, 5], [0, 0], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 2056, .edge 2227 ⟨![[0], [], [2], [1, 3], [0], [], [2], [1]], ![[0], [7], [2], [3, 3], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2233 ⟨![[], [0, 0, 1, 0], [2], [0, 0, 0], [4], [0, 1, 3], [0, 0, 2], [0]], ![[7], [1, 7], [2], [1, 3, 1, 3], [4], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2226 ⟨![[0], [1], [], [2, 5], [0, 4, 5], [1], [], [2]], ![[0], [1], [7], [1, 3, 1, 7], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2231 ⟨![[], [1], [0, 2], [0, 0, 0], [4], [1], [0, 2, 5], [0]], ![[7], [1], [2, 7], [1, 3, 1, 7], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2229 ⟨![[0], [], [1, 2, 5], [1, 3], [0], [], [1, 2, 5], [1]], ![[0], [7], [2, 7], [3, 3], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2234 ⟨![[], [0, 0, 1, 0], [0, 2], [0, 0, 0], [4], [0, 1, 3], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [1, 3, 1, 3], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 224) : Classified H :=
  classify_of_checks 224 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node224

end ReeTwo.SylowModel.SmallEvenMaximalLower
