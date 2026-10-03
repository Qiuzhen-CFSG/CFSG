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

namespace Node150

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 2, 0, 2], [3, 3], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 149) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 150 :=
  generated_of_packed 149 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1579 ⟨![[0], [], [1], [2], [0], [], [0, 0, 1], [2]], ![[0], [2], [3], [0, 2, 0, 2], [3, 3], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1586 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 5], [2, 4, 5]], ![[5], [2], [3], [2, 4, 6], [3, 3], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1578 ⟨![[0], [1], [], [2], [0, 5], [0, 0, 1], [], [2, 5]], ![[0], [1], [3], [0, 4], [3, 3], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1584 ⟨![[], [1], [0, 3], [2], [3, 5], [1], [0], [2, 4, 5]], ![[6], [1], [3], [2, 2], [3, 3], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1581 ⟨![[0], [], [0, 0, 1], [2], [0], [], [1], [2]], ![[0], [6], [3], [0, 2, 0, 6], [3, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1588 ⟨![[], [0, 1], [0, 3], [2], [1, 1], [1, 0, 5], [0], [2, 4, 5]], ![[6], [1, 6], [3], [2, 2], [3, 3], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 16, .edge 1583 ⟨![[], [1], [2], [0, 3, 4], [3, 5], [1], [2, 5], [0]], ![[7], [1], [2], [3, 3], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1580 ⟨![[0], [], [2], [1], [0], [], [0, 0, 2], [1]], ![[0], [3], [2], [0, 2, 0, 2], [3, 3], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1587 ⟨![[], [1, 0, 3], [2], [0, 3, 4], [3, 5], [0, 1, 4], [2, 5], [0]], ![[7], [1, 7], [2], [3, 3], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 2064, .edge 1585 ⟨![[], [1], [2, 0, 3], [0, 3, 4], [3, 5], [1], [2, 0], [0]], ![[7], [1], [2, 7], [2, 2], [3, 7], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 1582 ⟨![[0], [], [2, 1, 4], [1], [0], [], [0, 2, 0, 1], [1]], ![[0], [3], [2, 3], [0, 2, 0, 6], [3, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1589 ⟨![[], [1, 0, 3], [2, 0, 3], [0, 3, 4], [3, 5], [0, 1, 4], [2, 0], [0]], ![[7], [1, 7], [2, 7], [2, 2], [3, 7], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 150) : Classified H :=
  classify_of_checks 150 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node150

namespace Node151

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 2, 0, 2], [1, 3, 1, 3], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 150) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 151 :=
  generated_of_packed 150 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1591 ⟨![[0], [], [1], [2], [0], [], [0, 0, 1], [2, 4]], ![[0], [2], [3], [0, 2, 0, 2], [3, 7], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .noncentric 100, .noncentric 24, .edge 1596 ⟨![[], [1], [0, 3], [2], [3, 5], [1], [0], [2, 5]], ![[6], [1], [3], [2, 2], [1, 3, 1, 3], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1593 ⟨![[0], [], [0, 0, 1], [2], [0], [], [1], [2, 4]], ![[0], [6], [3], [0, 2, 0, 6], [3, 7], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1599 ⟨![[], [0, 1], [0, 3], [2], [1, 1], [1, 0, 5], [0], [2, 5]], ![[6], [1, 6], [3], [2, 2], [1, 3, 5, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 16, .edge 1595 ⟨![[], [1], [2], [0, 3], [3, 5], [1], [2, 5], [0]], ![[7], [1], [2], [3, 3], [1, 3, 1, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1592 ⟨![[0], [], [2], [1, 4], [0], [], [0, 0, 2], [1]], ![[0], [7], [2], [0, 2, 0, 2], [3, 3], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1598 ⟨![[], [1, 0, 3], [2], [0, 3], [3, 5], [0, 1, 4], [2, 5], [0]], ![[7], [1, 7], [2], [3, 3], [1, 3, 1, 3], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1590 ⟨![[0], [1], [], [2], [0, 5], [0, 0, 1], [], [2]], ![[0], [1], [3], [0, 4], [1, 3, 5, 3], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1597 ⟨![[], [1], [0, 2, 3], [0, 3], [3, 5], [1], [0, 2], [0]], ![[7], [1], [2, 7], [2, 2], [1, 3, 1, 7], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 1594 ⟨![[0], [], [2, 1, 4], [1, 4], [0], [], [1, 2], [1]], ![[0], [7], [2, 7], [0, 2, 0, 6], [3, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1600 ⟨![[], [1, 0, 3], [0, 2, 3], [0, 3], [3, 5], [0, 1, 4], [0, 2], [0]], ![[7], [1, 7], [2, 7], [2, 2], [1, 3, 1, 3], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 151) : Classified H :=
  classify_of_checks 151 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node151

namespace Node152

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 2, 0, 2], [3, 3], [2, 2, 3, 3], [2, 2, 3, 3], [2, 2, 3, 3], [2, 2, 3, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 151) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 152 :=
  generated_of_packed 151 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1603 ⟨![[0], [], [1], [2], [0], [], [0, 0, 1], [2, 4]], ![[0], [2], [3], [0, 2, 0, 2], [3, 3], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1610 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 4], [2, 4]], ![[5], [2], [3], [2, 4, 6], [3, 3], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1601 ⟨![[0], [1], [], [2], [0, 4], [0, 0, 1], [4, 5], [2, 5]], ![[0], [1], [3], [0, 4, 6], [3, 3], [3, 3, 6], [3, 3, 6], [3, 3, 6], [3, 3, 6], [3, 3, 6]]⟩, .edge 1608 ⟨![[], [1], [0, 3, 4, 5], [2], [3, 5], [1], [0], [2, 4]], ![[6], [1], [3], [2, 2], [3, 3], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 1605 ⟨![[0], [], [0, 0, 1], [2], [0], [], [1], [2, 4]], ![[0], [6], [3], [0, 2, 0, 6], [3, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1612 ⟨![[], [1, 0, 3], [0, 1, 1, 5], [2], [3, 5], [1, 0, 5], [0], [2, 4]], ![[6], [1, 6], [3], [2, 2], [3, 3], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .noncentric 2064, .edge 1607 ⟨![[], [1], [2], [0, 0, 0, 4], [0, 0], [1], [2, 4], [0]], ![[7], [1], [2], [2, 4, 6], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1604 ⟨![[0], [], [2], [1, 4], [0], [], [0, 0, 2], [1]], ![[0], [7], [2], [0, 2, 0, 2], [3, 7], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1611 ⟨![[], [0, 0, 0, 1], [2], [0, 0, 0, 4], [0, 0], [0, 1], [2, 4], [0]], ![[7], [1, 7], [2], [2, 4, 6], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1602 ⟨![[0], [1], [], [2, 4], [0, 4], [0, 0, 1], [4, 5], [2]], ![[0], [1], [7], [0, 4, 6], [3, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7]]⟩, .edge 1609 ⟨![[], [1], [0, 2, 3], [0, 0, 0, 4], [0, 0], [1], [2, 0, 4], [0]], ![[7], [1], [2, 7], [2, 2], [3, 7], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 1606 ⟨![[0], [], [2, 1], [1, 4], [0], [], [0, 0, 2, 1], [1]], ![[0], [7], [2, 7], [0, 2, 0, 6], [3, 7], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1613 ⟨![[], [0, 0, 0, 1], [0, 2, 3], [0, 0, 0, 4], [0, 0], [0, 1], [2, 0, 4], [0]], ![[7], [1, 7], [2, 7], [2, 2], [3, 7], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 152) : Classified H :=
  classify_of_checks 152 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node152

namespace Node153

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 3, 0, 3], [3, 3], [2, 2, 3, 3], [2, 2, 3, 3], [2, 2, 3, 3], [2, 2, 3, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 152) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 153 :=
  generated_of_packed 152 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1616 ⟨![[0], [], [1], [2], [0], [], [0, 0, 1, 4], [2]], ![[0], [2], [3], [2, 6], [3, 3], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 1623 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 1, 1], [1, 1, 2]], ![[5], [2], [3], [3, 4, 7], [3, 3], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1614 ⟨![[0], [1], [], [2], [0, 4, 5], [0, 0, 1, 4], [4, 5], [2, 5]], ![[0], [1], [3], [1, 5, 6], [3, 3], [3, 3, 6], [3, 3, 6], [3, 3, 6], [3, 3, 6], [3, 3, 6]]⟩, .edge 1621 ⟨![[], [1], [0, 3, 4], [2], [0, 0], [1], [0], [2, 4, 5]], ![[6], [1], [3], [3, 4, 7], [3, 3], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1618 ⟨![[0], [], [0, 0, 1, 4], [2], [0], [], [1], [2]], ![[0], [6], [3], [2, 2], [3, 3], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 1625 ⟨![[], [0, 1, 5], [0, 3, 4], [2], [0, 0], [1, 0], [0], [2, 4, 5]], ![[6], [1, 6], [3], [3, 4, 7], [3, 3], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 2072, .edge 1620 ⟨![[], [1], [2], [0, 3, 4], [3, 5], [1], [2, 2, 2], [0]], ![[7], [1], [2], [3, 3], [3, 7], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1617 ⟨![[0], [], [2], [1], [0], [], [0, 0, 2, 4], [1]], ![[0], [3], [2], [2, 6], [3, 3], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 1624 ⟨![[], [1, 0, 3], [2], [0, 3, 4], [3, 5], [0, 1, 4], [2, 2, 2], [0]], ![[7], [1, 7], [2], [3, 3], [3, 7], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1615 ⟨![[0], [1], [], [2, 4], [0, 4, 5], [2, 1, 2], [4, 5], [2]], ![[0], [1], [7], [1, 5, 6], [3, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7]]⟩, .edge 1622 ⟨![[], [1], [2, 0, 3], [0, 3, 4], [3, 5], [1], [2, 0, 4], [0]], ![[7], [1], [2, 7], [3, 3], [3, 7], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1619 ⟨![[0], [], [1, 2, 3], [1], [0], [], [0, 0, 2, 1], [1]], ![[0], [3], [2, 3], [2, 2], [3, 3], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 1626 ⟨![[], [1, 0, 3], [2, 0, 3], [0, 3, 4], [3, 5], [0, 1, 4], [2, 0, 4], [0]], ![[7], [1, 7], [2, 7], [3, 3], [3, 7], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 153) : Classified H :=
  classify_of_checks 153 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node153

namespace Node154

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 2, 0, 2], [1, 3, 1, 3], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 153) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 154 :=
  generated_of_packed 153 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1627 ⟨![[0], [], [1], [2], [0], [], [0, 0, 1], [2, 4]], ![[0], [2], [3], [0, 2, 0, 2], [3, 7], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1634 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 4], [2, 5]], ![[5], [2], [3], [2, 4, 6], [1, 3, 5, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 24, .edge 1632 ⟨![[], [1], [0, 3, 4, 5], [2], [3, 5], [1], [0], [2, 5]], ![[6], [1], [3], [2, 2], [1, 3, 1, 3], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1629 ⟨![[0], [], [0, 0, 1], [2], [0], [], [1], [2, 4]], ![[0], [6], [3], [0, 2, 0, 6], [3, 7], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1636 ⟨![[], [1, 0, 3], [0, 1, 1, 5], [2], [3, 5], [1, 0, 5], [0], [2, 5]], ![[6], [1, 6], [3], [2, 2], [1, 3, 5, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 2064, .edge 1631 ⟨![[], [1], [2], [0, 3], [3, 5], [1], [2, 4], [0]], ![[7], [1], [2], [3, 3], [1, 3, 1, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1628 ⟨![[0], [], [2], [1, 4], [0], [], [0, 0, 2], [1]], ![[0], [7], [2], [0, 2, 0, 2], [3, 3], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1635 ⟨![[], [1, 0, 3], [2], [0, 3], [3, 5], [0, 1, 4], [2, 4], [0]], ![[7], [1, 7], [2], [3, 3], [1, 3, 1, 3], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 2072, .edge 1633 ⟨![[], [1], [2, 0, 3], [0, 3], [3, 5], [1], [0, 2], [0]], ![[7], [1], [2, 7], [2, 2], [1, 3, 1, 7], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 1630 ⟨![[0], [], [2, 1, 4], [1, 4], [0], [], [1, 2], [1]], ![[0], [7], [2, 7], [0, 2, 0, 6], [3, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1637 ⟨![[], [1, 0, 3], [2, 0, 3], [0, 3], [3, 5], [0, 1, 4], [0, 2], [0]], ![[7], [1, 7], [2, 7], [2, 2], [1, 3, 1, 3], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 154) : Classified H :=
  classify_of_checks 154 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node154

namespace Node155

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 1, 0, 1], [1, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 154) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 155 :=
  generated_of_packed 154 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1641 ⟨![[0], [], [1], [2], [0, 4, 5], [4], [1, 3], [2, 4]], ![[0], [2], [3], [2, 6], [5], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 1648 ⟨![[], [0, 3, 4], [1], [2], [3, 5], [0], [1, 5], [2, 4]], ![[5], [2], [3], [1, 1], [1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1639 ⟨![[0], [1], [], [2], [0, 5], [1, 3], [], [2, 5]], ![[0], [1], [3], [0, 4], [1, 1], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1646 ⟨![[], [1], [0, 3], [2], [3, 5], [0, 1, 0], [0], [2, 4]], ![[6], [1], [3], [2, 2], [1, 1], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1643 ⟨![[0], [], [1, 1, 1], [2], [0, 4, 5], [4], [1], [2, 4]], ![[0], [6], [3], [0, 4, 5], [5], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1650 ⟨![[], [0, 1, 4], [0, 3], [2], [3, 5], [0, 1, 3], [0], [2, 4]], ![[6], [1, 6], [3], [1, 1], [1, 5], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 1638 ⟨![[0], [1], [2], [], [0, 4], [1, 4], [2, 5], [4]], ![[0], [1], [2], [0, 0, 2, 6], [7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1645 ⟨![[], [1], [2], [0, 0, 0, 4], [0, 0], [1, 4, 5], [2, 5], [0]], ![[7], [1], [2], [1, 4, 5], [1, 1], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1642 ⟨![[0], [], [2], [1], [0, 4, 5], [4], [2, 3], [1]], ![[0], [3], [2], [2, 6], [5], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 1649 ⟨![[], [0, 0, 1, 0], [2], [0, 0, 0, 4], [0, 0], [0, 1], [2, 5], [0]], ![[7], [1, 7], [2], [1, 1], [1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1640 ⟨![[0], [1], [], [2, 5], [0, 5], [1, 3], [], [2]], ![[0], [1], [7], [0, 4], [1, 1], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1647 ⟨![[], [1], [0, 0, 2, 0], [0, 0, 0, 4], [0, 0], [1, 2, 2], [2, 0, 5], [0]], ![[7], [1], [2, 7], [2, 2], [1, 1], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1644 ⟨![[0], [], [2, 1, 4], [1], [0, 2, 2], [4], [2, 1, 3], [1]], ![[0], [3], [2, 3], [0, 4, 5], [5], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1651 ⟨![[], [0, 0, 1, 0], [0, 0, 2, 0], [0, 0, 0, 4], [0, 0], [0, 1], [2, 0, 5], [0]], ![[7], [1, 7], [2, 7], [1, 1], [1, 5], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 155) : Classified H :=
  classify_of_checks 155 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node155

namespace Node156

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 2, 0, 2], [3, 3], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 155) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 156 :=
  generated_of_packed 155 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1655 ⟨![[0], [], [1], [2], [0, 4], [], [1, 3], [2]], ![[0], [2], [3], [2, 6], [3, 3], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 1662 ⟨![[], [0, 0, 0], [1], [2], [3, 5], [0], [1, 5], [2, 4, 5]], ![[5], [2], [3], [2, 4, 6], [3, 3], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1653 ⟨![[0], [1], [], [2], [0, 5], [1, 3], [], [2, 5]], ![[0], [1], [3], [0, 4], [3, 3], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1660 ⟨![[], [1], [0, 3], [2], [3, 5], [1, 4], [0], [2, 4, 5]], ![[6], [1], [3], [2, 2], [1, 5], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1657 ⟨![[0], [], [1, 3], [2], [0, 4], [], [1], [2]], ![[0], [6], [3], [2, 2], [3, 3], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 1664 ⟨![[], [1, 0, 3], [0, 3], [2], [3, 5], [0, 1, 3], [0], [2, 4, 5]], ![[6], [1, 6], [3], [2, 2], [3, 3], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1652 ⟨![[0], [1], [2], [], [0, 4, 5], [1], [2, 5], [4]], ![[0], [1], [2], [0, 4, 7], [7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1659 ⟨![[], [1], [2], [0, 3, 4], [3, 5], [1, 4], [2, 5], [0]], ![[7], [1], [2], [3, 3], [1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1656 ⟨![[0], [], [2], [1], [0, 4], [], [2, 3], [1]], ![[0], [3], [2], [2, 6], [3, 3], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 1663 ⟨![[], [1, 0, 3], [2], [0, 3, 4], [3, 5], [0, 1, 4], [2, 5], [0]], ![[7], [1, 7], [2], [3, 3], [3, 7], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1654 ⟨![[0], [1], [], [2, 5], [0, 5], [1, 3], [], [2]], ![[0], [1], [7], [0, 4], [3, 7], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1661 ⟨![[], [1], [2, 0, 3], [0, 3, 4], [3, 5], [1, 4], [2, 0], [0]], ![[7], [1], [2, 7], [2, 2], [1, 5], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 1658 ⟨![[0], [], [2, 1, 4], [1], [0, 4], [], [0, 2, 1, 0], [1]], ![[0], [3], [2, 3], [2, 2], [3, 3], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 1665 ⟨![[], [1, 0, 3], [2, 0, 3], [0, 3, 4], [3, 5], [0, 1, 4], [2, 0], [0]], ![[7], [1, 7], [2, 7], [2, 2], [3, 7], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 156) : Classified H :=
  classify_of_checks 156 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node156

namespace Node157

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 1, 0, 1], [1, 1], [1, 1, 2, 2], [1, 1, 2, 2], [1, 1, 2, 2], [1, 1, 2, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 156) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 157 :=
  generated_of_packed 156 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1669 ⟨![[0], [], [1], [2], [0, 1, 1], [4], [1, 3], [2, 4]], ![[0], [2], [3], [0, 4, 5], [5], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 1676 ⟨![[], [0, 3, 4], [1], [2], [3, 5], [0], [1, 4], [2, 4]], ![[5], [2], [3], [1, 1], [1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1667 ⟨![[0], [1], [], [2], [0, 4], [1, 3], [4, 5], [2, 5]], ![[0], [1], [3], [0, 4, 6], [1, 1], [1, 1, 6], [1, 1, 6], [1, 1, 6], [1, 1, 6], [1, 1, 6]]⟩, .edge 1674 ⟨![[], [1], [0, 3, 4, 5], [2], [3, 5], [0, 1, 0], [0], [2, 4]], ![[6], [1], [3], [2, 2], [1, 1], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1671 ⟨![[0], [], [1, 3, 4], [2], [0, 4, 5], [4], [1], [2, 4]], ![[0], [6], [3], [0, 4, 5], [5], [2, 5, 6], [2, 5, 6], [2, 5, 6], [2, 5, 6], [2, 5, 6]]⟩, .edge 1678 ⟨![[], [0, 1, 5], [0, 1, 1, 4], [2], [1, 1], [1, 0, 4], [0], [2, 4]], ![[6], [1, 6], [3], [1, 1], [1, 5], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 1666 ⟨![[0], [1], [2], [], [0, 4], [1, 4], [2, 5], [4]], ![[0], [1], [2], [0, 1, 0, 1], [7], [2, 2, 7], [2, 2, 7], [2, 2, 7], [2, 2, 7], [2, 2, 7]]⟩, .edge 1673 ⟨![[], [1], [2], [0, 0, 0, 4], [0, 0], [1, 2, 2], [2, 4], [0]], ![[7], [1], [2], [1, 4, 5], [1, 1], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1670 ⟨![[0], [], [2], [1], [0, 2, 2], [4], [2, 3], [1]], ![[0], [3], [2], [0, 4, 5], [5], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 1677 ⟨![[], [0, 0, 1, 0], [2], [0, 0, 0, 4], [0, 0], [0, 1], [2, 4], [0]], ![[7], [1, 7], [2], [1, 1], [1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1668 ⟨![[0], [1], [], [2, 4], [0, 4], [1, 3], [4, 5], [2]], ![[0], [1], [7], [0, 4, 6], [1, 1], [1, 1, 6], [1, 1, 6], [1, 1, 6], [1, 1, 6], [1, 1, 6]]⟩, .edge 1675 ⟨![[], [1], [0, 2, 3], [0, 0, 0, 4], [0, 0], [1, 4, 5], [2, 0, 4], [0]], ![[7], [1], [2, 7], [2, 2], [1, 1], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1672 ⟨![[0], [], [2, 1, 4], [1], [0, 4, 5], [4], [2, 1, 3], [1]], ![[0], [3], [2, 3], [0, 4, 5], [5], [2, 5, 6], [2, 5, 6], [2, 5, 6], [2, 5, 6], [2, 5, 6]]⟩, .edge 1679 ⟨![[], [0, 0, 1, 0], [0, 2, 3], [0, 0, 0, 4], [0, 0], [0, 1], [2, 0, 4], [0]], ![[7], [1, 7], [2, 7], [1, 1], [1, 5], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 157) : Classified H :=
  classify_of_checks 157 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node157

namespace Node158

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 3, 0, 3], [3, 3], [2, 2, 3, 3], [2, 2, 3, 3], [2, 2, 3, 3], [2, 2, 3, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 157) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 158 :=
  generated_of_packed 157 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1683 ⟨![[0], [], [1], [2], [0, 4], [], [0, 1, 0], [2]], ![[0], [2], [3], [0, 2, 2, 4], [3, 3], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6]]⟩, .edge 1690 ⟨![[], [0, 0, 0], [1], [2], [3, 5], [0], [1, 1, 1], [1, 1, 2]], ![[5], [2], [3], [3, 4, 7], [3, 3], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1681 ⟨![[0], [1], [], [2], [0, 4, 5], [1, 3, 4], [4, 5], [2, 5]], ![[0], [1], [3], [0, 1, 4, 1], [3, 3], [3, 3, 6], [3, 3, 6], [3, 3, 6], [3, 3, 6], [3, 3, 6]]⟩, .edge 1688 ⟨![[], [1], [0, 3, 4], [2], [0, 0], [1, 4], [0], [2, 4, 5]], ![[6], [1], [3], [3, 4, 7], [1, 5], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1685 ⟨![[0], [], [1, 3, 4], [2], [0, 4], [], [1], [2]], ![[0], [6], [3], [0, 2, 6, 4], [3, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1692 ⟨![[], [0, 1, 4], [0, 3, 4], [2], [0, 0], [1, 0, 4], [0], [2, 4, 5]], ![[6], [1, 6], [3], [3, 4, 7], [3, 3], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1680 ⟨![[0], [1], [2], [], [0, 2, 2], [1], [2, 5], [4]], ![[0], [1], [2], [0, 4, 7], [7], [2, 2, 7], [2, 2, 7], [2, 2, 7], [2, 2, 7], [2, 2, 7]]⟩, .edge 1687 ⟨![[], [1], [2], [0, 3, 4], [3, 5], [1, 4], [2, 2, 2], [0]], ![[7], [1], [2], [3, 3], [1, 5], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1684 ⟨![[0], [], [2], [1], [0, 4], [], [0, 2, 0], [1]], ![[0], [3], [2], [0, 2, 2, 4], [3, 3], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6]]⟩, .edge 1691 ⟨![[], [1, 0, 3], [2], [0, 3, 4], [3, 5], [0, 1, 4], [2, 2, 2], [0]], ![[7], [1, 7], [2], [3, 3], [3, 7], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1682 ⟨![[0], [1], [], [2, 4], [0, 4, 5], [1, 3, 4], [4, 5], [2]], ![[0], [1], [7], [0, 1, 4, 1], [3, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7]]⟩, .edge 1689 ⟨![[], [1], [2, 0, 3], [0, 3, 4], [3, 5], [1, 4], [2, 0, 4], [0]], ![[7], [1], [2, 7], [3, 3], [1, 5], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1686 ⟨![[0], [], [2, 1, 4], [1], [0, 4], [], [2, 1, 3], [1]], ![[0], [3], [2, 3], [0, 2, 6, 4], [3, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1693 ⟨![[], [1, 0, 3], [2, 0, 3], [0, 3, 4], [3, 5], [0, 1, 4], [2, 0, 4], [0]], ![[7], [1, 7], [2, 7], [3, 3], [3, 7], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 158) : Classified H :=
  classify_of_checks 158 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node158

namespace Node159

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0], [1, 3, 1, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 158) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 159 :=
  generated_of_packed 158 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1697 ⟨![[0], [], [1], [2], [0], [], [1, 3, 5], [2, 4]], ![[0], [2], [3], [0, 0], [3, 7], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .noncentric 68, .edge 1695 ⟨![[0], [1], [], [2], [0], [1, 3, 5], [], [2]], ![[0], [1], [3], [0, 0], [1, 3, 1, 3], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5]]⟩, .edge 1702 ⟨![[], [1], [0, 3], [2], [3], [1], [0], [2, 5]], ![[6], [1], [3], [4], [1, 3, 1, 3], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1699 ⟨![[0], [], [1, 1, 1], [2], [0], [], [1], [2, 4]], ![[0], [6], [3], [0, 0], [3, 7], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 1705 ⟨![[], [0, 1, 5], [0, 3], [2], [3], [1, 0], [0], [2, 5]], ![[6], [1, 6], [3], [4], [1, 3, 5, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1694 ⟨![[0], [1], [2], [], [0, 5], [1, 4], [2], []], ![[0], [1], [2], [0, 0], [1, 5], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1701 ⟨![[], [1], [2], [0, 0, 0], [3], [1], [2], [0]], ![[7], [1], [2], [4], [1, 3, 1, 7], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1698 ⟨![[0], [], [2], [1, 4], [0], [], [2, 3, 5], [1]], ![[0], [7], [2], [0, 0], [3, 3], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 1704 ⟨![[], [0, 0, 1, 0], [2], [0, 0, 0], [3], [0, 1, 4], [2], [0]], ![[7], [1, 7], [2], [4], [1, 3, 1, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1696 ⟨![[0], [1], [], [2], [0], [1, 3, 5], [], [2]], ![[0], [1], [3], [0, 0], [1, 3, 5, 3], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5]]⟩, .edge 1703 ⟨![[], [1], [0, 2, 3], [0, 0, 0], [3], [1], [0, 2], [0]], ![[7], [1], [2, 7], [4], [1, 3, 1, 7], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1700 ⟨![[0], [], [2, 1, 4], [1, 4], [0], [], [1, 2], [1]], ![[0], [7], [2, 7], [0, 0], [3, 3], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 1706 ⟨![[], [0, 0, 1, 0], [0, 2, 3], [0, 0, 0], [3], [0, 1, 4], [0, 2], [0]], ![[7], [1, 7], [2, 7], [4], [1, 3, 1, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 159) : Classified H :=
  classify_of_checks 159 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node159

namespace Node160

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0], [1, 3, 1, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 159) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 160 :=
  generated_of_packed 159 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1710 ⟨![[0], [], [1], [2], [0], [], [1, 3, 5], [2, 4]], ![[0], [2], [3], [0, 0], [3, 7], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1717 ⟨![[], [0, 3], [1], [2], [3], [0], [1, 1, 1], [2, 5]], ![[5], [2], [3], [4], [1, 2, 1, 6], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1708 ⟨![[0], [1], [], [2], [0, 4, 5], [1, 3, 5], [4, 5], [2]], ![[0], [1], [3], [0, 0], [0, 1, 4, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5]]⟩, .edge 1715 ⟨![[], [1], [0, 3, 4, 5], [2], [3], [1], [0], [2, 5]], ![[6], [1], [3], [4], [1, 3, 1, 3], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1712 ⟨![[0], [], [1, 3, 5], [2], [0], [], [1], [2, 4]], ![[0], [6], [3], [0, 0], [3, 7], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1719 ⟨![[], [0, 1, 4], [0, 1, 1, 5], [2], [3], [1, 0], [0], [2, 5]], ![[6], [1, 6], [3], [4], [1, 2, 5, 2], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1707 ⟨![[0], [1], [2], [], [0, 5], [1, 4], [2], []], ![[0], [1], [2], [0, 0], [1, 5], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1714 ⟨![[], [1], [2], [0, 0, 0], [3], [1], [2, 2, 2], [0]], ![[7], [1], [2], [4], [1, 3, 1, 7], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1711 ⟨![[0], [], [2], [1, 4], [0], [], [2, 3, 5], [1]], ![[0], [7], [2], [0, 0], [3, 3], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1718 ⟨![[], [0, 0, 1, 0], [2], [0, 0, 0], [3], [0, 1, 4], [2, 2, 2], [0]], ![[7], [1, 7], [2], [4], [1, 2, 1, 6], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1709 ⟨![[0], [1], [], [2, 2, 2], [0, 2, 2], [1, 3, 5], [2, 2], [2]], ![[0], [1], [7], [0, 0], [0, 1, 4, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5]]⟩, .edge 1716 ⟨![[], [1], [0, 0, 2, 0], [0, 0, 0], [3], [1], [0, 2], [0]], ![[7], [1], [2, 7], [4], [1, 3, 1, 7], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1713 ⟨![[0], [], [2, 1, 4], [1, 4], [0], [], [1, 2], [1]], ![[0], [7], [2, 7], [0, 0], [3, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1720 ⟨![[], [0, 0, 1, 0], [0, 0, 2, 0], [0, 0, 0], [3], [0, 1, 4], [0, 2], [0]], ![[7], [1, 7], [2, 7], [4], [1, 2, 5, 2], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 160) : Classified H :=
  classify_of_checks 160 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node160

namespace Node161

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [5]],
   ![[0], [1], [2], [0, 1, 1, 1, 0, 1], [1, 0, 1, 0], [3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 160) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 161 :=
  generated_of_packed 160 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 1721 ⟨![[], [0], [1], [2], [], [0, 3], [1, 5], [2]], ![[1], [2], [3], [1, 1, 1, 5], [1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .core, .edge 1722 ⟨![[], [0, 3], [1], [2], [], [0], [1, 5], [2]], ![[5], [2], [3], [1, 1, 1, 5], [1, 1], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 161) : Classified H :=
  classify_of_checks 161 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node161

namespace Node162

def gen : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 1, 0, 1], [0, 1, 0, 1, 1, 3, 1], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 161) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 162 :=
  generated_of_packed 161 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .edge 1723 ⟨![[], [0], [1], [2, 3], [], [0, 3], [1, 5], [2, 3]], ![[1], [2], [1, 1, 1, 5, 3], [1, 1, 1, 5], [1, 5], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .core, .edge 1724 ⟨![[], [0, 3], [1], [2, 3], [], [0], [1, 5], [2, 3]], ![[5], [2], [1, 1, 1, 5, 3], [1, 1, 1, 5], [1, 1], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 32, .noncentric 160, .noncentric 128, .noncentric 160, .noncentric 128] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 162) : Classified H :=
  classify_of_checks 162 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node162

namespace Node163

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [1, 1], [0, 0, 0, 0, 1, 0, 1, 0], [1, 0, 1, 0], [0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 162) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 163 :=
  generated_of_packed 162 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .edge 1725 ⟨![[], [0], [1], [0, 1, 2, 4]], ![[1], [2], [1, 1], [1, 2, 2, 3, 2], [1, 3, 2], [1, 2, 2, 2, 3], [1, 2, 2, 2, 3], [1, 2, 2, 2, 3], [1, 2, 2, 2, 3], [1, 2, 2, 2, 3]]⟩, .core, .noncentric 96] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 163) : Classified H :=
  classify_of_checks 163 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node163

namespace Node164

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 1], [0, 1, 0, 1], [0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 163) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 164 :=
  generated_of_packed 163 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .edge 1726 ⟨![[], [0], [1], [0, 2, 1]], ![[1], [2], [2, 1, 2, 1], [2, 2, 3, 2, 1], [3, 2, 1], [1, 2, 2, 2, 3], [1, 2, 2, 2, 3], [1, 2, 2, 2, 3], [1, 2, 2, 2, 3], [1, 2, 2, 2, 3]]⟩, .core, .noncentric 96] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 164) : Classified H :=
  classify_of_checks 164 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node164

namespace Node165

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 3, 3], [0, 1, 0, 1], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 164) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 165 :=
  generated_of_packed 164 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 96, .noncentric 96, .noncentric 96, .noncentric 96, .edge 1729 ⟨![[0], [], [1, 5], [2], [0, 5], [], [1], [2, 5]], ![[0], [6], [3], [0, 0, 2, 2], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1732 ⟨![[], [1, 0, 5], [0, 1, 1], [2], [4, 5], [0, 1, 1, 1], [0], [0, 2, 0]], ![[6], [1, 6], [3], [3, 3, 4], [1, 1], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .noncentric 96, .noncentric 96, .edge 1728 ⟨![[0], [], [2], [1, 5], [0, 5], [], [2, 5], [1]], ![[0], [7], [2], [0, 0, 2, 6], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1731 ⟨![[], [0, 1, 3], [2], [0, 1, 1], [4, 5], [0, 1, 1, 1], [2, 3], [0]], ![[7], [1, 7], [2], [3, 4, 7], [1, 1], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 1727 ⟨![[0], [1], [], [0, 0, 2, 3], [0, 3], [1, 5], [3, 4], [2]], ![[0], [1], [7], [0, 0, 0, 4], [0, 0, 1, 5], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1730 ⟨![[], [1], [0, 2, 5], [0, 3, 4], [4, 5], [1, 5], [0, 2, 3, 4], [0]], ![[7], [1], [2, 7], [3, 4, 7], [1, 4, 5], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .noncentric 96, .noncentric 96] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 165) : Classified H :=
  classify_of_checks 165 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node165

namespace Node166

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 165) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 166 :=
  generated_of_packed 165 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .core, .edge 1733 ⟨![[0], [], [2, 0], []], ![[0], [0, 0, 0, 0, 0, 0, 0, 2, 2, 0], [0, 0, 0, 0, 0, 2, 2, 2], [0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0], [0, 0, 0, 0, 0, 2, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2]]⟩, .edge 1734 ⟨![[], [0, 2, 1, 3], [1, 4], [0]], ![[3], [3, 2, 1], [1, 2, 1], [2, 2], [1, 1, 2, 1, 2, 1], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1, 2, 2]]⟩] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 2 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 166) : Classified H :=
  classify_of_checks 166 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node166

namespace Node167

def gen : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 2 10 :=
  ⟨![[0], [1]],
   ![[0], [1], [1, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 0, 1, 1], [0, 0, 0, 0], [0, 0, 0, 0, 1, 1], [0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 166) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 167 :=
  generated_of_packed 166 gen generationWords generation_checked

def pivot (σ : Fin 2 → Bool) : Fin 2 :=
  ![0, 0, 1, 0] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 2 → Bool) : BranchData 2 :=
  ![.core, .core, .edge 1735 ⟨![[0], [], [2, 0, 3], [3, 4]], ![[0], [2, 3, 2, 3], [0, 2, 2, 2], [0, 0, 0, 0], [0, 0, 0, 0, 3], [0, 0, 2, 2, 3], [0, 0, 2, 2, 3], [0, 0, 2, 2, 3], [0, 0, 2, 2, 3], [0, 0, 2, 2, 3]]⟩, .edge 1736 ⟨![[], [0, 1, 2], [1, 4], [0]], ![[3], [1, 1, 3, 2, 3], [2, 1, 1], [2, 2], [1, 2, 2, 3], [1, 1, 3, 3], [1, 1, 3, 3], [1, 1, 3, 3], [1, 1, 3, 3], [1, 1, 3, 3]]⟩] ⟨signatureIndex σ % 4, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 2 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 2 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 167) : Classified H :=
  classify_of_checks 167 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node167

namespace Node168

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [2, 2], [0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 167) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 168 :=
  generated_of_packed 167 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1738 ⟨![[0], [], [1], [2], [0], [], [1, 4], [0, 0, 2]], ![[0], [2], [3], [2, 2], [0, 3, 0, 3], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1743 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 3], [0, 2, 0]], ![[5], [2], [3], [2, 2], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 2048, .edge 1742 ⟨![[], [1], [0, 0, 0, 3], [2], [0, 0], [1], [0], [2, 3, 5]], ![[6], [1], [3], [2, 6], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1740 ⟨![[0], [], [1, 4], [2], [0], [], [1], [0, 0, 2]], ![[0], [6], [3], [2, 6], [0, 3, 0, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1745 ⟨![[], [0, 0, 1, 0], [0, 0, 0, 3], [2], [0, 0], [1, 0], [0], [1, 2, 1]], ![[6], [1, 6], [3], [2, 6], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 2056, .edge 1741 ⟨![[], [1], [2], [0, 3, 4], [4, 5], [1], [2, 3], [0]], ![[7], [1], [2], [2, 2], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1739 ⟨![[0], [], [2], [0, 0, 1], [0], [], [2, 4], [1]], ![[0], [7], [2], [2, 2], [0, 3, 0, 7], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1744 ⟨![[], [0, 1, 3], [2], [0, 3, 4], [4, 5], [1, 0, 5], [2, 3], [0]], ![[7], [1, 7], [2], [2, 2], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1737 ⟨![[0], [1], [], [2, 3], [0, 3], [1, 4], [3], [2]], ![[0], [1], [7], [6], [1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5]]⟩, .noncentric 64, .noncentric 32, .edge 1746 ⟨![[], [0, 1, 3], [2, 0, 4], [0, 3, 4], [4, 5], [1, 0, 5], [0, 2, 3], [0]], ![[7], [1, 7], [2, 7], [2, 6], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 168) : Classified H :=
  classify_of_checks 168 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node168

namespace Node169

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [2, 2], [0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 168) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 169 :=
  generated_of_packed 168 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1748 ⟨![[0], [], [1], [2], [0], [], [1, 4], [2]], ![[0], [2], [3], [2, 2], [0, 3, 0, 3], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .noncentric 96, .edge 1747 ⟨![[0], [1], [], [2], [0, 3], [1, 4], [3], [2, 5]], ![[0], [1], [3], [6], [1, 5], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1752 ⟨![[], [1], [0, 0, 0, 3], [2], [0, 0], [1], [0], [2, 5]], ![[6], [1], [3], [2, 6], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 32, .edge 1755 ⟨![[], [0, 0, 1, 0], [0, 0, 0, 3], [2], [0, 0], [1, 0], [0], [2, 5]], ![[6], [1, 6], [3], [2, 6], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 2056, .edge 1751 ⟨![[], [1], [2], [0, 4], [4, 5], [1], [2, 3], [0]], ![[7], [1], [2], [2, 2], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1749 ⟨![[0], [], [2], [1], [0], [], [2, 4], [1]], ![[0], [3], [2], [2, 2], [0, 3, 0, 3], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1754 ⟨![[], [1, 0, 4], [2], [0, 4], [4, 5], [0, 1], [2, 3], [0]], ![[7], [1, 7], [2], [2, 2], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .noncentric 2072, .edge 1753 ⟨![[], [1], [2, 0, 4], [0, 4], [4, 5], [1], [0, 2, 5], [0]], ![[7], [1], [2, 7], [2, 6], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 1750 ⟨![[0], [], [2, 1], [1], [0], [], [1, 2, 5], [1]], ![[0], [3], [2, 3], [2, 6], [0, 3, 0, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1756 ⟨![[], [1, 0, 4], [2, 0, 4], [0, 4], [4, 5], [0, 1], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [2, 6], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 169) : Classified H :=
  classify_of_checks 169 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node169

namespace Node170

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [2, 2], [0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 169) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 170 :=
  generated_of_packed 169 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1758 ⟨![[0], [], [1], [2], [0], [], [0, 0, 1], [2]], ![[0], [2], [3], [2, 2], [0, 2, 0, 2], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .noncentric 96, .edge 1757 ⟨![[0], [1], [], [2], [0, 3, 5], [0, 0, 1], [3], [2, 5]], ![[0], [1], [3], [6], [0, 4, 6], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1762 ⟨![[], [1], [0, 3, 4], [2], [4, 5], [1], [0], [2, 5]], ![[6], [1], [3], [2, 6], [2, 2], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 32, .edge 1765 ⟨![[], [0, 1, 3], [0, 3, 4], [2], [4, 5], [1, 0, 5], [0], [2, 5]], ![[6], [1, 6], [3], [2, 6], [2, 2], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 2048, .edge 1761 ⟨![[], [1], [2], [0, 4], [4, 5], [1], [2, 3, 5], [0]], ![[7], [1], [2], [2, 2], [3, 3], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 1759 ⟨![[0], [], [2], [1], [0], [], [0, 0, 2], [1]], ![[0], [3], [2], [2, 2], [0, 2, 0, 2], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 1764 ⟨![[], [1, 0, 4], [2], [0, 4], [4, 5], [0, 1], [2, 3, 5], [0]], ![[7], [1, 7], [2], [2, 2], [3, 3], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 2064, .edge 1763 ⟨![[], [1], [2, 0, 4], [0, 4], [4, 5], [1], [0, 2, 5], [0]], ![[7], [1], [2, 7], [2, 6], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 1760 ⟨![[0], [], [2, 1], [1], [0], [], [1, 2, 5], [1]], ![[0], [3], [2, 3], [2, 6], [0, 2, 0, 6], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 1766 ⟨![[], [1, 0, 4], [2, 0, 4], [0, 4], [4, 5], [0, 1], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [2, 6], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 170) : Classified H :=
  classify_of_checks 170 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node170

namespace Node171

def gen : Fin 5 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [3], [4]],
   ![[0], [1], [2], [3], [4], [0, 2, 0, 2], [1, 2, 1, 2], [1, 2, 1, 2], [1, 2, 1, 2], [1, 2, 1, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 170) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 171 :=
  generated_of_packed 170 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .core, .edge 1770 ⟨![[0], [], [1], [2], [3], [0], [], [1, 5], [2], [3]], ![[0], [2], [3], [4], [0, 0, 2, 7], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 1777 ⟨![[], [0, 0, 0], [1], [2], [3], [0, 0], [0], [1, 5], [2, 5], [3]], ![[6], [2], [3], [4], [2, 5, 7], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 1768 ⟨![[0], [1], [], [2], [3], [0, 5], [1, 5], [], [2], [3]], ![[0], [1], [3], [4], [0, 5], [1, 6], [1, 6], [1, 6], [1, 6], [1, 6]]⟩, .edge 1775 ⟨![[], [1], [0, 4], [2], [3], [4, 5], [1], [0], [2, 5], [3]], ![[7], [1], [3], [4], [2, 2], [3, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 1772 ⟨![[0], [], [1, 5], [2], [3], [0], [], [1], [2], [3]], ![[0], [7], [3], [4], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1779 ⟨![[], [0, 1, 4], [0, 4], [2], [3], [4, 5], [0, 1, 5], [0], [2, 5], [3]], ![[7], [1, 7], [3], [4], [2, 2], [3, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .edge 1767 ⟨![[0], [1], [2], [], [3], [0, 5], [1], [2], [], [3]], ![[0], [1], [2], [4], [0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 1774 ⟨![[], [1], [2], [0, 4], [3], [4, 5], [1], [2, 5], [0], [3]], ![[8], [1], [2], [4], [3, 3], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 1771 ⟨![[0], [], [2], [1], [3], [0], [], [2, 5], [1], [3]], ![[0], [3], [2], [4], [0, 0, 2, 7], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 1778 ⟨![[], [1, 0, 4], [2], [0, 4], [3], [4, 5], [0, 1], [2, 5], [0], [3]], ![[8], [1, 8], [2], [4], [3, 3], [2, 7], [2, 7], [2, 7], [2, 7], [2, 7]]⟩, .edge 1769 ⟨![[0], [1], [], [2], [3], [0, 5], [1, 5], [], [2], [3]], ![[0], [1], [3], [4], [0, 5], [1, 6], [1, 6], [1, 6], [1, 6], [1, 6]]⟩, .edge 1776 ⟨![[], [1], [0, 2, 4], [0, 4], [3], [4, 5], [1], [0, 2], [0], [3]], ![[8], [1], [2, 8], [4], [2, 2], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 1773 ⟨![[0], [], [2, 1], [1], [3], [0], [], [1, 2], [1], [3]], ![[0], [3], [2, 3], [4], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1780 ⟨![[], [1, 0, 4], [0, 2, 4], [0, 4], [3], [4, 5], [0, 1], [0, 2], [0], [3]], ![[8], [1, 8], [2, 8], [4], [2, 2], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 171) : Classified H :=
  classify_of_checks 171 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node171

namespace Node172

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [2, 2], [0, 3, 0, 3], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 171) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 172 :=
  generated_of_packed 171 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1783 ⟨![[0], [], [1], [2], [0, 3, 5], [0, 0, 3], [1, 4], [2, 5]], ![[0], [2], [3], [2, 2], [0, 0, 3, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 96, .noncentric 32, .edge 1788 ⟨![[], [1], [0, 1, 1], [2], [0, 0], [1, 3, 5], [0], [2, 5]], ![[6], [1], [3], [2, 6], [1, 5], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1785 ⟨![[0], [], [1, 3, 5], [2], [0, 3, 5], [0, 0, 3], [1], [2, 5]], ![[0], [6], [3], [2, 6], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1791 ⟨![[], [0, 1], [0, 0, 0, 3], [2], [0, 0], [0, 1, 3, 4], [0], [2, 5]], ![[6], [1, 6], [3], [2, 6], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1781 ⟨![[0], [1], [2], [], [0, 5], [1, 5], [2, 5], []], ![[0], [1], [2], [2, 2], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1787 ⟨![[], [1], [2], [0, 4], [4, 5], [1, 3, 5], [2, 3], [0]], ![[7], [1], [2], [2, 2], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 1784 ⟨![[0], [], [2], [1, 1, 1], [0, 3, 5], [0, 0, 3], [2, 4], [1]], ![[0], [7], [2], [2, 2], [0, 2, 2, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 1790 ⟨![[], [1, 0, 4], [2], [0, 4], [4, 5], [0, 1, 5], [2, 3], [0]], ![[7], [1, 7], [2], [2, 2], [3, 3], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1782 ⟨![[0], [1], [], [2, 2, 2], [0, 3], [1, 4], [3], [2]], ![[0], [1], [7], [6], [0, 1, 5, 4], [1, 5, 6], [1, 5, 6], [1, 5, 6], [1, 5, 6], [1, 5, 6]]⟩, .edge 1789 ⟨![[], [1], [2, 0, 4], [0, 4], [4, 5], [1, 2, 2], [0, 2, 5], [0]], ![[7], [1], [2, 7], [2, 6], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 1786 ⟨![[0], [], [1, 2, 3], [1, 1, 1], [0, 2, 2], [0, 0, 3], [1, 2, 5], [1]], ![[0], [7], [2, 7], [2, 6], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 1792 ⟨![[], [1, 0, 4], [2, 0, 4], [0, 4], [4, 5], [0, 1, 5], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [2, 6], [3, 3], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 172) : Classified H :=
  classify_of_checks 172 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node172

namespace Node173

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [2, 2], [0, 1, 0, 1], [2, 2, 3, 3], [2, 2, 3, 3], [2, 2, 3, 3], [2, 2, 3, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 172) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 173 :=
  generated_of_packed 172 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 1796 ⟨![[0], [], [1], [2], [0, 5], [], [0, 0, 1], [2, 4]], ![[0], [2], [3], [2, 2], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .noncentric 96, .edge 1794 ⟨![[0], [1], [], [2], [0, 3], [0, 0, 1], [3], [2, 5]], ![[0], [1], [3], [6], [0, 1, 0, 1], [3, 3, 6], [3, 3, 6], [3, 3, 6], [3, 3, 6], [3, 3, 6]]⟩, .edge 1801 ⟨![[], [1], [0, 0, 0, 3], [2], [0, 0], [1, 5], [0], [2, 3]], ![[6], [1], [3], [2, 6], [1, 4, 5], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1798 ⟨![[0], [], [0, 0, 1], [2], [0, 5], [], [1], [2, 4]], ![[0], [6], [3], [2, 6], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1803 ⟨![[], [0, 0, 1, 0], [0, 1, 1], [2], [0, 0], [1, 0, 5], [0], [2, 3]], ![[6], [1, 6], [3], [2, 6], [1, 1], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 1793 ⟨![[0], [1], [2], [], [0, 3], [1, 4], [2, 5], [3, 5]], ![[0], [1], [2], [2, 2], [1, 5], [2, 2, 7], [2, 2, 7], [2, 2, 7], [2, 2, 7], [2, 2, 7]]⟩, .edge 1800 ⟨![[], [1], [2], [0, 3, 4, 5], [4, 5], [1, 5], [2, 3], [0]], ![[7], [1], [2], [2, 2], [3, 3], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 1797 ⟨![[0], [], [2], [1, 4], [0, 5], [], [0, 0, 2], [1]], ![[0], [7], [2], [2, 2], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1802 ⟨![[], [1, 0, 4], [2], [0, 1, 1], [4, 5], [1, 0], [2, 3], [0]], ![[7], [1, 7], [2], [2, 2], [1, 1], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 1795 ⟨![[0], [1], [], [2, 3, 5], [0, 3], [0, 0, 1], [3], [2]], ![[0], [1], [7], [6], [0, 1, 0, 1], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7]]⟩, .noncentric 64, .edge 1799 ⟨![[0], [], [1, 1, 1, 2], [1, 4], [0, 5], [], [1, 2, 3], [1]], ![[0], [7], [2, 7], [2, 6], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 1804 ⟨![[], [1, 0, 4], [2, 0, 4], [0, 1, 1], [4, 5], [1, 0], [0, 2, 3], [0]], ![[7], [1, 7], [2, 7], [2, 6], [1, 1], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 173) : Classified H :=
  classify_of_checks 173 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node173

namespace Node174

def gen : Fin 5 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [3], [4]],
   ![[0], [1], [2], [3], [4], [0, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 173) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 174 :=
  generated_of_packed 173 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .core, .edge 1806 ⟨![[0], [], [1], [2], [3], [0, 4, 5], [], [1, 5], [2], [3]], ![[0], [2], [3], [4], [0, 0], [0, 5], [0, 5], [0, 5], [0, 5], [0, 5]]⟩, .edge 1809 ⟨![[], [0, 5], [1], [2], [3], [4], [0], [1, 5], [2], [3]], ![[6], [2], [3], [4], [5], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 1805 ⟨![[0], [1], [], [2], [3], [0, 5], [1, 5], [], [2], [3]], ![[0], [1], [3], [4], [0, 0], [1, 6], [1, 6], [1, 6], [1, 6], [1, 6]]⟩, .edge 1808 ⟨![[], [1], [0, 0, 0], [2], [3], [4], [0, 0, 1], [0], [2], [3]], ![[7], [1], [3], [4], [5], [1, 5, 6], [1, 5, 6], [1, 5, 6], [1, 5, 6], [1, 5, 6]]⟩, .edge 1807 ⟨![[0], [], [1, 5], [2], [3], [0, 4, 5], [], [1], [2], [3]], ![[0], [7], [3], [4], [0, 0], [0, 5], [0, 5], [0, 5], [0, 5], [0, 5]]⟩, .edge 1810 ⟨![[], [0, 1], [0, 0, 0], [2], [3], [4], [0, 1, 5], [0], [2], [3]], ![[7], [1, 7], [3], [4], [5], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 64, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 174) : Classified H :=
  classify_of_checks 174 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node174

end ReeTwo.SylowModel.SmallEvenMaximalLower
