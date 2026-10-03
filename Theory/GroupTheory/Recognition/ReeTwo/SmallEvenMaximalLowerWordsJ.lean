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

namespace Node225

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 0], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 224) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 225 :=
  generated_of_packed 224 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2238 ⟨![[0], [], [1], [2], [0], [], [1], [2, 3]], ![[0], [2], [3], [3, 3], [0, 0], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩, .edge 2244 ⟨![[], [0, 4], [1], [2], [4], [0], [1, 3, 4], [2, 3]], ![[5], [2], [3], [3, 3], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2236 ⟨![[0], [1], [], [2], [0, 3, 4], [1], [3, 4, 5], [2, 4]], ![[0], [1], [3], [0, 4], [0, 0], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7]]⟩, .noncentric 2056, .edge 2240 ⟨![[0], [], [1], [2], [0], [], [1], [2, 3]], ![[0], [2], [3], [3, 3], [0, 0], [2, 3, 2, 7], [2, 3, 2, 7], [2, 3, 2, 7], [2, 3, 2, 7], [2, 3, 2, 7]]⟩, .edge 2245 ⟨![[], [0, 0, 1, 0], [0, 3], [2], [4], [1, 0, 5], [0], [2, 3]], ![[6], [1, 6], [3], [3, 3], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2235 ⟨![[0], [1], [2], [], [0, 3], [1, 3], [2, 4], [3]], ![[0], [1], [2], [7], [0, 0], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7], [2, 6, 7]]⟩, .edge 2242 ⟨![[], [1], [2], [0, 3, 4], [4], [1], [0, 2, 0], [0]], ![[7], [1], [2], [3, 7], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2239 ⟨![[0], [], [2], [1, 3], [0], [], [2], [1]], ![[0], [7], [2], [3, 7], [0, 0], [2, 3, 2, 7], [2, 3, 2, 7], [2, 3, 2, 7], [2, 3, 2, 7], [2, 3, 2, 7]]⟩, .noncentric 2988, .edge 2237 ⟨![[0], [1], [], [2, 3, 5], [0, 3, 4], [1], [3, 4, 5], [2]], ![[0], [1], [7], [0, 4], [0, 0], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2243 ⟨![[], [1], [0, 2, 4], [0, 3, 4], [4], [1], [0, 2, 3, 4], [0]], ![[7], [1], [2, 7], [3, 7], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2241 ⟨![[0], [], [2, 1], [1, 3], [0], [], [2, 1], [1]], ![[0], [7], [2, 7], [3, 7], [0, 0], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩, .edge 2246 ⟨![[], [0, 1, 4], [0, 2, 4], [0, 3, 4], [4], [0, 1], [0, 1, 2, 1], [0]], ![[7], [1, 7], [2, 7], [3, 7], [4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 225) : Classified H :=
  classify_of_checks 225 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node225

namespace Node226

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 3, 0, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 225) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 226 :=
  generated_of_packed 225 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2249 ⟨![[0], [], [1], [2], [0, 3], [], [1, 3], [2]], ![[0], [2], [3], [3, 3], [2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 2256 ⟨![[], [0, 0, 0], [1], [2], [4, 5], [0], [1, 1, 1], [1, 2, 1]], ![[5], [2], [3], [3, 3], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2247 ⟨![[0], [1], [], [2], [0, 3, 4], [1, 3], [3, 4], [0, 0, 2]], ![[0], [1], [3], [1, 5], [1, 5, 6], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7]]⟩, .edge 2254 ⟨![[], [1], [0, 3, 5], [2], [0, 0], [1, 3], [0], [0, 2, 0]], ![[6], [1], [3], [1, 5], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2251 ⟨![[0], [], [1, 3], [2], [0, 3], [], [1], [2]], ![[0], [6], [3], [3, 3], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 2258 ⟨![[], [0, 0, 1, 0], [0, 3, 5], [2], [0, 0], [0, 1, 4], [0], [0, 2, 0]], ![[6], [1, 6], [3], [3, 3], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 2056, .edge 2253 ⟨![[], [1], [2], [0, 2, 2], [4, 5], [1, 3], [2, 2, 2], [0]], ![[7], [1], [2], [1, 5], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 2250 ⟨![[0], [], [2], [1], [0, 3], [], [2, 3], [1]], ![[0], [3], [2], [3, 3], [2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 2257 ⟨![[], [1, 0, 4], [2], [0, 2, 2], [4, 5], [0, 1, 3], [2, 2, 2], [0]], ![[7], [1, 7], [2], [3, 7], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 2248 ⟨![[0], [1], [], [2, 3, 5], [0, 3, 4], [1, 3], [3, 4], [2]], ![[0], [1], [7], [1, 5], [1, 5, 6], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2255 ⟨![[], [1], [0, 2, 4], [0, 3, 4], [4, 5], [1, 3], [0, 2, 3, 4, 5], [0]], ![[7], [1], [2, 7], [1, 5], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 2252 ⟨![[0], [], [2, 1, 3], [1], [0, 3], [], [2, 1], [1]], ![[0], [3], [2, 3], [3, 3], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 2259 ⟨![[], [1, 0, 4], [0, 2, 4], [0, 3, 4], [4, 5], [0, 1, 3], [0, 1, 2, 1, 3], [0]], ![[7], [1, 7], [2, 7], [3, 7], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 226) : Classified H :=
  classify_of_checks 226 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node226

namespace Node227

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 1], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 226) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 227 :=
  generated_of_packed 226 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2262 ⟨![[0], [], [1], [2], [0, 3, 5], [3], [1, 4, 5], [2, 3]], ![[0], [2], [3], [5], [0, 0], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 2269 ⟨![[], [0, 0, 0, 3], [1], [2], [4], [0], [0, 0, 1], [2, 3]], ![[5], [2], [3], [1, 5], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 2260 ⟨![[0], [1], [], [2], [0, 4, 5], [1, 4, 5], [], [2, 4]], ![[0], [1], [3], [1, 1], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2267 ⟨![[], [1], [0, 5], [2], [4], [1, 3, 5], [0], [2, 3]], ![[6], [1], [3], [1, 1], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2264 ⟨![[0], [], [1, 1, 1], [2], [0, 3, 5], [3], [1], [2, 3]], ![[0], [6], [3], [5], [0, 0], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6]]⟩, .edge 2270 ⟨![[], [0, 1, 3], [0, 5], [2], [4], [0, 1, 4, 5], [0], [2, 3]], ![[6], [1, 6], [3], [1, 5], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .noncentric 2048, .edge 2266 ⟨![[], [1], [2], [0, 3, 4], [4], [1, 3, 5], [0, 2, 0], [0]], ![[7], [1], [2], [1, 1], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2263 ⟨![[0], [], [2], [1], [0, 3, 5], [3], [2, 4, 5], [1]], ![[0], [3], [2], [5], [0, 0], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .noncentric 24, .edge 2261 ⟨![[0], [1], [], [2, 4], [0, 4, 5], [1, 4, 5], [], [2]], ![[0], [1], [7], [1, 1], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2268 ⟨![[], [1], [2, 0, 4], [0, 2, 2], [4], [1, 3, 5], [0, 2, 2, 2], [0]], ![[7], [1], [2, 7], [1, 1], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2265 ⟨![[0], [], [1, 2, 5], [1], [0, 3, 5], [3], [1, 2, 2, 2], [1]], ![[0], [3], [2, 3], [5], [0, 0], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6]]⟩, .edge 2271 ⟨![[], [1, 0, 4], [2, 0, 4], [0, 2, 2], [4], [0, 1], [0, 2, 2, 2], [0]], ![[7], [1, 7], [2, 7], [1, 5], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 227) : Classified H :=
  classify_of_checks 227 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node227

namespace Node228

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 3, 0, 3], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 227) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 228 :=
  generated_of_packed 227 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2275 ⟨![[0], [], [1], [2], [0], [], [1, 4], [2]], ![[0], [2], [3], [3, 3], [2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .noncentric 2048, .edge 2273 ⟨![[0], [1], [], [2], [0, 4], [1, 4], [], [0, 0, 2]], ![[0], [1], [3], [3, 3], [1, 5], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2279 ⟨![[], [1], [0, 5], [2], [4, 5], [1], [0], [2, 3, 5]], ![[6], [1], [3], [3, 3], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2277 ⟨![[0], [], [1, 4], [2], [0], [], [1], [2]], ![[0], [6], [3], [3, 3], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 2280 ⟨![[], [0, 1, 5], [0, 5], [2], [4, 5], [0, 1, 4], [0], [2, 3, 5]], ![[6], [1, 6], [3], [3, 3], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2272 ⟨![[0], [1], [2], [], [0, 3, 5], [1], [0, 0, 2], [3]], ![[0], [1], [2], [7], [0, 4, 7], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .noncentric 80, .edge 2276 ⟨![[0], [], [2], [1], [0], [], [2, 4], [1]], ![[0], [3], [2], [3, 3], [2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .noncentric 24, .edge 2274 ⟨![[0], [1], [], [0, 0, 2], [0, 4], [1, 4], [], [2]], ![[0], [1], [7], [3, 7], [1, 5], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .noncentric 2988, .edge 2278 ⟨![[0], [], [2, 1, 3], [1], [0], [], [1, 2, 2, 2], [1]], ![[0], [3], [2, 3], [3, 3], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 2281 ⟨![[], [1, 0, 4], [2, 0, 4], [0, 3, 4], [4, 5], [0, 1, 3], [0, 2, 2, 2], [0]], ![[7], [1, 7], [2, 7], [3, 7], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 228) : Classified H :=
  classify_of_checks 228 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node228

namespace Node229

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 1], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 228) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 229 :=
  generated_of_packed 228 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 64, .noncentric 24, .edge 2282 ⟨![[0], [1], [], [2], [0, 4, 5], [1, 4, 5], [], [2, 5]], ![[0], [1], [3], [1, 1], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .noncentric 36, .edge 2285 ⟨![[0], [], [1, 1, 1], [2], [0, 3, 5], [3], [1], [2, 3]], ![[0], [6], [3], [5], [0, 0], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6]]⟩, .edge 2290 ⟨![[], [0, 1, 3], [0, 5], [2], [4], [0, 1, 4, 5], [0], [2, 5]], ![[6], [1, 6], [3], [1, 5], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .noncentric 2048, .edge 2287 ⟨![[], [1], [2], [0, 0, 0], [4], [1, 3, 5], [0, 0, 2], [0]], ![[7], [1], [2], [1, 1], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2284 ⟨![[0], [], [2], [1], [0, 3, 5], [3], [2, 4, 5], [1]], ![[0], [3], [2], [5], [0, 0], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 2289 ⟨![[], [0, 0, 0, 1], [2], [0, 0, 0], [4], [0, 1, 3], [0, 0, 2], [0]], ![[7], [1, 7], [2], [1, 5], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 2283 ⟨![[0], [1], [], [2, 5], [0, 4, 5], [1, 4, 5], [], [2]], ![[0], [1], [7], [1, 1], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2288 ⟨![[], [1], [0, 2], [0, 0, 0], [4], [1, 3, 5], [0, 2, 5], [0]], ![[7], [1], [2, 7], [1, 1], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2286 ⟨![[0], [], [2, 1], [1], [0, 3, 5], [3], [1, 2, 5], [1]], ![[0], [3], [2, 3], [5], [0, 0], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6]]⟩, .edge 2291 ⟨![[], [0, 0, 0, 1], [0, 2], [0, 0, 0], [4], [0, 1, 3], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [1, 5], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 229) : Classified H :=
  classify_of_checks 229 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node229

namespace Node230

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 1], [0, 0], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 229) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 230 :=
  generated_of_packed 229 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2294 ⟨![[0], [], [1], [2], [0, 3, 5], [3], [1, 4, 5], [2, 3]], ![[0], [2], [3], [5], [0, 0], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩, .edge 2301 ⟨![[], [0, 1, 1], [1], [2], [4], [0], [0, 1, 0], [2, 3]], ![[5], [2], [3], [1, 5], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2292 ⟨![[0], [1], [], [2], [0, 3, 4], [1, 4, 5], [3, 4, 5], [2, 4]], ![[0], [1], [3], [0, 4], [0, 0], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7], [3, 6, 7]]⟩, .edge 2299 ⟨![[], [1], [0, 3], [2], [4], [0, 1, 0], [0], [2, 3]], ![[6], [1], [3], [1, 1], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2296 ⟨![[0], [], [1, 3, 4, 5], [2], [0, 3, 5], [3], [1], [2, 3]], ![[0], [6], [3], [5], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2303 ⟨![[], [0, 0, 0, 1], [0, 3], [2], [4], [0, 1, 3], [0], [2, 3]], ![[6], [1, 6], [3], [1, 5], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .noncentric 2048, .edge 2298 ⟨![[], [1], [2], [0, 3, 4], [4], [1, 3, 5], [0, 2, 0], [0]], ![[7], [1], [2], [1, 1], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2295 ⟨![[0], [], [2], [1], [0, 3, 5], [3], [2, 4, 5], [1]], ![[0], [3], [2], [5], [0, 0], [2, 3, 6, 3], [2, 3, 6, 3], [2, 3, 6, 3], [2, 3, 6, 3], [2, 3, 6, 3]]⟩, .edge 2302 ⟨![[], [1, 0, 4], [2], [0, 3, 4], [4], [0, 1], [0, 2, 0], [0]], ![[7], [1, 7], [2], [1, 5], [4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2293 ⟨![[0], [1], [], [2, 3, 5], [0, 3, 4], [1, 4, 5], [3, 4, 5], [2]], ![[0], [1], [7], [0, 4], [0, 0], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2300 ⟨![[], [1], [0, 2, 4], [0, 3, 4], [4], [1, 3, 5], [0, 2, 3, 4], [0]], ![[7], [1], [2, 7], [1, 1], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2297 ⟨![[0], [], [1, 2, 5], [1], [0, 3, 5], [3], [1, 2, 3, 4], [1]], ![[0], [3], [2, 3], [5], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2304 ⟨![[], [1, 0, 4], [0, 2, 4], [0, 3, 4], [4], [0, 1], [0, 2, 3, 4], [0]], ![[7], [1, 7], [2, 7], [1, 5], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 230) : Classified H :=
  classify_of_checks 230 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node230

namespace Node231

def gen : Fin 5 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [3], [4]],
   ![[0], [1], [2], [3], [4], [0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 230) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 231 :=
  generated_of_packed 230 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .core, .edge 2306 ⟨![[0], [], [1], [2], [3], [0], [], [1], [0, 0, 2], [3]], ![[0], [2], [3], [4], [0, 3, 0, 3], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8], [0, 3, 0, 8]]⟩, .edge 2309 ⟨![[], [0, 0, 0], [1], [2], [3], [0, 0], [0], [1], [2, 5], [3]], ![[6], [2], [3], [4], [3, 5, 8], [3, 8], [3, 8], [3, 8], [3, 8], [3, 8]]⟩, .noncentric 16, .noncentric 16, .noncentric 16, .noncentric 16, .edge 2305 ⟨![[0], [1], [2], [], [3], [0, 5], [0, 0, 1], [2], [], [3]], ![[0], [1], [2], [4], [0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5], [0, 0, 0, 5]]⟩, .edge 2308 ⟨![[], [1], [2], [0, 4], [3], [4, 5], [1], [2], [0], [3]], ![[8], [1], [2], [4], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .edge 2307 ⟨![[0], [], [2], [0, 0, 1], [3], [0], [], [2], [1], [3]], ![[0], [8], [2], [4], [0, 3, 0, 8], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3], [0, 3, 0, 3]]⟩, .edge 2310 ⟨![[], [0, 1], [2], [0, 4], [3], [1, 1], [1, 0, 5], [2], [0], [3]], ![[8], [1, 8], [2], [4], [3, 3], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5], [3, 3, 5]]⟩, .noncentric 16, .noncentric 16, .noncentric 16, .noncentric 16, .noncentric 16, .noncentric 16, .noncentric 16, .noncentric 16, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 16, .noncentric 16, .noncentric 16, .noncentric 16, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 231) : Classified H :=
  classify_of_checks 231 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node231

namespace Node232

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 1, 3, 0, 1, 3], [0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 231) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 232 :=
  generated_of_packed 231 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2312 ⟨![[0], [], [1], [2], [0], [], [0, 0, 1], [0, 0, 2, 3]], ![[0], [2], [3], [0, 3, 0, 7], [3, 7], [0, 0, 3, 7], [0, 0, 3, 7], [0, 0, 3, 7], [0, 0, 3, 7], [0, 0, 3, 7]]⟩, .edge 2319 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 5], [2, 2, 2]], ![[5], [2], [3], [1, 3, 1, 3], [2, 4, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 2072, .edge 2317 ⟨![[], [1], [0, 4], [2], [4, 5], [1], [0], [2, 2, 2]], ![[6], [1], [3], [2, 3, 2, 7], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2314 ⟨![[0], [], [0, 0, 1], [2], [0], [], [1], [1, 2, 1]], ![[0], [6], [3], [0, 3, 0, 7], [3, 7], [0, 0, 3, 7], [0, 0, 3, 7], [0, 0, 3, 7], [0, 0, 3, 7], [0, 0, 3, 7]]⟩, .edge 2321 ⟨![[], [0, 1], [0, 4], [2], [1, 1], [1, 0, 5], [0], [2, 2, 2]], ![[6], [1, 6], [3], [1, 3, 1, 3], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .noncentric 16, .edge 2316 ⟨![[], [1], [2], [0, 3, 4], [0, 0], [1], [2, 5], [0]], ![[7], [1], [2], [1, 3, 1, 3], [2, 4, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2313 ⟨![[0], [], [2], [0, 0, 1, 3], [0], [], [0, 0, 2], [1]], ![[0], [7], [2], [0, 3, 0, 3], [3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 2320 ⟨![[], [0, 1, 5], [2], [0, 3, 4], [0, 0], [1, 0], [2, 5], [0]], ![[7], [1, 7], [2], [1, 3, 1, 7], [2, 4, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2311 ⟨![[0], [1], [], [0, 0, 2], [0, 5], [0, 0, 1], [], [2]], ![[0], [1], [7], [0, 3, 3, 4], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2318 ⟨![[], [1], [0, 2, 3], [0, 2, 2], [0, 0], [1], [2, 0, 5], [0]], ![[7], [1], [2, 7], [1, 3, 1, 3], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2315 ⟨![[0], [], [2, 1, 4], [0, 0, 1, 3], [0], [], [2, 1, 5], [1]], ![[0], [7], [2, 7], [0, 3, 0, 3], [3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3], [0, 0, 3, 3]]⟩, .edge 2322 ⟨![[], [0, 1, 5], [0, 2, 3], [0, 2, 2], [0, 0], [1, 0], [2, 0, 5], [0]], ![[7], [1, 7], [2, 7], [1, 3, 1, 7], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 232) : Classified H :=
  classify_of_checks 232 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node232

namespace Node233

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [1, 3, 1, 3], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 232) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 233 :=
  generated_of_packed 232 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 2056, .edge 2331 ⟨![[], [0, 4], [1], [2], [4, 5], [0], [1], [2, 3]], ![[5], [2], [3], [3, 3], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2324 ⟨![[0], [1], [], [2], [0], [1], [], [2, 4]], ![[0], [1], [3], [3, 3], [1, 3, 1, 3], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 2329 ⟨![[], [1], [0, 0, 0], [2], [0, 0], [1, 5], [0], [2, 3]], ![[6], [1], [3], [3, 3], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2326 ⟨![[0], [], [0, 0, 1], [2], [0, 5], [0, 0], [1], [2, 3, 5]], ![[0], [6], [3], [3, 3], [0, 4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2333 ⟨![[], [0, 1, 4], [0, 0, 0], [2], [0, 0], [0, 1], [0], [2, 3]], ![[6], [1, 6], [3], [3, 3], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2323 ⟨![[0], [1], [2], [], [0, 3], [1, 3, 5], [2, 4], [3]], ![[0], [1], [2], [7], [2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 2328 ⟨![[], [1], [2], [1, 0, 1], [0, 0], [1, 5], [2], [0]], ![[7], [1], [2], [3, 7], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .noncentric 2072, .edge 2332 ⟨![[], [0, 0, 0, 1], [2], [0, 0, 0, 3], [0, 0], [0, 1, 5], [2], [0]], ![[7], [1, 7], [2], [3, 7], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2325 ⟨![[0], [1], [], [2, 4], [0], [1], [], [2]], ![[0], [1], [7], [3, 7], [1, 3, 1, 7], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 2330 ⟨![[], [1], [0, 0, 2, 0], [1, 0, 1], [0, 0], [1, 5], [2, 0], [0]], ![[7], [1], [2, 7], [3, 7], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2327 ⟨![[0], [], [2, 1, 4], [0, 1, 0], [0, 5], [0, 0], [2, 1, 5], [1]], ![[0], [7], [2, 7], [3, 7], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2334 ⟨![[], [0, 0, 0, 1], [0, 0, 2, 0], [0, 0, 0, 3], [0, 0], [0, 1, 5], [2, 0], [0]], ![[7], [1, 7], [2, 7], [3, 7], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 233) : Classified H :=
  classify_of_checks 233 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node233

namespace Node234

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 0, 1, 0, 1], [0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 233) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 234 :=
  generated_of_packed 233 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2336 ⟨![[0], [], [1], [2], [0, 3], [], [1, 4], [2, 4]], ![[0], [2], [3], [0, 0, 0, 4], [2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 2341 ⟨![[], [0, 0, 0], [1], [2], [4, 5], [0], [1], [2, 5]], ![[5], [2], [3], [1, 1, 4], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2335 ⟨![[0], [1], [], [2], [0], [1, 4], [], [2]], ![[0], [1], [3], [0, 0, 0, 1, 0, 1], [1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5]]⟩, .edge 2340 ⟨![[], [1], [0, 0, 0], [2], [0, 0], [1, 3], [0], [2, 5]], ![[6], [1], [3], [1, 5], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2337 ⟨![[0], [], [1, 4], [2], [0, 3], [], [1], [2, 4]], ![[0], [6], [3], [0, 0, 0, 4], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 2343 ⟨![[], [0, 0, 1, 0], [0, 0, 0], [2], [0, 0], [0, 1, 4], [0], [2, 5]], ![[6], [1, 6], [3], [1, 1, 4], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 2056, .edge 2339 ⟨![[], [1], [2], [0, 4], [4, 5], [1, 3], [2], [0]], ![[7], [1], [2], [1, 5], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .noncentric 2072, .edge 2342 ⟨![[], [1, 0, 4], [2], [0, 4], [4, 5], [0, 1, 4], [2], [0]], ![[7], [1, 7], [2], [1, 1, 4], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .noncentric 56, .noncentric 104, .edge 2338 ⟨![[0], [], [1, 2, 4], [1, 4], [0, 3], [], [1, 2], [1]], ![[0], [7], [2, 7], [0, 0, 0, 4], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 2344 ⟨![[], [1, 0, 4], [2, 0, 4], [0, 4], [4, 5], [0, 1, 4], [0, 2], [0]], ![[7], [1, 7], [2, 7], [1, 1, 4], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 234) : Classified H :=
  classify_of_checks 234 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node234

namespace Node235

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 234) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 235 :=
  generated_of_packed 234 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2348 ⟨![[0], [], [1], [2], [0, 4, 5], [], [1], [2, 3]], ![[0], [2], [3], [3, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2354 ⟨![[], [0, 5], [1], [2], [4], [0], [1], [2, 3, 5]], ![[5], [2], [3], [3, 3], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2346 ⟨![[0], [1], [], [2], [0], [1], [], [2, 4]], ![[0], [1], [3], [3, 3], [0, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 2352 ⟨![[], [1], [0, 4], [2], [4], [1, 4, 5], [0], [0, 2, 0]], ![[6], [1], [3], [3, 3], [4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2350 ⟨![[0], [], [1], [2], [0, 4, 5], [], [1], [2, 3]], ![[0], [2], [3], [3, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2356 ⟨![[], [0, 1, 5], [0, 4], [2], [4], [0, 1], [0], [0, 2, 0]], ![[6], [1, 6], [3], [3, 3], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2345 ⟨![[0], [1], [2], [], [0, 3, 5], [1, 3], [2, 4], [3]], ![[0], [1], [2], [7], [0, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .noncentric 2072, .edge 2349 ⟨![[0], [], [2], [1, 3], [0, 4, 5], [], [2], [1]], ![[0], [7], [2], [3, 7], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2355 ⟨![[], [0, 1, 5], [2], [0, 0, 0, 3], [4], [0, 1], [2], [0]], ![[7], [1, 7], [2], [3, 7], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2347 ⟨![[0], [1], [], [2, 4], [0], [1], [], [2]], ![[0], [1], [7], [3, 7], [0, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 2353 ⟨![[], [1], [0, 2, 3], [1, 0, 1], [4], [0, 0, 1], [2, 0, 5], [0]], ![[7], [1], [2, 7], [3, 7], [4], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2351 ⟨![[0], [], [2, 1], [1, 3], [0, 4, 5], [], [2, 1], [1]], ![[0], [7], [2, 7], [3, 7], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2357 ⟨![[], [0, 1, 5], [0, 2, 3], [0, 0, 0, 3], [4], [0, 1], [2, 0, 5], [0]], ![[7], [1, 7], [2, 7], [3, 7], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 235) : Classified H :=
  classify_of_checks 235 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node235

namespace Node236

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 0, 1, 0, 1], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 235) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 236 :=
  generated_of_packed 235 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2360 ⟨![[0], [], [1], [2], [0, 3], [], [1], [0, 0, 2]], ![[0], [2], [3], [0, 0, 0, 4], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2365 ⟨![[], [0, 0, 0], [1], [2], [4, 5], [0], [1, 4], [2]], ![[5], [2], [3], [1, 1, 4], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2358 ⟨![[0], [1], [], [2], [0, 4], [1], [], [2]], ![[0], [1], [3], [0, 0, 0, 1, 0, 1], [0, 0, 0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .noncentric 4, .edge 2362 ⟨![[0], [], [1], [2], [0, 3], [], [1], [0, 0, 2]], ![[0], [2], [3], [0, 0, 0, 4], [0, 0, 0, 2, 4, 2], [0, 2, 4, 2], [0, 2, 4, 2], [0, 2, 4, 2], [0, 2, 4, 2], [0, 2, 4, 2]]⟩, .noncentric 68, .noncentric 2056, .noncentric 2072, .edge 2361 ⟨![[0], [], [2], [0, 0, 1], [0, 3], [], [2], [1]], ![[0], [7], [2], [0, 0, 0, 4], [0, 0, 0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2366 ⟨![[], [0, 1, 3], [2], [0, 0, 0], [0, 0], [1, 0, 3], [2, 4], [0]], ![[7], [1, 7], [2], [1, 1, 4], [2, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6], [2, 4, 6]]⟩, .edge 2359 ⟨![[0], [1], [], [2], [0, 4], [1], [], [2]], ![[0], [1], [3], [0, 0, 0, 1, 0, 1], [0, 0, 0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2364 ⟨![[], [1], [0, 2, 5], [0, 0, 0], [0, 0], [1, 3], [0, 2], [0]], ![[7], [1], [2, 7], [1, 5], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2363 ⟨![[0], [], [1, 2], [0, 0, 1], [0, 3], [], [1, 2], [1]], ![[0], [7], [2, 7], [0, 0, 0, 4], [0, 0, 0, 2, 4, 2], [0, 2, 4, 2], [0, 2, 4, 2], [0, 2, 4, 2], [0, 2, 4, 2], [0, 2, 4, 2]]⟩, .edge 2367 ⟨![[], [0, 1, 3], [0, 2, 5], [0, 0, 0], [0, 0], [1, 0, 3], [0, 2], [0]], ![[7], [1, 7], [2, 7], [1, 1, 4], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 236) : Classified H :=
  classify_of_checks 236 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node236

namespace Node237

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 0], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 236) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 237 :=
  generated_of_packed 236 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2371 ⟨![[0], [], [1], [2], [0, 4], [4, 5], [1], [2, 3, 5]], ![[0], [2], [3], [3, 3], [0, 0], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2378 ⟨![[], [0], [1], [2], [4], [0], [1], [2, 3, 5]], ![[1], [2], [3], [3, 3], [4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2369 ⟨![[0], [1], [], [2], [0], [1], [], [2, 4]], ![[0], [1], [3], [3, 3], [0, 0], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩, .edge 2376 ⟨![[], [1], [0, 4], [2], [4], [1, 4], [0], [0, 2, 0]], ![[6], [1], [3], [3, 3], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2373 ⟨![[0], [], [1, 1, 1], [2], [0, 4], [1, 1], [1], [2, 3, 5]], ![[0], [6], [3], [3, 3], [0, 0], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2380 ⟨![[], [0, 1], [0, 4], [2], [4], [0, 1], [0], [0, 2, 0]], ![[6], [1, 6], [3], [3, 3], [4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2368 ⟨![[0], [1], [2], [], [0, 3, 5], [1, 3, 5], [2, 4], [3]], ![[0], [1], [2], [7], [0, 0], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩, .edge 2375 ⟨![[], [1], [2], [0, 0, 0, 3], [4], [1, 4], [2], [0]], ![[7], [1], [2], [3, 7], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2372 ⟨![[0], [], [2], [1, 3, 4], [0, 4], [4, 5], [2], [1]], ![[0], [7], [2], [3, 7], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2379 ⟨![[], [0, 1, 5], [2], [0, 0, 0, 3], [4], [0, 1, 5], [2], [0]], ![[7], [1, 7], [2], [3, 7], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 2370 ⟨![[0], [1], [], [2, 4], [0], [1], [], [2]], ![[0], [1], [7], [3, 7], [0, 0], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩, .edge 2377 ⟨![[], [1], [0, 2, 3], [0, 0, 0, 3], [4], [1, 4], [2, 0, 5], [0]], ![[7], [1], [2, 7], [3, 7], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2374 ⟨![[0], [], [2, 1, 4], [1, 2, 2], [0, 4], [4, 5], [2, 1, 5], [1]], ![[0], [7], [2, 7], [3, 7], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2381 ⟨![[], [0, 1, 5], [0, 2, 3], [0, 0, 0, 3], [4], [0, 1, 5], [2, 0, 5], [0]], ![[7], [1, 7], [2, 7], [3, 7], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 237) : Classified H :=
  classify_of_checks 237 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node237

namespace Node238

def gen : Fin 5 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 5 10 :=
  ⟨![[0], [1], [2], [3], [4]],
   ![[0], [1], [2], [3], [4], [1, 2, 1, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 237) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 238 :=
  generated_of_packed 237 gen generationWords generation_checked

def pivot (σ : Fin 5 → Bool) : Fin 5 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 5 → Bool) : BranchData 5 :=
  ![.core, .core, .edge 2385 ⟨![[0], [], [1], [2], [3], [0], [], [1, 4], [2, 4], [3]], ![[0], [2], [3], [4], [2, 7], [0, 0, 2, 7], [0, 0, 2, 7], [0, 0, 2, 7], [0, 0, 2, 7], [0, 0, 2, 7]]⟩, .edge 2392 ⟨![[], [0, 0, 0], [1], [2], [3], [0, 0], [0], [1, 4], [2], [3]], ![[6], [2], [3], [4], [2, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7]]⟩, .edge 2383 ⟨![[0], [1], [], [2], [3], [0, 4], [1, 4], [], [2], [3]], ![[0], [1], [3], [4], [1, 6], [0, 5], [0, 5], [0, 5], [0, 5], [0, 5]]⟩, .edge 2390 ⟨![[], [1], [0, 5], [2], [3], [4, 5], [1], [0], [2], [3]], ![[7], [1], [3], [4], [2, 2, 5], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2387 ⟨![[0], [], [1, 4], [2], [3], [0], [], [1], [2, 4], [3]], ![[0], [7], [3], [4], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 2394 ⟨![[], [0, 1, 5], [0, 5], [2], [3], [4, 5], [0, 1, 4], [0], [2], [3]], ![[7], [1, 7], [3], [4], [2, 2, 5], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2382 ⟨![[0], [1], [2], [], [3], [0], [1, 4], [2], [], [3]], ![[0], [1], [2], [4], [1, 6], [0, 0, 1, 6], [0, 0, 1, 6], [0, 0, 1, 6], [0, 0, 1, 6], [0, 0, 1, 6]]⟩, .edge 2389 ⟨![[], [1], [2], [0, 0, 0], [3], [0, 0], [1], [2, 4], [0], [3]], ![[8], [1], [2], [4], [2, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7]]⟩, .edge 2386 ⟨![[0], [], [2], [1, 4], [3], [0], [], [2, 4], [1], [3]], ![[0], [8], [2], [4], [2, 7], [0, 0, 2, 7], [0, 0, 2, 7], [0, 0, 2, 7], [0, 0, 2, 7], [0, 0, 2, 7]]⟩, .edge 2393 ⟨![[], [0, 1, 5], [2], [0, 0, 0], [3], [0, 0], [1, 0], [2, 4], [0], [3]], ![[8], [1, 8], [2], [4], [2, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7], [2, 5, 7]]⟩, .edge 2384 ⟨![[0], [1], [], [2], [3], [0, 4], [1, 4], [], [2], [3]], ![[0], [1], [3], [4], [1, 6], [0, 5], [0, 5], [0, 5], [0, 5], [0, 5]]⟩, .edge 2391 ⟨![[], [1], [0, 2, 5], [0, 0, 0], [3], [0, 0], [1], [0, 2], [0], [3]], ![[8], [1], [2, 8], [4], [2, 2, 5], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2388 ⟨![[0], [], [1, 2, 4], [1, 4], [3], [0], [], [1, 2], [1], [3]], ![[0], [8], [2, 8], [4], [2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 2, 2]]⟩, .edge 2395 ⟨![[], [0, 1, 5], [0, 2, 5], [0, 0, 0], [3], [0, 0], [1, 0], [0, 2], [0], [3]], ![[8], [1, 8], [2, 8], [4], [2, 2, 5], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128, .noncentric 128] ⟨signatureIndex σ % 32, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 5 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 238) : Classified H :=
  classify_of_checks 238 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node238

namespace Node239

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 2, 3, 2, 3], [0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 238) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 239 :=
  generated_of_packed 238 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2397 ⟨![[0], [], [1], [2], [0], [], [0, 0, 1], [0, 0, 2]], ![[0], [2], [3], [2, 3, 2, 7], [0, 2, 0, 2], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 2404 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 5], [2, 3]], ![[5], [2], [3], [2, 3, 3, 6], [2, 4, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 2064, .edge 2402 ⟨![[], [1], [0, 4], [2], [4, 5], [1], [0], [2, 3]], ![[6], [1], [3], [3, 3, 3, 7], [2, 2], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2399 ⟨![[0], [], [0, 0, 1], [2], [0], [], [1], [0, 0, 2]], ![[0], [6], [3], [2, 3, 2, 7], [0, 2, 0, 6], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2406 ⟨![[], [0, 1], [0, 4], [2], [1, 1], [1, 0, 5], [0], [2, 3]], ![[6], [1, 6], [3], [3, 3, 3, 7], [2, 2], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 16, .edge 2401 ⟨![[], [1], [2], [0, 3, 4, 5], [4, 5], [1], [2, 5], [0]], ![[7], [1], [2], [2, 3, 7, 6], [3, 3], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2398 ⟨![[0], [], [2], [0, 0, 1], [0], [], [0, 0, 2], [1]], ![[0], [7], [2], [2, 3, 2, 7], [0, 2, 0, 2], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 2405 ⟨![[], [1, 0, 4], [2], [0, 1, 1, 5], [4, 5], [1, 0, 5], [2, 5], [0]], ![[7], [1, 7], [2], [2, 3, 7, 6], [3, 3], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2396 ⟨![[0], [1], [], [2, 4], [0, 5], [0, 0, 1], [], [2]], ![[0], [1], [7], [0, 0, 3, 3], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2403 ⟨![[], [1], [2, 0, 4], [0, 2, 2], [4, 5], [1], [2, 0], [0]], ![[7], [1], [2, 7], [2, 2, 3, 4, 7], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2400 ⟨![[0], [], [1, 2, 3], [0, 0, 1], [0], [], [0, 1, 0, 2], [1]], ![[0], [7], [2, 7], [2, 3, 2, 7], [0, 2, 0, 6], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2407 ⟨![[], [1, 0, 4], [2, 0, 4], [0, 2, 2], [4, 5], [1, 0, 5], [2, 0], [0]], ![[7], [1, 7], [2, 7], [2, 2, 3, 4, 7], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 239) : Classified H :=
  classify_of_checks 239 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node239

namespace Node240

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 3, 0, 3], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 239) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 240 :=
  generated_of_packed 239 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .noncentric 2048, .edge 2416 ⟨![[], [0, 4], [1], [2], [4, 5], [0], [1], [0, 2, 0]], ![[5], [2], [3], [3, 3], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2409 ⟨![[0], [1], [], [2], [0], [1], [], [0, 0, 2]], ![[0], [1], [3], [3, 3], [0, 3, 0, 3], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 2414 ⟨![[], [1], [0, 0, 0], [2], [0, 0], [1, 5], [0], [0, 2, 0]], ![[6], [1], [3], [3, 3], [1, 5], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2411 ⟨![[0], [], [0, 0, 1], [2], [0, 5], [0, 0], [1], [2, 5]], ![[0], [6], [3], [3, 3], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2418 ⟨![[], [0, 1, 4], [0, 0, 0], [2], [0, 0], [0, 1], [0], [0, 2, 0]], ![[6], [1, 6], [3], [3, 3], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2408 ⟨![[0], [1], [2], [], [0, 3, 5], [1, 5], [0, 0, 2], [3]], ![[0], [1], [2], [7], [1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5], [0, 0, 1, 5]]⟩, .edge 2413 ⟨![[], [1], [2], [0, 3, 4], [1, 1], [1, 5], [2], [0]], ![[7], [1], [2], [3, 7], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .noncentric 2064, .edge 2417 ⟨![[], [1, 0, 4], [2], [0, 1, 1], [4, 5], [1, 0], [2], [0]], ![[7], [1, 7], [2], [3, 7], [3, 3], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2410 ⟨![[0], [1], [], [0, 0, 2], [0], [1], [], [2]], ![[0], [1], [7], [3, 7], [0, 3, 0, 7], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 2415 ⟨![[], [1], [0, 2, 3], [0, 3, 4], [1, 1], [1, 5], [2, 0, 5], [0]], ![[7], [1], [2, 7], [3, 7], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2412 ⟨![[0], [], [1, 2, 3], [1, 4], [0, 5], [0, 0], [0, 1, 0, 2], [1]], ![[0], [7], [2, 7], [3, 7], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2419 ⟨![[], [1, 0, 4], [0, 2, 3], [0, 1, 1], [4, 5], [1, 0], [2, 0, 5], [0]], ![[7], [1, 7], [2, 7], [3, 7], [3, 3], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 240) : Classified H :=
  classify_of_checks 240 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node240

namespace Node241

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 1], [0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 240) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 241 :=
  generated_of_packed 240 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2421 ⟨![[0], [], [1], [2], [0, 3, 5], [3], [0, 0, 1], [2, 4]], ![[0], [2], [3], [5], [3, 7], [0, 0, 3, 7], [0, 0, 3, 7], [0, 0, 3, 7], [0, 0, 3, 7], [0, 0, 3, 7]]⟩, .edge 2427 ⟨![[], [0, 3, 4], [1], [2], [4, 5], [0], [1], [2, 5]], ![[5], [2], [3], [1, 5], [1, 1], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2420 ⟨![[0], [1], [], [2], [0], [0, 0, 1], [], [2]], ![[0], [1], [3], [1, 1], [0, 1, 0, 1], [0, 1, 0, 5], [0, 1, 0, 5], [0, 1, 0, 5], [0, 1, 0, 5], [0, 1, 0, 5]]⟩, .edge 2425 ⟨![[], [1], [0, 0, 0], [2], [0, 0], [0, 1, 0], [0], [2, 5]], ![[6], [1], [3], [1, 1], [1, 4, 5], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2422 ⟨![[0], [], [1, 1, 1], [2], [0, 3, 5], [3], [1], [2, 4]], ![[0], [6], [3], [5], [3, 7], [0, 0, 3, 7], [0, 0, 3, 7], [0, 0, 3, 7], [0, 0, 3, 7], [0, 0, 3, 7]]⟩, .edge 2429 ⟨![[], [0, 0, 1, 0], [0, 0, 0], [2], [0, 0], [0, 0, 0, 1], [0], [2, 5]], ![[6], [1, 6], [3], [1, 5], [1, 1], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .noncentric 2048, .edge 2424 ⟨![[], [1], [2], [0, 4], [4, 5], [0, 1, 0], [2], [0]], ![[7], [1], [2], [1, 1], [3, 3], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .noncentric 2064, .edge 2428 ⟨![[], [0, 1, 3], [2], [0, 4], [4, 5], [0, 1, 4], [2], [0]], ![[7], [1, 7], [2], [1, 5], [1, 1], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .noncentric 56, .edge 2426 ⟨![[], [1], [2, 0, 4], [0, 4], [4, 5], [0, 1, 0], [0, 2], [0]], ![[7], [1], [2, 7], [1, 1], [3, 3], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2423 ⟨![[0], [], [0, 1, 0, 2], [1, 1, 1], [0, 3, 5], [3], [1, 2], [1]], ![[0], [7], [2, 7], [5], [0, 4, 5], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .noncentric 104] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 241) : Classified H :=
  classify_of_checks 241 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node241

namespace Node242

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 241) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 242 :=
  generated_of_packed 241 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2433 ⟨![[0], [], [1], [2], [0, 4, 5], [], [1], [2]], ![[0], [2], [3], [3, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2440 ⟨![[], [0, 5], [1], [2], [4], [0], [1], [2, 3]], ![[5], [2], [3], [3, 3], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2431 ⟨![[0], [1], [], [2], [0], [1], [], [2, 4, 5]], ![[0], [1], [3], [3, 3], [0, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 2438 ⟨![[], [1], [0, 4], [2], [4], [1, 4, 5], [0], [2, 3]], ![[6], [1], [3], [3, 3], [4], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2435 ⟨![[0], [], [1], [2], [0, 4, 5], [], [1], [2]], ![[0], [2], [3], [3, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2442 ⟨![[], [0, 1, 5], [0, 4], [2], [4], [0, 1], [0], [2, 3]], ![[6], [1, 6], [3], [3, 3], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2430 ⟨![[0], [1], [2], [], [0, 3], [1], [2, 4, 5], [3]], ![[0], [1], [2], [7], [0, 0], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 2437 ⟨![[], [1], [2], [0, 3, 4], [4], [1, 4, 5], [2], [0]], ![[7], [1], [2], [3, 7], [4], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2434 ⟨![[0], [], [2], [1], [0, 4, 5], [], [2], [1]], ![[0], [3], [2], [3, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2441 ⟨![[], [1, 0, 4], [2], [0, 3, 4], [4], [0, 1, 3], [2], [0]], ![[7], [1, 7], [2], [3, 7], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2432 ⟨![[0], [1], [], [2, 4, 5], [0], [1], [], [2]], ![[0], [1], [7], [3, 7], [0, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩, .edge 2439 ⟨![[], [1], [2, 0, 4], [0, 3, 4], [4], [1, 4, 5], [2, 0], [0]], ![[7], [1], [2, 7], [3, 7], [4], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2436 ⟨![[0], [], [2, 1, 3], [1], [0, 4, 5], [], [2, 1, 3], [1]], ![[0], [3], [2, 3], [3, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2443 ⟨![[], [1, 0, 4], [2, 0, 4], [0, 3, 4], [4], [0, 1, 3], [2, 0], [0]], ![[7], [1, 7], [2, 7], [3, 7], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 242) : Classified H :=
  classify_of_checks 242 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node242

namespace Node243

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [3, 3], [0, 0], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 242) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 243 :=
  generated_of_packed 242 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2447 ⟨![[0], [], [1], [2], [0, 4], [4, 5], [1], [2, 5]], ![[0], [2], [3], [3, 3], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .noncentric 2048, .edge 2445 ⟨![[0], [1], [], [2], [0], [1], [], [1, 1, 2]], ![[0], [1], [3], [3, 3], [0, 0], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩, .edge 2452 ⟨![[], [1], [0, 4], [2], [4], [1, 4], [0], [2, 3]], ![[6], [1], [3], [3, 3], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2449 ⟨![[0], [], [1, 1, 1], [2], [0, 4], [1, 1], [1], [2, 5]], ![[0], [6], [3], [3, 3], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2454 ⟨![[], [0, 1], [0, 4], [2], [4], [0, 1], [0], [2, 3]], ![[6], [1, 6], [3], [3, 3], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 2444 ⟨![[0], [1], [2], [], [0, 3], [1, 5], [1, 1, 2], [3]], ![[0], [1], [2], [7], [0, 0], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩, .edge 2451 ⟨![[], [1], [2], [0, 3, 4], [4], [1, 4], [2], [0]], ![[7], [1], [2], [3, 7], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2448 ⟨![[0], [], [2], [1, 4], [0, 4], [4, 5], [2], [1]], ![[0], [7], [2], [3, 7], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .noncentric 2064, .edge 2446 ⟨![[0], [1], [], [1, 1, 2], [0], [1], [], [2]], ![[0], [1], [7], [3, 7], [0, 0], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]⟩, .edge 2453 ⟨![[], [1], [2, 0, 4], [0, 3, 4], [4], [1, 4], [2, 0], [0]], ![[7], [1], [2, 7], [3, 7], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2450 ⟨![[0], [], [1, 2, 3], [1, 4], [0, 4], [4, 5], [1, 2, 2, 2], [1]], ![[0], [7], [2, 7], [3, 7], [0, 0], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5], [0, 0, 5]]⟩, .edge 2455 ⟨![[], [1, 0, 4], [2, 0, 4], [0, 1, 1], [4], [1, 0, 4], [2, 0], [0]], ![[7], [1, 7], [2, 7], [3, 7], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 243) : Classified H :=
  classify_of_checks 243 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node243

namespace Node244

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 1], [0, 0], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 243) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 244 :=
  generated_of_packed 243 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2458 ⟨![[0], [], [1], [2], [0, 3, 5], [3], [1, 4, 5], [2, 4]], ![[0], [2], [3], [5], [0, 0], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .edge 2464 ⟨![[], [0, 0, 0, 3], [1], [2], [4], [0], [0, 0, 1], [2]], ![[5], [2], [3], [1, 5], [4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]⟩, .edge 2456 ⟨![[0], [1], [], [2], [0, 4, 5], [1, 4, 5], [], [2]], ![[0], [1], [3], [1, 1], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .noncentric 36, .edge 2460 ⟨![[0], [], [1, 1, 1], [2], [0, 3, 5], [3], [1], [2, 4]], ![[0], [6], [3], [5], [0, 0], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6]]⟩, .noncentric 100, .noncentric 2048, .edge 2462 ⟨![[], [1], [2], [0, 4], [4], [0, 1, 0], [2, 4, 5], [0]], ![[7], [1], [2], [1, 1], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2459 ⟨![[0], [], [2], [1, 1, 1], [0, 3, 5], [3], [2, 4, 5], [1]], ![[0], [7], [2], [5], [0, 0], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6], [0, 0, 2, 6]]⟩, .noncentric 2064, .edge 2457 ⟨![[0], [1], [], [2], [0, 4, 5], [1, 4, 5], [], [2]], ![[0], [1], [3], [1, 1], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2463 ⟨![[], [1], [0, 2, 5], [0, 4], [4], [0, 1, 0], [0, 2], [0]], ![[7], [1], [2, 7], [1, 1], [4], [1, 5], [1, 5], [1, 5], [1, 5], [1, 5]]⟩, .edge 2461 ⟨![[0], [], [0, 1, 0, 2], [1, 1, 1], [0, 3, 5], [3], [1, 2], [1]], ![[0], [7], [2, 7], [5], [0, 0], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6], [0, 2, 4, 6]]⟩, .edge 2465 ⟨![[], [1, 0, 4], [0, 2, 5], [0, 4], [4], [0, 1, 4], [0, 2], [0]], ![[7], [1, 7], [2, 7], [1, 5], [4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 244) : Classified H :=
  classify_of_checks 244 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node244

namespace Node245

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 2, 1, 2, 2, 2], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 244) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 245 :=
  generated_of_packed 244 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2467 ⟨![[0], [], [1], [2], [0], [], [1, 3], [0, 0, 2]], ![[0], [2], [3], [2, 2, 2, 6], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2474 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 5], [2, 5]], ![[5], [2], [3], [1, 2, 5, 2], [2, 2, 4], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .noncentric 16, .edge 2472 ⟨![[], [1], [0, 4], [2], [0, 0], [1], [0], [2, 5]], ![[6], [1], [3], [1, 2, 1, 2, 4], [2, 4, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2469 ⟨![[0], [], [1, 3], [2], [0], [], [1], [0, 0, 2]], ![[0], [6], [3], [2, 2, 2, 6], [0, 0, 2, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2476 ⟨![[], [0, 0, 1, 0], [0, 4], [2], [0, 0], [1, 0], [0], [2, 5]], ![[6], [1, 6], [3], [1, 2, 5, 6], [2, 4, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 24, .edge 2471 ⟨![[], [1], [2], [0, 4], [4, 5], [1], [2, 5], [0]], ![[7], [1], [2], [1, 2, 1, 6], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2468 ⟨![[0], [], [2], [0, 0, 1], [0], [], [2, 3], [1]], ![[0], [7], [2], [2, 2, 2, 6], [0, 0, 2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2475 ⟨![[], [0, 1], [2], [0, 4], [1, 1], [1, 0, 5], [2, 5], [0]], ![[7], [1, 7], [2], [1, 2, 5, 2], [3, 3], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]⟩, .edge 2466 ⟨![[0], [1], [], [2, 5], [0, 5], [1, 3], [5], [2]], ![[0], [1], [7], [1, 5], [0, 4], [6], [6], [6], [6], [6]]⟩, .edge 2473 ⟨![[], [1], [0, 2, 4], [0, 4], [4, 5], [1], [0, 2], [0]], ![[7], [1], [2, 7], [1, 2, 1, 2, 4], [3, 3], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2470 ⟨![[0], [], [1, 2, 3], [0, 0, 1], [0], [], [1, 2], [1]], ![[0], [7], [2, 7], [2, 2, 2, 6], [0, 0, 2, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2477 ⟨![[], [0, 1], [0, 2, 4], [0, 4], [1, 1], [1, 0, 5], [0, 2], [0]], ![[7], [1, 7], [2, 7], [1, 2, 5, 6], [3, 3], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 245) : Classified H :=
  classify_of_checks 245 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node245

namespace Node246

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 1, 3, 1, 3], [0, 2, 0, 2], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3], [2, 3, 2, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 245) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 246 :=
  generated_of_packed 245 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2479 ⟨![[0], [], [1], [2], [0], [], [0, 0, 1], [0, 0, 2, 3]], ![[0], [2], [3], [0, 0, 3, 7], [0, 2, 0, 2], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 2486 ⟨![[], [0, 0, 0], [1], [2], [0, 0], [0], [1, 5], [2]], ![[5], [2], [3], [1, 3, 1, 3], [2, 4, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2478 ⟨![[0], [1], [], [2], [0, 5], [0, 0, 1], [], [2, 5]], ![[0], [1], [3], [1, 3, 5, 3], [0, 4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2484 ⟨![[], [1], [0, 4], [2], [4, 5], [1], [0], [2]], ![[6], [1], [3], [1, 3, 1, 3, 4], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2481 ⟨![[0], [], [0, 0, 1], [2], [0], [], [1], [0, 0, 2, 3]], ![[0], [6], [3], [0, 0, 3, 7], [0, 2, 0, 6], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2488 ⟨![[], [0, 1], [0, 4], [2], [1, 1], [1, 0, 5], [0], [2]], ![[6], [1, 6], [3], [1, 3, 1, 3], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .noncentric 16, .edge 2483 ⟨![[], [1], [2], [0, 0, 0], [0, 0], [1], [2, 5], [0]], ![[7], [1], [2], [1, 3, 1, 3], [2, 4, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2480 ⟨![[0], [], [2], [1, 1, 1], [0], [], [0, 0, 2], [1]], ![[0], [7], [2], [0, 0, 3, 3], [0, 2, 0, 2], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6], [0, 2, 0, 6]]⟩, .edge 2487 ⟨![[], [0, 1, 3], [2], [0, 0, 0], [0, 0], [1, 0], [2, 5], [0]], ![[7], [1, 7], [2], [1, 3, 1, 7], [2, 4, 6], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 24, .edge 2485 ⟨![[], [1], [0, 0, 0, 2], [0, 0, 0], [0, 0], [1], [0, 2, 5], [0]], ![[7], [1], [2, 7], [1, 3, 1, 3], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩, .edge 2482 ⟨![[0], [], [1, 2, 4], [1, 1, 1], [0], [], [1, 2, 5], [1]], ![[0], [7], [2, 7], [0, 0, 3, 3], [0, 2, 0, 6], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2], [0, 2, 0, 2]]⟩, .edge 2489 ⟨![[], [0, 1, 3], [0, 0, 0, 2], [0, 0, 0], [0, 0], [1, 0], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [1, 3, 1, 7], [2, 2], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 246) : Classified H :=
  classify_of_checks 246 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node246

namespace Node247

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [0, 0, 1, 3, 1, 3], [0, 3, 0, 3], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 246) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 247 :=
  generated_of_packed 246 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2493 ⟨![[0], [], [1], [2], [0, 5], [0, 0], [1], [2, 3]], ![[0], [2], [3], [3, 7], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2500 ⟨![[], [0, 4], [1], [2], [4, 5], [0], [1], [2, 5]], ![[5], [2], [3], [1, 3, 1, 3], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2491 ⟨![[0], [1], [], [2], [0], [1], [], [2, 5]], ![[0], [1], [3], [0, 0, 1, 3, 1, 3], [0, 0, 3, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2498 ⟨![[], [1], [0, 0, 0], [2], [0, 0], [1, 5], [0], [2, 5]], ![[6], [1], [3], [1, 3, 1, 3, 4], [1, 5], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2495 ⟨![[0], [], [0, 0, 1], [2], [0, 5], [0, 0], [1], [2, 3]], ![[0], [6], [3], [3, 7], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2502 ⟨![[], [0, 1, 4], [0, 0, 0], [2], [0, 0], [0, 1], [0], [2, 5]], ![[6], [1, 6], [3], [1, 3, 1, 3], [1, 1, 4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2490 ⟨![[0], [1], [2], [], [0, 5], [1, 3], [2, 5], []], ![[0], [1], [2], [0, 0, 1, 5], [0, 4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2497 ⟨![[], [1], [2], [0, 4], [1, 1], [1, 5], [2], [0]], ![[7], [1], [2], [1, 3, 1, 3], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2494 ⟨![[0], [], [2], [1, 1, 1], [0, 5], [0, 0], [2], [1]], ![[0], [7], [2], [3, 3, 5], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2501 ⟨![[], [1, 0, 4], [2], [0, 4], [4, 5], [1, 0], [2], [0]], ![[7], [1, 7], [2], [1, 3, 1, 3, 4], [3, 3], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2492 ⟨![[0], [1], [], [2, 5], [0], [1], [], [2]], ![[0], [1], [7], [0, 0, 1, 3, 1, 7], [0, 0, 3, 3], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2499 ⟨![[], [1], [0, 2, 4], [0, 4], [1, 1], [1, 5], [0, 2, 5], [0]], ![[7], [1], [2, 7], [1, 3, 1, 3], [1, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2496 ⟨![[0], [], [1, 2, 4], [1, 1, 1], [0, 5], [0, 0], [1, 2, 5], [1]], ![[0], [7], [2, 7], [3, 3, 5], [0, 4], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5], [0, 4, 5]]⟩, .edge 2503 ⟨![[], [1, 0, 4], [0, 2, 4], [0, 4], [4, 5], [1, 0], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [1, 3, 1, 3, 4], [3, 3], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 247) : Classified H :=
  classify_of_checks 247 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node247

namespace Node248

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 1], [0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 247) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 248 :=
  generated_of_packed 247 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2507 ⟨![[0], [], [1], [2], [0, 5], [3], [1, 5], [0, 0, 2]], ![[0], [2], [3], [5], [0, 4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2514 ⟨![[], [0, 4], [1], [2], [4, 5], [0], [1], [2, 5]], ![[5], [2], [3], [1, 5], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2505 ⟨![[0], [1], [], [2], [0], [1, 5], [], [2]], ![[0], [1], [3], [1, 1], [0, 3, 0, 3], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5]]⟩, .edge 2512 ⟨![[], [1], [0, 0, 0], [2], [0, 0], [1, 5], [0], [2, 5]], ![[6], [1], [3], [1, 1], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2509 ⟨![[0], [], [1, 1, 1], [2], [0, 5], [3], [1], [0, 0, 2]], ![[0], [6], [3], [5], [0, 4], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 2516 ⟨![[], [0, 0, 0, 1], [0, 0, 0], [2], [0, 0], [0, 1, 5], [0], [2, 5]], ![[6], [1, 6], [3], [1, 5], [3, 4, 7], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2504 ⟨![[0], [1], [2], [], [0, 5], [0, 0, 1], [2], []], ![[0], [1], [2], [1, 1], [0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]⟩, .edge 2511 ⟨![[], [1], [2], [0, 4], [4, 5], [1, 5], [2], [0]], ![[7], [1], [2], [1, 1], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 2508 ⟨![[0], [], [2], [1, 1, 1], [0, 5], [3], [2, 5], [1]], ![[0], [7], [2], [5], [0, 4], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .edge 2515 ⟨![[], [0, 1, 5], [2], [0, 4], [4, 5], [1, 0], [2], [0]], ![[7], [1, 7], [2], [1, 5], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 2506 ⟨![[0], [1], [], [2], [0], [1, 5], [], [2]], ![[0], [1], [3], [1, 1], [0, 3, 0, 3], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5], [1, 1, 1, 5]]⟩, .edge 2513 ⟨![[], [1], [2, 0, 4], [0, 4], [4, 5], [1, 5], [0, 2], [0]], ![[7], [1], [2, 7], [1, 1], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩, .edge 2510 ⟨![[0], [], [1, 1, 2, 1], [1, 1, 1], [0, 5], [3], [1, 2], [1]], ![[0], [7], [2, 7], [5], [0, 4], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5], [2, 2, 5]]⟩, .edge 2517 ⟨![[], [0, 1, 5], [2, 0, 4], [0, 4], [4, 5], [1, 0], [0, 2], [0]], ![[7], [1, 7], [2, 7], [1, 5], [3, 3], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem separation_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ) := by
  have h : ∀ (σ : Fin 4 → Bool), (branches σ).needsSeparation = false := by decide +kernel
  intro σ _
  exact (branches σ).separation_of_false (h σ) gen σ (pivot σ)

theorem classify (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 248) : Classified H :=
  classify_of_checks 248 gen generated pivot branches pivot_checked equations_checked
    separation_checked H hH

end Node248

namespace Node249

def gen : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]

def generationWords : ClosureWords 4 10 :=
  ⟨![[0], [1], [2], [3]],
   ![[0], [1], [2], [3], [1, 3, 1, 3], [0, 0], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]⟩

theorem generation_checked : PackedEquality generationWords gen
    (SmallEvenDescentEdges.Certificates.fastNodeGenerator 248) := by decide +kernel

theorem generated : Subgroup.closure (Set.range gen) = smallEvenDescentNode 249 :=
  generated_of_packed 248 gen generationWords generation_checked

def pivot (σ : Fin 4 → Bool) : Fin 4 :=
  ![0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

def branches (σ : Fin 4 → Bool) : BranchData 4 :=
  ![.core, .core, .edge 2521 ⟨![[0], [], [1], [2], [0, 4, 5], [], [1], [2, 3]], ![[0], [2], [3], [3, 7], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2527 ⟨![[], [0, 5], [1], [2], [4], [0], [1], [2, 5]], ![[5], [2], [3], [1, 3, 1, 3], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2519 ⟨![[0], [1], [], [2], [0], [1], [], [2, 5]], ![[0], [1], [3], [1, 3, 1, 3], [0, 0], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2525 ⟨![[], [1], [0, 4], [2], [4], [1, 4, 5], [0], [2, 5]], ![[6], [1], [3], [1, 3, 1, 3], [4], [3, 7], [3, 7], [3, 7], [3, 7], [3, 7]]⟩, .edge 2523 ⟨![[0], [], [1], [2], [0, 4, 5], [], [1], [2, 3]], ![[0], [2], [3], [3, 7], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2529 ⟨![[], [0, 1, 5], [0, 4], [2], [4], [0, 1], [0], [2, 5]], ![[6], [1, 6], [3], [1, 3, 1, 3], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2518 ⟨![[0], [1], [2], [], [0, 5], [1, 3], [2, 5], []], ![[0], [1], [2], [1, 5], [0, 0], [2, 6], [2, 6], [2, 6], [2, 6], [2, 6]]⟩, .noncentric 8, .edge 2522 ⟨![[0], [], [2], [1, 3], [0, 4, 5], [], [2], [1]], ![[0], [7], [2], [3, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2528 ⟨![[], [0, 0, 1, 0], [2], [0, 0, 0], [4], [0, 1, 3], [2], [0]], ![[7], [1, 7], [2], [1, 3, 1, 3], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩, .edge 2520 ⟨![[0], [1], [], [2, 5], [0], [1], [], [2]], ![[0], [1], [7], [1, 3, 1, 7], [0, 0], [3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]⟩, .edge 2526 ⟨![[], [1], [0, 0, 0, 2], [0, 0, 0], [4], [0, 0, 1], [0, 2, 5], [0]], ![[7], [1], [2, 7], [1, 3, 1, 3], [4], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5], [1, 4, 5]]⟩, .edge 2524 ⟨![[0], [], [1, 2, 5], [1, 3], [0, 4, 5], [], [1, 2, 5], [1]], ![[0], [7], [2, 7], [3, 3], [0, 0], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]⟩, .edge 2530 ⟨![[], [0, 0, 1, 0], [0, 0, 0, 2], [0, 0, 0], [4], [0, 1, 3], [0, 2, 5], [0]], ![[7], [1, 7], [2, 7], [1, 3, 1, 3], [4], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]⟩] ⟨signatureIndex σ % 16, Nat.mod_lt _ (by decide)⟩

theorem pivot_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → σ (pivot σ) = true := by decide +kernel

theorem equations_checked : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Equations gen σ (pivot σ) := by decide +kernel

theorem classify (hn : ∀ (σ : Fin 4 → Bool),
    (∃ k, σ k = true) → (branches σ).Separation gen σ (pivot σ))
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode 249) : Classified H :=
  classify_of_checks 249 gen generated pivot branches pivot_checked equations_checked hn H hH

end Node249

end ReeTwo.SylowModel.SmallEvenMaximalLower
