module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeLongCoordinates

/-!
# Normal words for the long rank-three parity carriers

Each finite parameter tuple is reconstructed as an ordered binary word in the
original defining generators. The inverse exponent polynomials are checked in
the kernel using collected multiplication. Thus the proposed carrier lies in
the original subgroup, without relying on an order computation.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified root generators
in `SmallParityThreeGenerators` and operations in `CollectedOperations`.
-/

@[expose] public section

namespace ReeTwo.SylowModel.SmallParityLong
set_option maxRecDepth 32768
private def wordBits (c : Fin 3) (p : Parameters c) : Fin 9 → ZMod 2 :=
  let t₀ : ZMod 2 := p.1.toAdd.val
  let t₁ : ZMod 2 := (p.1.toAdd.val / 2 : ℕ)
  let b3 := bit c p 0; let b4 := bit c p 1; let b7 := bit c p 2
  let b8 := bit c p 3; let b9 := bit c p 4
  let b5 := bit c p 5; let b6 := bit c p (if c = 0 then 6 else 5)
  (![![t₀ + t₁ + t₀*t₁ + b3,
t₁ + t₀*t₁ + b3,
t₀ + t₀*t₁ + b3 + t₀*b3,
b3 + t₀*b3 + b4 + b5,
t₁ + t₀*t₁ + t₀*b3 + t₁*b3 + t₀*t₁*b3 + b5,
t₁ + t₀*t₁ + b3 + t₀*b3 + b4 + b5 + t₀*b5 + b6,
b3 + t₁*b3 + b7 + b5 + t₁*b5 + b6 + t₀*b6,
t₀ + t₁ + b3 + t₀*t₁*b3 + t₀*b7 + b8 + t₀*b5 + t₁*b5 + t₀*t₁*b5 + t₁*b6,
b3 + t₀*b3 + t₁*b3 + t₁*b4 + t₀*t₁*b4 + t₀*b3*b4 + t₁*b3*b4 + t₀*t₁*b3*b4 + b7 + b9 + b6],
![t₀ + t₁ + t₀*t₁ + b3,
t₁ + t₀*t₁ + b3,
t₀ + t₀*t₁ + b3 + t₀*b3,
b3 + t₀*b3 + t₀*b4 + b6,
t₁*b3 + t₀*t₁*b3 + b4,
b3 + t₀*t₁*b3 + b4 + t₀*b4 + t₁*b4 + b7 + t₀*b6,
t₀ + t₀*t₁ + t₀*b3 + b4 + t₀*t₁*b4 + b7 + t₀*b7 + b8 + t₀*b6 + t₁*b6,
t₀ + t₀*t₁ + b3 + t₀*b3 + t₁*b3 + t₀*t₁*b3 + t₀*b3*b4 + t₁*b3*b4 + t₀*t₁*b3*b4 + b7 + t₀*b7 + b8 + b9 + t₁*b6,
0],
![t₀ + t₁ + t₀*t₁ + b3,
t₁ + t₀*t₁ + b3,
t₀ + t₀*t₁ + b3 + t₀*b3,
b3 + t₀*b3 + t₀*t₁*b3 + b4 + t₁*b4 + b7,
t₁*b3 + t₀*t₁*b3 + b4,
t₀ + t₁ + t₀*b3 + t₁*b3 + t₀*b4 + t₁*b4 + t₀*b7 + b8,
t₀ + t₁ + b3 + t₀*b3 + t₁*b3 + t₀*t₁*b4 + t₀*b3*b4 + t₁*b3*b4 + t₀*t₁*b3*b4 + b7 + t₀*b7 + b8 + b9,
0,
0]] : Fin 3 → Fin 9 → ZMod 2) c

private def generator (c : Fin 3) (j : Fin 9) : SylowModel :=
  (![![⟨⟨1,0,0,0,0,0,0,0,0,0⟩, Multiplicative.ofAdd 3⟩,
⟨⟨1,0,0,1,1,1,1,0,0,1⟩, Multiplicative.ofAdd 3⟩,
⟨⟨0,1,0,1,1,0,1,1,1,0⟩, Multiplicative.ofAdd 2⟩,
⟨⟨0,0,0,0,1,0,1,1,0,0⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,1,1,0,1,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,1,1,0,0⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,1,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,1,0⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,0,1⟩, Multiplicative.ofAdd 0⟩],
![⟨⟨1,0,0,0,0,0,0,0,0,0⟩, Multiplicative.ofAdd 3⟩,
⟨⟨1,0,0,1,0,1,0,0,1,1⟩, Multiplicative.ofAdd 3⟩,
⟨⟨0,1,0,1,1,0,1,1,1,0⟩, Multiplicative.ofAdd 2⟩,
⟨⟨0,0,0,0,0,0,1,0,0,0⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,1,1,0,1,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,1,1,0⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,1,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,0,1⟩, Multiplicative.ofAdd 0⟩],
![⟨⟨1,0,0,0,0,0,0,0,0,0⟩, Multiplicative.ofAdd 3⟩,
⟨⟨1,0,0,1,0,1,1,1,1,0⟩, Multiplicative.ofAdd 3⟩,
⟨⟨0,1,0,1,1,0,1,1,1,0⟩, Multiplicative.ofAdd 2⟩,
⟨⟨0,0,0,0,0,0,0,1,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,1,1,0,1,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,1,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,0,1⟩, Multiplicative.ofAdd 0⟩]] : Fin 3 → Fin 9 → SylowModel) c j

set_option maxHeartbeats 8000000 in
private theorem generator_eq : ∀ (c : Fin 3) (j : Fin 9),
    generator c j = smallParityThreeGenerator (index c) j := by decide +kernel

private def collectedWord (c : Fin 3) (v : Fin 9 → ZMod 2) : SylowModel :=
  (((List.finRange 9).map fun j =>
    collectedPow (generator c j) (v j).val)).foldl
      collectedMul 1

private theorem collectedWord_mem (c : Fin 3) (v : Fin 9 → ZMod 2) :
    collectedWord c v ∈ Candidate c := by
  unfold collectedWord
  have hlist : ∀ a ∈ (List.finRange 9).map (fun j =>
      collectedPow (generator c j) (v j).val),
      a ∈ Candidate c := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    rw [collectedPow_eq, generator_eq]
    exact Subgroup.pow_mem _ (smallParityThreeGenerator_mem _ _) _
  generalize (List.finRange 9).map _ = l at hlist ⊢
  have hfold : ∀ a ∈ Candidate c, l.foldl collectedMul a ∈ Candidate c := by
    induction l with
    | nil => intro a ha; exact ha
    | cons x l ih =>
      intro a ha
      apply ih (fun y hy => hlist y (List.mem_cons_of_mem _ hy))
      rw [collectedMul_eq]
      exact Subgroup.mul_mem _ ha (hlist x (List.mem_cons_self))
  exact hfold 1 (Subgroup.one_mem _)

set_option maxHeartbeats 8000000 in
private theorem word_valid : ∀ (c : Fin 3) (p : Parameters c),
    collectedWord c (wordBits c p) = element c p := by decide +kernel

theorem element_mem (c : Fin 3) (p : Parameters c) : element c p ∈ Candidate c := by
  rw [← word_valid]
  exact collectedWord_mem c _


end ReeTwo.SylowModel.SmallParityLong
