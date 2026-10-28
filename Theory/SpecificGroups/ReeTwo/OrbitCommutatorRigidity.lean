module

public import Theory.SpecificGroups.ReeTwo.OrbitFrameAlgebra

/-!
# Rigidity of the binary orbit commutator coordinates

The five-action and the seed-normalized doubling symmetry have columns
`[2,4,8,15]` and `[1,4,15,2]` in the four root displacements. Two compatibility
equations leave only the zero commutator or the six Ree commutators. This
module separates the finite calculation from the group identities needed to
apply it; `OrbitCommutatorTransport` records those identities explicitly.

The calculation follows the five-orbit normalization in Parrott (1972),
pp.672–674, with the root convention of Shinoda (1975), pp.81–82.
-/

@[expose] public section
namespace ReeTwo

/-- Binary coordinates in the four root displacements. -/
abbrev OrbitBits := Fin 4 → Fin 2

/-- The five-action, whose columns have binary masks 2, 4, 8, 15. -/
def orbitFive (v : OrbitBits) : OrbitBits :=
  ![v 3, v 0 + v 3, v 1 + v 3, v 2 + v 3]

/-- The seed-normalized symmetry, whose columns have masks 1, 4, 15, 2. -/
def orbitSymmetry (v : OrbitBits) : OrbitBits :=
  ![v 0 + v 2, v 2 + v 3, v 1 + v 2, v 2]

/-- The finite rigidity certificate is checked by the kernel. -/
theorem orbitBits_rigidity : ∀ v : OrbitBits,
    orbitFive (orbitFive (orbitFive (orbitFive (orbitSymmetry v)))) =
      v + orbitFive v + orbitFive (orbitSymmetry v) →
    orbitSymmetry (orbitSymmetry v) =
      v + orbitSymmetry v + orbitFive (orbitFive (orbitFive (orbitSymmetry v))) →
    v = 0 ∨ v = ![1, 1, 0, 1] := by decide +kernel

section Words
variable {C : Type*} [CommGroup C] (d : Fin 4 → C)
    (hd : ∀ i, d i * d i = 1)

private theorem bit_add (x : C) (hx : x*x=1) (e f : Fin 2) :
    x ^ (e+f).val = x ^ e.val * x ^ f.val := by
  fin_cases e <;> fin_cases f <;> simp [hx]

include hd

/-- Binary words in commuting involutions convert addition to multiplication. -/
theorem binaryWord4_add (e f : OrbitBits) : binaryWord4 d (e+f) =
    binaryWord4 d e * binaryWord4 d f := by
  simp only [binaryWord4, Pi.add_apply, bit_add _ (hd _)]
  ac_rfl

set_option linter.unusedSimpArgs false in
/-- Checking the four columns suffices to transport every binary word. -/
theorem binaryWord4_map_five (F : C →* C)
    (hf : ∀ i, F (d i) = binaryWord4 d (orbitFive (Pi.single i 1)))
    (e : OrbitBits) : F (binaryWord4 d e) = binaryWord4 d (orbitFive e) := by
  have cancel (i : Fin 4) (x : C) : d i * (d i * x) = x := by
    rw [← mul_assoc, hd, one_mul]
  simp only [binaryWord4, map_mul, map_pow, hf]
  generalize h0 : e 0 = e0
  generalize h1 : e 1 = e1
  generalize h2 : e 2 = e2
  generalize h3 : e 3 = e3
  fin_cases e0 <;> fin_cases e1 <;> fin_cases e2 <;> fin_cases e3 <;>
    simp [orbitFive, h0, h1, h2, h3, mul_assoc, mul_left_comm, mul_comm, hd, cancel]

set_option linter.unusedSimpArgs false in
/-- The analogous word transport for the normalized doubling symmetry. -/
theorem binaryWord4_map_symmetry (F : C →* C)
    (hf : ∀ i, F (d i) = binaryWord4 d (orbitSymmetry (Pi.single i 1)))
    (e : OrbitBits) : F (binaryWord4 d e) = binaryWord4 d (orbitSymmetry e) := by
  have cancel (i : Fin 4) (x : C) : d i * (d i * x) = x := by
    rw [← mul_assoc, hd, one_mul]
  simp only [binaryWord4, map_mul, map_pow, hf]
  generalize h0 : e 0 = e0
  generalize h1 : e 1 = e1
  generalize h2 : e 2 = e2
  generalize h3 : e 3 = e3
  fin_cases e0 <;> fin_cases e1 <;> fin_cases e2 <;> fin_cases e3 <;>
    simp [orbitSymmetry, h0, h1, h2, h3, mul_assoc, mul_left_comm, mul_comm, hd, cancel]
end Words

variable {H : Type*} [Group H]

/-- Vanishing of the right commutator is exactly commutation. -/
theorem rightComm_eq_one_iff_commute (x y : H) : rightComm x y = 1 ↔ Commute x y := by
  rw [show rightComm x y = (y*x)⁻¹*(x*y) by simp [rightComm, mul_assoc],
    inv_mul_eq_one]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- The group identities that make the finite rigidity certificate applicable.
The endomorphisms act on the ambient group; no model or commutator table is
assumed. In an intrinsic extension they come from the five-action and the
seed-normalized symmetry on the central quotient. -/
structure OrbitCommutatorTransport (u : Fin 4 → H) (t : H) where
  five : H →* H
  symmetry : H →* H
  word_add : ∀ e f : OrbitBits,
    binaryWord4 (fun i => rightComm (u i) t) (e+f) =
      binaryWord4 (fun i => rightComm (u i) t) e *
      binaryWord4 (fun i => rightComm (u i) t) f
  map_five : ∀ e : OrbitBits,
    five (binaryWord4 (fun i => rightComm (u i) t) e) =
      binaryWord4 (fun i => rightComm (u i) t) (orbitFive e)
  map_symmetry : ∀ e : OrbitBits,
    symmetry (binaryWord4 (fun i => rightComm (u i) t) e) =
      binaryWord4 (fun i => rightComm (u i) t) (orbitSymmetry e)
  comm02 : rightComm (u 0) (u 2) = symmetry (rightComm (u 0) (u 1))
  comm03 : rightComm (u 0) (u 3) = five (five (five (symmetry (rightComm (u 0) (u 1)))))
  comm12 : rightComm (u 1) (u 2) = five (rightComm (u 0) (u 1))
  comm13 : rightComm (u 1) (u 3) = five (symmetry (rightComm (u 0) (u 1)))
  comm23 : rightComm (u 2) (u 3) = five (five (rightComm (u 0) (u 1)))
  five_constraint : five (five (five (five (symmetry (rightComm (u 0) (u 1)))))) =
    rightComm (u 0) (u 1) * five (rightComm (u 0) (u 1)) *
      five (symmetry (rightComm (u 0) (u 1)))
  symmetry_constraint : symmetry (symmetry (rightComm (u 0) (u 1))) =
    rightComm (u 0) (u 1) * symmetry (rightComm (u 0) (u 1)) *
      five (five (five (symmetry (rightComm (u 0) (u 1)))))

/-- Injective tail coordinates transfer the two group constraints to the finite
certificate. Its zero branch consists of four commuting orbit generators. -/
theorem OrbitCommutatorTransport.coordinates_or_commute
    {u : Fin 4 → H} {t : H} (h : OrbitCommutatorTransport u t)
    (hinj : Function.Injective (binaryWord4 (fun i => rightComm (u i) t)))
    (hspan : ∃ e : OrbitBits, rightComm (u 0) (u 1) =
      binaryWord4 (fun i => rightComm (u i) t) e) :
    (∀ i j, Commute (u i) (u j)) ∨ OrbitCommutatorCoordinates u t := by
  obtain ⟨v, hv⟩ := hspan
  have hfive := h.five_constraint
  have hsym := h.symmetry_constraint
  rw [hv] at hfive hsym
  simp only [h.map_five, h.map_symmetry, ← h.word_add] at hfive hsym
  rcases orbitBits_rigidity v (hinj hfive) (hinj hsym) with hz | hn
  · left
    have h01 : rightComm (u 0) (u 1) = 1 := by simpa [hz, binaryWord4] using hv
    have h02 : rightComm (u 0) (u 2) = 1 := by simp [h.comm02, h01]
    have h03 : rightComm (u 0) (u 3) = 1 := by simp [h.comm03, h01]
    have h12 : rightComm (u 1) (u 2) = 1 := by simp [h.comm12, h01]
    have h13 : rightComm (u 1) (u 3) = 1 := by simp [h.comm13, h01]
    have h23 : rightComm (u 2) (u 3) = 1 := by simp [h.comm23, h01]
    rw [rightComm_eq_one_iff_commute] at h01 h02 h03 h12 h13 h23
    intro i j
    fin_cases i <;> fin_cases j <;>
      first | exact Commute.refl _ | assumption | exact h01.symm | exact h02.symm |
        exact h03.symm | exact h12.symm | exact h13.symm | exact h23.symm
  · right
    subst v
    constructor
    · simpa [binaryWord4] using hv
    · rw [h.comm02, hv, h.map_symmetry]
      simp [orbitSymmetry, binaryWord4]
    · rw [h.comm03, hv, h.map_symmetry, h.map_five, h.map_five, h.map_five]
      simp [orbitSymmetry, orbitFive, binaryWord4]
    · rw [h.comm12, hv, h.map_five]
      simp [orbitFive, binaryWord4]
    · rw [h.comm13, hv, h.map_symmetry, h.map_five]
      simp [orbitSymmetry, orbitFive, binaryWord4]
    · rw [h.comm23, hv, h.map_five, h.map_five]
      simp [orbitFive, binaryWord4]
end ReeTwo
