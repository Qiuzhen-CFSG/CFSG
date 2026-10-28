module

public import Theory.AlgebraicGroup.RootSystems.F4RootPairing
public import Mathlib.Tactic
/-!
# Coordinates for the Ree end-root trace calculation

Enumerate the 48 actual Euclidean F₄ roots by their doubled integral coordinates.
Membership and exhaustiveness follow from the pair, unit, and half-sign root
families; an integral encoding proves injectivity. This gives the basis change
used to certify the end-root Geck matrices.

Source: the standard F₄ realization underlying GLS3, §§1.8 and 1.12, and the
actual `typeF4RootPairing` in `F4RootPairing.lean`.
-/

@[expose] public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.Cartan.FieldSeparation.TraceValues
set_option maxRecDepth 4000

def coord (r : Fin 48) : Fin 4 → ℤ :=
  match r.val with
  | 0 => ![-2, 0, 0, 0]
  | 1 => ![2, 0, 0, 0]
  | 2 => ![0, -2, 0, 0]
  | 3 => ![0, 2, 0, 0]
  | 4 => ![0, 0, -2, 0]
  | 5 => ![0, 0, 2, 0]
  | 6 => ![0, 0, 0, -2]
  | 7 => ![0, 0, 0, 2]
  | 8 => ![-2, -2, 0, 0]
  | 9 => ![-2, 2, 0, 0]
  | 10 => ![2, -2, 0, 0]
  | 11 => ![2, 2, 0, 0]
  | 12 => ![-2, 0, -2, 0]
  | 13 => ![-2, 0, 2, 0]
  | 14 => ![2, 0, -2, 0]
  | 15 => ![2, 0, 2, 0]
  | 16 => ![-2, 0, 0, -2]
  | 17 => ![-2, 0, 0, 2]
  | 18 => ![2, 0, 0, -2]
  | 19 => ![2, 0, 0, 2]
  | 20 => ![0, -2, -2, 0]
  | 21 => ![0, -2, 2, 0]
  | 22 => ![0, 2, -2, 0]
  | 23 => ![0, 2, 2, 0]
  | 24 => ![0, -2, 0, -2]
  | 25 => ![0, -2, 0, 2]
  | 26 => ![0, 2, 0, -2]
  | 27 => ![0, 2, 0, 2]
  | 28 => ![0, 0, -2, -2]
  | 29 => ![0, 0, -2, 2]
  | 30 => ![0, 0, 2, -2]
  | 31 => ![0, 0, 2, 2]
  | 32 => ![-1, -1, -1, -1]
  | 33 => ![-1, -1, -1, 1]
  | 34 => ![-1, -1, 1, -1]
  | 35 => ![-1, -1, 1, 1]
  | 36 => ![-1, 1, -1, -1]
  | 37 => ![-1, 1, -1, 1]
  | 38 => ![-1, 1, 1, -1]
  | 39 => ![-1, 1, 1, 1]
  | 40 => ![1, -1, -1, -1]
  | 41 => ![1, -1, -1, 1]
  | 42 => ![1, -1, 1, -1]
  | 43 => ![1, -1, 1, 1]
  | 44 => ![1, 1, -1, -1]
  | 45 => ![1, 1, -1, 1]
  | 46 => ![1, 1, 1, -1]
  | _ => ![1, 1, 1, 1]

noncomputable def realCoord (r : Fin 48) : Vec 4 := fun k => (coord r k : ℝ) / 2
set_option maxHeartbeats 800000 in
lemma realCoord_mem (r : Fin 48) : realCoord r ∈ typeF4Roots := by
  fin_cases r
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inr; exact ⟨0, Or.inr (by ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff])⟩
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inr; exact ⟨0, Or.inl (by ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff])⟩
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inr; exact ⟨1, Or.inr (by ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff])⟩
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inr; exact ⟨1, Or.inl (by ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff])⟩
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inr; exact ⟨2, Or.inr (by ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff])⟩
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inr; exact ⟨2, Or.inl (by ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff])⟩
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inr; exact ⟨3, Or.inr (by ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff])⟩
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inr; exact ⟨3, Or.inl (by ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff])⟩
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨0, 1, by decide, -1, -1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨0, 1, by decide, -1, 1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨0, 1, by decide, 1, -1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨0, 1, by decide, 1, 1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨0, 2, by decide, -1, -1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨0, 2, by decide, -1, 1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨0, 2, by decide, 1, -1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨0, 2, by decide, 1, 1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨0, 3, by decide, -1, -1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨0, 3, by decide, -1, 1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨0, 3, by decide, 1, -1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨0, 3, by decide, 1, 1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨1, 2, by decide, -1, -1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨1, 2, by decide, -1, 1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨1, 2, by decide, 1, -1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨1, 2, by decide, 1, 1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨1, 3, by decide, -1, -1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨1, 3, by decide, -1, 1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨1, 3, by decide, 1, -1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨1, 3, by decide, 1, 1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨2, 3, by decide, -1, -1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨2, 3, by decide, -1, 1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨2, 3, by decide, 1, -1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inl; apply Or.inl; refine ⟨2, 3, by decide, 1, 1, by norm_num, by norm_num, ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![false, false, false, false], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![false, false, false, true], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![false, false, true, false], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![false, false, true, true], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![false, true, false, false], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![false, true, false, true], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![false, true, true, false], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![false, true, true, true], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![true, false, false, false], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![true, false, false, true], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![true, false, true, false], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![true, false, true, true], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![true, true, false, false], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![true, true, false, true], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![true, true, true, false], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
  · change _ ∈ (pairRoots 4 ∪ signedUnitRoots 4 ∪ Set.range halfSignVector)
    apply Or.inr; refine ⟨![true, true, true, true], ?_⟩
    ext k; fin_cases k <;> norm_num [realCoord, coord, halfSignVector]
noncomputable def root (r : Fin 48) : typeF4Roots := ⟨realCoord r, realCoord_mem r⟩

def encode (c : Fin 4 → ℤ) : ℤ :=
  ((c 0 * 5 + c 1) * 5 + c 2) * 5 + c 3

def decode : ℤ → Fin 48
  | -250 => 0
  | 250 => 1
  | -50 => 2
  | 50 => 3
  | -10 => 4
  | 10 => 5
  | -2 => 6
  | 2 => 7
  | -300 => 8
  | -200 => 9
  | 200 => 10
  | 300 => 11
  | -260 => 12
  | -240 => 13
  | 240 => 14
  | 260 => 15
  | -252 => 16
  | -248 => 17
  | 248 => 18
  | 252 => 19
  | -60 => 20
  | -40 => 21
  | 40 => 22
  | 60 => 23
  | -52 => 24
  | -48 => 25
  | 48 => 26
  | 52 => 27
  | -12 => 28
  | -8 => 29
  | 8 => 30
  | 12 => 31
  | -156 => 32
  | -154 => 33
  | -146 => 34
  | -144 => 35
  | -106 => 36
  | -104 => 37
  | -96 => 38
  | -94 => 39
  | 94 => 40
  | 96 => 41
  | 104 => 42
  | 106 => 43
  | 144 => 44
  | 146 => 45
  | 154 => 46
  | 156 => 47
  | _ => 0

lemma decode_encode (r : Fin 48) : decode (encode (coord r)) = r := by
  fin_cases r <;> rfl

lemma root_injective : Function.Injective root := by
  intro r s h
  have hc : coord r = coord s := by
    funext k
    have he := congrArg (fun r : typeF4Roots => r.val k) h
    change (coord r k : ℝ) / 2 = (coord s k : ℝ) / 2 at he
    have he' : (coord r k : ℝ) = (coord s k : ℝ) := by linarith
    exact_mod_cast he'
  simpa only [decode_encode] using congrArg (fun c => decode (encode c)) hc

set_option maxHeartbeats 800000 in
private lemma pair_in_range (i j : Fin 4) (hij : i ≠ j) (a b : ℝ)
    (ha : a ∈ ({-1, 1} : Set ℝ)) (hb : b ∈ ({-1, 1} : Set ℝ)) :
    ∃ n, realCoord n = a • basisVector i + b • basisVector j := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  all_goals fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · refine ⟨8, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨12, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨16, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨8, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · exact (hij rfl).elim
  · refine ⟨20, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨24, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨12, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨20, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · exact (hij rfl).elim
  · refine ⟨28, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨16, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨24, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨28, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · exact (hij rfl).elim
  · exact (hij rfl).elim
  · refine ⟨9, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨13, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨17, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨10, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · exact (hij rfl).elim
  · refine ⟨21, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨25, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨14, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨22, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · exact (hij rfl).elim
  · refine ⟨29, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨18, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨26, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨30, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · exact (hij rfl).elim
  · exact (hij rfl).elim
  · refine ⟨10, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨14, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨18, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨9, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · exact (hij rfl).elim
  · refine ⟨22, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨26, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨13, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨21, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · exact (hij rfl).elim
  · refine ⟨30, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨17, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨25, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨29, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · exact (hij rfl).elim
  · exact (hij rfl).elim
  · refine ⟨11, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨15, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨19, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨11, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · exact (hij rfl).elim
  · refine ⟨23, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨27, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨15, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨23, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · exact (hij rfl).elim
  · refine ⟨31, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨19, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨27, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨31, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · exact (hij rfl).elim

set_option maxHeartbeats 800000 in
private lemma unit_in_range (v : Vec 4) (i : Fin 4)
    (h : v = basisVector i ∨ v = -basisVector i) :
    ∃ n, realCoord n = v := by
  rcases h with rfl | rfl
  all_goals fin_cases i
  · refine ⟨1, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨3, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨5, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨7, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨0, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨2, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨4, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]
  · refine ⟨6, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, basisVector, Pi.single_apply, Fin.ext_iff]

set_option maxHeartbeats 800000 in
private lemma half_in_range (ε : Fin 4 → Bool) :
    ∃ n, realCoord n = halfSignVector ε := by
  cases h0 : ε 0 <;> cases h1 : ε 1 <;> cases h2 : ε 2 <;> cases h3 : ε 3
  · refine ⟨32, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3
  · refine ⟨33, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3
  · refine ⟨34, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3
  · refine ⟨35, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3
  · refine ⟨36, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3
  · refine ⟨37, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3
  · refine ⟨38, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3
  · refine ⟨39, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3
  · refine ⟨40, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3
  · refine ⟨41, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3
  · refine ⟨42, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3
  · refine ⟨43, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3
  · refine ⟨44, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3
  · refine ⟨45, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3
  · refine ⟨46, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3
  · refine ⟨47, ?_⟩; ext k; fin_cases k <;> norm_num [root, realCoord, coord, halfSignVector, h0, h1, h2, h3] <;> first | exact h0 | exact h1 | exact h2 | exact h3

lemma root_surjective : Function.Surjective root := by
  intro r
  suffices h : ∃ n, realCoord n = r.val by
    obtain ⟨n, hn⟩ := h
    exact ⟨n, Subtype.ext hn⟩
  rcases r with ⟨v, (hp | hu) | hh⟩
  · obtain ⟨i, j, hij, a, b, ha, hb, rfl⟩ := hp
    exact pair_in_range i j hij a b ha hb
  · obtain ⟨i, hi⟩ := hu
    exact unit_in_range v i hi
  · obtain ⟨ε, rfl⟩ := hh
    exact half_in_range ε

noncomputable def rootEquiv : Fin 48 ≃ typeF4Roots :=
  Equiv.ofBijective root ⟨root_injective, root_surjective⟩
end ReeF4.Cartan.FieldSeparation.TraceValues
