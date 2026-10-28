/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/SupportSigns.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.Parity
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechEvenProfiles

/-!
Signed support vectors and parity-constrained binary sign assignments.
Support recovery gives injectivity, while summing signs gives norm, residue, and parity formulas.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

/-- Signs of prescribed parity, indexed by a finite type. -/
def ParitySigns (α : Type*) [Fintype α] (b : Bit) := {s : α → Bit // ∑ i, s i = b}

def paritySignsFinEquiv (n : ℕ) (b : Bit) : (Fin n → Bit) ≃ ParitySigns (Fin (n+1)) b where
  toFun r := ⟨Fin.cons (b - ∑ i, r i) r, by simp [Fin.sum_univ_succ]⟩
  invFun r := fun i => r.val i.succ
  left_inv r := rfl
  right_inv r := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    have h := r.prop
    rw [Fin.sum_univ_succ] at h
    change b - ∑ i : Fin n, r.val i.succ = r.val 0
    exact sub_eq_iff_eq_add.mpr h.symm

def paritySignsCongr {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (b : Bit) :
    ParitySigns α b ≃ ParitySigns β b where
  toFun r := ⟨fun i => r.val (e.symm i), by rw [Equiv.sum_comp]; exact r.prop⟩
  invFun r := ⟨fun i => r.val (e i), by rw [Equiv.sum_comp]; exact r.prop⟩
  left_inv r := by apply Subtype.ext; funext i; simp
  right_inv r := by apply Subtype.ext; funext i; simp

theorem paritySigns_card (α : Type*) [Fintype α] (b : Bit) (h : 0 < Fintype.card α) :
    Nat.card (ParitySigns α b) = 2 ^ (Fintype.card α - 1) := by
  have hc : Fintype.card α = (Fintype.card α - 1) + 1 := by omega
  let e := Fintype.equivFinOfCardEq hc
  rw [Nat.card_congr (paritySignsCongr e b),
    ← Nat.card_congr (paritySignsFinEquiv (Fintype.card α - 1) b)]
  simp [Nat.card_eq_fintype_card,ZMod.card]

def signedSupport (T : Finset Omega) (s : T → Bit) : IntegerCoordinates :=
  fun i => if h : i ∈ T then (if s ⟨i,h⟩ = 0 then 1 else -1) else 0

def supportWord (T : Finset Omega) : BinaryWord := fun i => if i ∈ T then 1 else 0

theorem signedSupport_square (T : Finset Omega) (s : T → Bit) (i : Omega) :
    signedSupport T s i * signedSupport T s i = if i ∈ T then 1 else 0 := by
  simp only [signedSupport]; split_ifs <;> norm_num

theorem signedSupport_norm (T : Finset Omega) (s : T → Bit) :
    integerDot (signedSupport T s) (signedSupport T s) = T.card := by
  simp [integerDot,signedSupport_square]

theorem signedSupport_reduction (T : Finset Omega) (s : T → Bit) :
    integerReduction (signedSupport T s) = supportWord T := by
  ext i
  simp only [integerReduction,AddMonoidHom.coe_mk,ZeroHom.coe_mk,signedSupport,supportWord]
  split_ifs <;> decide

theorem signedSupport_injective (T : Finset Omega) : Function.Injective (signedSupport T) := by
  intro s t h
  funext i
  have hi := congrFun h i.val
  simp only [signedSupport,dif_pos i.prop] at hi
  rcases bit_cases (s i) with hs | hs <;> rcases bit_cases (t i) with ht | ht <;>
    simp_all

theorem signedSupport_sum (T : Finset Omega) (s : T → Bit) :
    (∑ i, signedSupport T s i) = (T.card : ℤ) - 2 * ∑ i : T, (if s i = 0 then (0 : ℤ) else 1) := by
  have hh : (∑ i, signedSupport T s i) = ∑ i : T, (if s i = 0 then (1 : ℤ) else -1) := by
    calc
      _ = ∑ i ∈ T, signedSupport T s i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ T)
        intro i _ hi
        simp [signedSupport,hi]
      _ = _ := by
        rw [← Finset.sum_attach T]
        simp [signedSupport]
  rw [hh]
  have he (i : T) : (if s i = 0 then (1 : ℤ) else -1) = 1 - 2 * (if s i = 0 then 0 else 1) := by
    split_ifs <;> norm_num
  simp only [he,Finset.sum_sub_distrib,← Finset.mul_sum]
  simp

theorem signedSupport_negative_parity (T : Finset Omega) (s : T → Bit) :
    ((∑ i : T, (if s i = 0 then (0 : ℤ) else 1) : ℤ) : Bit) = ∑ i : T, s i := by
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases bit_cases (s i) with h | h <;> simp [h]

end Atlas.Lattices
