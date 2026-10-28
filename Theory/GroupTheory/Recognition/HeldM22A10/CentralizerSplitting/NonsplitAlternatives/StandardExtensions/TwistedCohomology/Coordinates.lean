module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.Parity
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.Nonsplitting
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Word normalization for the twisted binary action of S4

Changing the section along a spanning tree in the two-generator Cayley graph
makes every tree edge trivial. The 25 remaining edges give 100 binary
coordinates. The cocycle identity reconstructs all other values from those
edges, without any classification hypothesis.

The finite permutation and word tables are checked by the Lean kernel.
This is the normalization step of the independent extension calculation used
for Huppert--Blackburn, *Finite Groups III*, XII.1.18(b), p.314.
-/

@[expose] public section

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions.TwistedCohomology
open LocalModelDichotomy AbelianExtension
open scoped BigOperators
def perm (i : Fin 24) : SymmetricFour where
  toFun := (![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 2, 3, 1], ![0, 3, 1, 2], ![0, 3, 2, 1], ![1, 0, 2, 3], ![1, 0, 3, 2], ![1, 2, 0, 3], ![1, 2, 3, 0], ![1, 3, 0, 2], ![1, 3, 2, 0], ![2, 0, 1, 3], ![2, 0, 3, 1], ![2, 1, 0, 3], ![2, 1, 3, 0], ![2, 3, 0, 1], ![2, 3, 1, 0], ![3, 0, 1, 2], ![3, 0, 2, 1], ![3, 1, 0, 2], ![3, 1, 2, 0], ![3, 2, 0, 1], ![3, 2, 1, 0]] i)
  invFun := (![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 3, 1, 2], ![0, 2, 3, 1], ![0, 3, 2, 1], ![1, 0, 2, 3], ![1, 0, 3, 2], ![2, 0, 1, 3], ![3, 0, 1, 2], ![2, 0, 3, 1], ![3, 0, 2, 1], ![1, 2, 0, 3], ![1, 3, 0, 2], ![2, 1, 0, 3], ![3, 1, 0, 2], ![2, 3, 0, 1], ![3, 2, 0, 1], ![1, 2, 3, 0], ![1, 3, 2, 0], ![2, 1, 3, 0], ![3, 1, 2, 0], ![2, 3, 1, 0], ![3, 2, 1, 0]] i)
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def mul (s t : Fin 24) : Fin 24 := (![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], ![1, 0, 4, 5, 2, 3, 7, 6, 10, 11, 8, 9, 18, 19, 20, 21, 22, 23, 12, 13, 14, 15, 16, 17], ![2, 3, 0, 1, 5, 4, 12, 13, 14, 15, 16, 17, 6, 7, 8, 9, 10, 11, 19, 18, 22, 23, 20, 21], ![3, 2, 5, 4, 0, 1, 13, 12, 16, 17, 14, 15, 19, 18, 22, 23, 20, 21, 6, 7, 8, 9, 10, 11], ![4, 5, 1, 0, 3, 2, 18, 19, 20, 21, 22, 23, 7, 6, 10, 11, 8, 9, 13, 12, 16, 17, 14, 15], ![5, 4, 3, 2, 1, 0, 19, 18, 22, 23, 20, 21, 13, 12, 16, 17, 14, 15, 7, 6, 10, 11, 8, 9], ![6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 14, 15, 12, 13, 17, 16, 20, 21, 18, 19, 23, 22], ![7, 6, 10, 11, 8, 9, 1, 0, 4, 5, 2, 3, 20, 21, 18, 19, 23, 22, 14, 15, 12, 13, 17, 16], ![8, 9, 6, 7, 11, 10, 14, 15, 12, 13, 17, 16, 0, 1, 2, 3, 4, 5, 21, 20, 23, 22, 18, 19], ![9, 8, 11, 10, 6, 7, 15, 14, 17, 16, 12, 13, 21, 20, 23, 22, 18, 19, 0, 1, 2, 3, 4, 5], ![10, 11, 7, 6, 9, 8, 20, 21, 18, 19, 23, 22, 1, 0, 4, 5, 2, 3, 15, 14, 17, 16, 12, 13], ![11, 10, 9, 8, 7, 6, 21, 20, 23, 22, 18, 19, 15, 14, 17, 16, 12, 13, 1, 0, 4, 5, 2, 3], ![12, 13, 14, 15, 16, 17, 2, 3, 0, 1, 5, 4, 8, 9, 6, 7, 11, 10, 22, 23, 19, 18, 21, 20], ![13, 12, 16, 17, 14, 15, 3, 2, 5, 4, 0, 1, 22, 23, 19, 18, 21, 20, 8, 9, 6, 7, 11, 10], ![14, 15, 12, 13, 17, 16, 8, 9, 6, 7, 11, 10, 2, 3, 0, 1, 5, 4, 23, 22, 21, 20, 19, 18], ![15, 14, 17, 16, 12, 13, 9, 8, 11, 10, 6, 7, 23, 22, 21, 20, 19, 18, 2, 3, 0, 1, 5, 4], ![16, 17, 13, 12, 15, 14, 22, 23, 19, 18, 21, 20, 3, 2, 5, 4, 0, 1, 9, 8, 11, 10, 6, 7], ![17, 16, 15, 14, 13, 12, 23, 22, 21, 20, 19, 18, 9, 8, 11, 10, 6, 7, 3, 2, 5, 4, 0, 1], ![18, 19, 20, 21, 22, 23, 4, 5, 1, 0, 3, 2, 10, 11, 7, 6, 9, 8, 16, 17, 13, 12, 15, 14], ![19, 18, 22, 23, 20, 21, 5, 4, 3, 2, 1, 0, 16, 17, 13, 12, 15, 14, 10, 11, 7, 6, 9, 8], ![20, 21, 18, 19, 23, 22, 10, 11, 7, 6, 9, 8, 4, 5, 1, 0, 3, 2, 17, 16, 15, 14, 13, 12], ![21, 20, 23, 22, 18, 19, 11, 10, 9, 8, 7, 6, 17, 16, 15, 14, 13, 12, 4, 5, 1, 0, 3, 2], ![22, 23, 19, 18, 21, 20, 16, 17, 13, 12, 15, 14, 5, 4, 3, 2, 1, 0, 11, 10, 9, 8, 7, 6], ![23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]] s t)
def gen : Fin 2 → Fin 24 := ![6, 9]
def words : Fin 24 → List (Fin 2) := ![[], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [0, 1], [1, 1, 1, 0], [1, 0, 1, 1, 0], [0], [1, 1, 0, 1, 1, 0], [0, 1, 1, 0, 1, 0], [1], [1, 0, 1], [1, 1, 1, 0, 1, 0], [1, 1, 0, 1], [0, 1, 0], [0, 1, 1, 0, 1], [1, 0], [1, 1], [0, 1, 1], [1, 1, 1], [1, 0, 1, 1], [1, 0, 1, 0], [1, 1, 1, 0, 1], [1, 1, 0], [0, 1, 1, 0]]
def wordIndex : List (Fin 2) → Fin 24
  | [] => 0
  | a :: w => mul (gen a) (wordIndex w)

theorem perm_zero : perm 0 = 1 := by decide +kernel

theorem perm_mul : ∀ s t, perm (mul s t) = perm s * perm t := by decide +kernel

theorem words_cover : ∀ s, wordIndex (words s) = s := by decide +kernel

theorem perm_surjective : Function.Surjective perm := by decide +kernel

def evalLift (c : FactorSet twistedAction) (w : List (Fin 2)) : c.Extension :=
  (w.map (fun a => (⟨1, perm (gen a)⟩ : c.Extension))).prod

theorem evalLift_quotient (c : FactorSet twistedAction) (w : List (Fin 2)) :
    (evalLift c w).quotient = perm (wordIndex w) := by
  induction w with
  | nil => exact perm_zero.symm
  | cons a w ih =>
    change perm (gen a) * (evalLift c w).quotient = perm (mul (gen a) (wordIndex w))
    rw [ih, perm_mul]

noncomputable def correction (c : FactorSet twistedAction) (s : SymmetricFour) : BinaryFour :=
  (evalLift c (words (Classical.choose (perm_surjective s)))).vector

theorem perm_injective : Function.Injective perm := by decide +kernel

theorem correction_perm (c : FactorSet twistedAction) (s : Fin 24) :
    correction c (perm s) = (evalLift c (words s)).vector := by
  have h : Classical.choose (perm_surjective (perm s)) = s :=
    perm_injective (Classical.choose_spec (perm_surjective (perm s)))
  simp only [correction, h]

theorem correction_one (c : FactorSet twistedAction) : correction c 1 = 1 := by
  rw [← perm_zero, correction_perm]
  rfl

-- Changing a section multiplies its cocycle by the associated coboundary.
def changeBy {N Q : Type*} [CommGroup N] [Group Q] {α : Q →* MulAut N}
    (c : FactorSet α) (b : Q → N) (hb : b 1 = 1) : FactorSet α where
  toFun q r := b q * α q (b r) * c.toFun q r * (b (q * r))⁻¹
  one_left q := by simp [hb, c.one_left]
  one_right q := by simp [hb, c.one_right]
  cocycle q r s := by
    simp only [map_mul, map_inv, MulAut.mul_apply]
    rw [← mul_assoc q r s]
    convert congrArg (fun z => b q * α q (b r) * α q (α r (b s)) *
      (b (q * r * s))⁻¹ * z) (c.cocycle q r s) using 1 <;>
      simp [mul_assoc, mul_left_comm, mul_comm]

noncomputable def normalize (c : FactorSet twistedAction) : FactorSet twistedAction :=
  changeBy c (correction c) (correction_one c)

theorem equivalent_changeBy {N Q : Type*} [CommGroup N] [Group Q] {α : Q →* MulAut N}
    (c : FactorSet α) (b : Q → N) (hb : b 1 = 1) : c.Equivalent (changeBy c b hb) := by
  refine ⟨fun q => (b q)⁻¹, by simp [hb], fun q r => ?_⟩
  simp [changeBy, mul_assoc, mul_left_comm, mul_comm]

theorem equivalent_normalize (c : FactorSet twistedAction) : c.Equivalent (normalize c) :=
  equivalent_changeBy c (correction c) (correction_one c)

def TreeEdge (a : Fin 2) (t : Fin 24) : Prop := words (mul (gen a) t) = a :: words t
instance (a : Fin 2) (t : Fin 24) : Decidable (TreeEdge a t) := inferInstanceAs
  (Decidable (words (mul (gen a) t) = a :: words t))

def Normalized (c : FactorSet twistedAction) : Prop :=
  ∀ a t, TreeEdge a t → c.toFun (perm (gen a)) (perm t) = 1

theorem words_gen : ∀ a, words (gen a) = [a] := by decide +kernel

theorem normalized_normalize (c : FactorSet twistedAction) : Normalized (normalize c) := by
  intro a t h
  have hgen : correction c (perm (gen a)) = 1 := by
    rw [correction_perm, words_gen]
    change (1 * twistedAction (perm (gen a)) 1 * c.toFun (perm (gen a)) 1) = 1
    simp [c.one_right]
  change correction c (perm (gen a)) * twistedAction (perm (gen a)) (correction c (perm t)) *
    c.toFun (perm (gen a)) (perm t) * (correction c (perm (gen a) * perm t))⁻¹ = 1
  rw [hgen, ← perm_mul, correction_perm, correction_perm]
  change words (mul (gen a) t) = a :: words t at h
  rw [h]
  change 1 * twistedAction (perm (gen a)) (evalLift c (words t)).vector *
    c.toFun (perm (gen a)) (perm t) *
    (1 * twistedAction (perm (gen a)) (evalLift c (words t)).vector *
      c.toFun (perm (gen a)) (evalLift c (words t)).quotient)⁻¹ = 1
  rw [evalLift_quotient, words_cover]
  exact mul_inv_cancel _


def freeCoordinate : Fin 100 → Fin 2 × Fin 24 × Fin 4 := ![(0, 1, 0), (0, 1, 1), (0, 1, 2), (0, 1, 3), (0, 3, 0), (0, 3, 1), (0, 3, 2), (0, 3, 3), (0, 4, 0), (0, 4, 1), (0, 4, 2), (0, 4, 3), (0, 5, 0), (0, 5, 1), (0, 5, 2), (0, 5, 3), (0, 6, 0), (0, 6, 1), (0, 6, 2), (0, 6, 3), (0, 7, 0), (0, 7, 1), (0, 7, 2), (0, 7, 3), (0, 8, 0), (0, 8, 1), (0, 8, 2), (0, 8, 3), (0, 10, 0), (0, 10, 1), (0, 10, 2), (0, 10, 3), (0, 11, 0), (0, 11, 1), (0, 11, 2), (0, 11, 3), (0, 13, 0), (0, 13, 1), (0, 13, 2), (0, 13, 3), (0, 14, 0), (0, 14, 1), (0, 14, 2), (0, 14, 3), (0, 17, 0), (0, 17, 1), (0, 17, 2), (0, 17, 3), (0, 18, 0), (0, 18, 1), (0, 18, 2), (0, 18, 3), (0, 19, 0), (0, 19, 1), (0, 19, 2), (0, 19, 3), (0, 20, 0), (0, 20, 1), (0, 20, 2), (0, 20, 3), (0, 21, 0), (0, 21, 1), (0, 21, 2), (0, 21, 3), (0, 23, 0), (0, 23, 1), (0, 23, 2), (0, 23, 3), (1, 1, 0), (1, 1, 1), (1, 1, 2), (1, 1, 3), (1, 4, 0), (1, 4, 1), (1, 4, 2), (1, 4, 3), (1, 7, 0), (1, 7, 1), (1, 7, 2), (1, 7, 3), (1, 8, 0), (1, 8, 1), (1, 8, 2), (1, 8, 3), (1, 11, 0), (1, 11, 1), (1, 11, 2), (1, 11, 3), (1, 14, 0), (1, 14, 1), (1, 14, 2), (1, 14, 3), (1, 18, 0), (1, 18, 1), (1, 18, 2), (1, 18, 3), (1, 21, 0), (1, 21, 1), (1, 21, 2), (1, 21, 3)]
def slot (a : Fin 2) (t : Fin 24) (i : Fin 4) : Option (Fin 100) := ![![![none, none, none, none], ![some 0, some 1, some 2, some 3], ![none, none, none, none], ![some 4, some 5, some 6, some 7], ![some 8, some 9, some 10, some 11], ![some 12, some 13, some 14, some 15], ![some 16, some 17, some 18, some 19], ![some 20, some 21, some 22, some 23], ![some 24, some 25, some 26, some 27], ![none, none, none, none], ![some 28, some 29, some 30, some 31], ![some 32, some 33, some 34, some 35], ![none, none, none, none], ![some 36, some 37, some 38, some 39], ![some 40, some 41, some 42, some 43], ![none, none, none, none], ![none, none, none, none], ![some 44, some 45, some 46, some 47], ![some 48, some 49, some 50, some 51], ![some 52, some 53, some 54, some 55], ![some 56, some 57, some 58, some 59], ![some 60, some 61, some 62, some 63], ![none, none, none, none], ![some 64, some 65, some 66, some 67]], ![![none, none, none, none], ![some 68, some 69, some 70, some 71], ![none, none, none, none], ![none, none, none, none], ![some 72, some 73, some 74, some 75], ![none, none, none, none], ![none, none, none, none], ![some 76, some 77, some 78, some 79], ![some 80, some 81, some 82, some 83], ![none, none, none, none], ![none, none, none, none], ![some 84, some 85, some 86, some 87], ![none, none, none, none], ![none, none, none, none], ![some 88, some 89, some 90, some 91], ![none, none, none, none], ![none, none, none, none], ![none, none, none, none], ![some 92, some 93, some 94, some 95], ![none, none, none, none], ![none, none, none, none], ![some 96, some 97, some 98, some 99], ![none, none, none, none], ![none, none, none, none]]] a t i

def edge (x : Fin 100 → ZMod 2) (a : Fin 2) (t : Fin 24) : BinaryFour :=
  Multiplicative.ofAdd (fun i => (slot a t i).elim 0 x)

def coordinates (c : FactorSet twistedAction) (k : Fin 100) : ZMod 2 :=
  (c.toFun (perm (gen (freeCoordinate k).1)) (perm (freeCoordinate k).2.1)).toAdd
    (freeCoordinate k).2.2

theorem slot_none : ∀ a t i, slot a t i = none → t = 0 ∨ TreeEdge a t := by decide +kernel

theorem slot_some : ∀ a t i k, slot a t i = some k → freeCoordinate k = (a,t,i) := by
  decide +kernel

theorem edge_coordinates (c : FactorSet twistedAction) (hc : Normalized c) (a : Fin 2) (t : Fin 24) :
    edge (coordinates c) a t = c.toFun (perm (gen a)) (perm t) := by
  apply Multiplicative.toAdd.injective
  funext i
  change (slot a t i).elim 0 (coordinates c) = _
  cases h : slot a t i with
  | none =>
    rcases slot_none a t i h with ht | ht
    · subst t; rw [perm_zero, c.one_right]; rfl
    · rw [hc a t ht]; rfl
  | some k =>
    have hk := slot_some a t i k h
    simp only [Option.elim_some, coordinates, hk]

def expand (e : Fin 2 → Fin 24 → BinaryFour) : List (Fin 2) → Fin 24 → BinaryFour
  | [], _ => 1
  | a :: w, t => (e a (wordIndex w))⁻¹ *
      twistedAction (perm (gen a)) (expand e w t) * e a (mul (wordIndex w) t)

theorem expand_eq (c : FactorSet twistedAction) (w : List (Fin 2)) (t : Fin 24) :
    expand (fun a t => c.toFun (perm (gen a)) (perm t)) w t =
      c.toFun (perm (wordIndex w)) (perm t) := by
  induction w with
  | nil => simpa only [expand, wordIndex, perm_zero] using (c.one_left (perm t)).symm
  | cons a w ih =>
    change (c.toFun (perm (gen a)) (perm (wordIndex w)))⁻¹ *
      twistedAction (perm (gen a)) _ * c.toFun (perm (gen a)) (perm (mul (wordIndex w) t)) = _
    rw [ih, perm_mul]
    change _ = c.toFun (perm (mul (gen a) (wordIndex w))) (perm t)
    rw [perm_mul]
    rw [mul_assoc, ← c.cocycle]
    exact inv_mul_cancel_left _ _

def table (x : Fin 100 → ZMod 2) (s t : Fin 24) : BinaryFour := expand (edge x) (words s) t

theorem table_coordinates (c : FactorSet twistedAction) (hc : Normalized c) (s t : Fin 24) :
    table (coordinates c) s t = c.toFun (perm s) (perm t) := by
  unfold table
  rw [show edge (coordinates c) = (fun a t => c.toFun (perm (gen a)) (perm t)) from
    funext (fun a => funext (fun t => edge_coordinates c hc a t))]
  rw [expand_eq, words_cover]

def IsCocycleTable (x : Fin 100 → ZMod 2) : Prop := ∀ s t u,
  table x s t * table x (mul s t) u = twistedAction (perm s) (table x t u) * table x s (mul t u)

theorem coordinates_cocycle (c : FactorSet twistedAction) (hc : Normalized c) :
    IsCocycleTable (coordinates c) := by
  intro s t u
  simp only [table_coordinates c hc, perm_mul]
  exact c.cocycle _ _ _

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions.TwistedCohomology
