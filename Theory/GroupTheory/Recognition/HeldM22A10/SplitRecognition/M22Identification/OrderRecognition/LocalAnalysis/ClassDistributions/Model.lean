module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData

/-!
# Finite class-count certificates for the Case II model

Seventeen explicit representatives cover the local model by conjugacy. A
coordinate table chooses a conjugator for every element; the Lean kernel checks
all these equalities and the fiber cardinalities. Merging the selected fibers
in either of the two possible ways for the last order-four pair gives the
centralizer and Sylow counts in Janko's source. This module asserts no ambient
fusion: the ambient argument must justify the merge separately.

The coordinate Sylow is the inverse image in the semidirect product of the
centralizer in S4 of the double transposition `a`. Its order is 128.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 5, pp.8–10, and Lemma 13, p.14.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
namespace CaseII
namespace Distribution

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

/-- The seventeen source representatives used to cover the local model. -/
@[expose] public def localRepresentative : Fin 17 → TwistedModel :=
  ![1, z 0, z 1, z 2, a, d, c, c * z 0, c * z 1, c * z 0 * z 1,
    z 3 * a, z 1 * a, b * d, z 1 * d, z 3 * d, z 1 * z 3 * d, z 1 * b * d]

private def actor : Fin 24 → SymmetricFour :=
  ![1,
    Equiv.swap 2 3,
    Equiv.swap 1 2,
    Equiv.swap 1 2 * Equiv.swap 2 3,
    Equiv.swap 1 3 * Equiv.swap 2 3,
    Equiv.swap 1 3,
    Equiv.swap 0 1,
    Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 1 * Equiv.swap 1 2,
    Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3,
    Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 3,
    Equiv.swap 0 1 * Equiv.swap 1 3,
    Equiv.swap 0 2 * Equiv.swap 1 2,
    Equiv.swap 0 2 * Equiv.swap 1 2 * Equiv.swap 2 3,
    Equiv.swap 0 2,
    Equiv.swap 0 2 * Equiv.swap 2 3,
    Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 2 3,
    Equiv.swap 0 3 * Equiv.swap 1 3 * Equiv.swap 2 3,
    Equiv.swap 0 3 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 2 3,
    Equiv.swap 0 3,
    Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 2 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]

private def actorIndex (s : SymmetricFour) : Fin 24 :=
  ⟨(6 * (s 0).val + 2 * ((if s 2 < s 1 then 1 else 0) +
    (if s 3 < s 1 then 1 else 0)) + (if s 3 < s 2 then 1 else 0)) % 24,
    Nat.mod_lt _ (by decide)⟩

private def vectorIndex (v : BinaryFour) : Fin 16 :=
  ⟨((v.toAdd 0).val + 2 * (v.toAdd 1).val + 4 * (v.toAdd 2).val +
    8 * (v.toAdd 3).val) % 16, Nat.mod_lt _ (by decide)⟩

private def element (n : Fin 384) : TwistedModel :=
  ⟨Multiplicative.ofAdd (fun i => ((n.val % 16 / 2 ^ i.val : ℕ) : ZMod 2)),
    actor ⟨n.val / 16 % 24, Nat.mod_lt _ (by decide)⟩⟩

/-- A finite coordinate classifier; its meaning is certified by conjugation below. -/
public def localClass (x : TwistedModel) : Fin 17 :=
  (![![0, 2, 2, 3, 2, 3, 3, 2, 2, 3, 3, 2, 3, 2, 2, 1],
    ![5, 13, 13, 5, 15, 14, 14, 15, 15, 14, 14, 15, 5, 13, 13, 5],
    ![5, 13, 15, 14, 15, 14, 5, 13, 13, 5, 14, 15, 14, 15, 13, 5],
    ![6, 8, 9, 7, 9, 7, 6, 8, 9, 7, 6, 8, 6, 8, 9, 7],
    ![6, 9, 8, 7, 8, 7, 6, 9, 8, 7, 6, 9, 6, 9, 8, 7],
    ![5, 13, 15, 14, 13, 5, 14, 15, 15, 14, 5, 13, 14, 15, 13, 5],
    ![5, 15, 15, 5, 13, 14, 14, 13, 13, 14, 14, 13, 5, 15, 15, 5],
    ![4, 11, 11, 4, 11, 10, 10, 11, 11, 10, 10, 11, 4, 11, 11, 4],
    ![6, 8, 8, 6, 8, 6, 6, 8, 9, 7, 7, 9, 7, 9, 9, 7],
    ![12, 16, 16, 12, 16, 12, 12, 16, 16, 12, 12, 16, 12, 16, 16, 12],
    ![12, 16, 16, 12, 16, 12, 12, 16, 16, 12, 12, 16, 12, 16, 16, 12],
    ![6, 9, 9, 6, 8, 7, 7, 8, 9, 6, 6, 9, 7, 8, 8, 7],
    ![6, 9, 9, 6, 9, 6, 6, 9, 8, 7, 7, 8, 7, 8, 8, 7],
    ![12, 16, 16, 12, 16, 12, 12, 16, 16, 12, 12, 16, 12, 16, 16, 12],
    ![5, 15, 13, 14, 15, 5, 14, 13, 13, 14, 5, 15, 14, 13, 15, 5],
    ![6, 8, 9, 7, 8, 6, 7, 9, 8, 6, 7, 9, 6, 8, 9, 7],
    ![4, 11, 11, 10, 11, 4, 10, 11, 11, 10, 4, 11, 10, 11, 11, 4],
    ![12, 16, 16, 12, 16, 12, 12, 16, 16, 12, 12, 16, 12, 16, 16, 12],
    ![12, 16, 16, 12, 16, 12, 12, 16, 16, 12, 12, 16, 12, 16, 16, 12],
    ![6, 8, 8, 6, 9, 7, 7, 9, 8, 6, 6, 8, 7, 9, 9, 7],
    ![6, 9, 8, 7, 9, 6, 7, 8, 9, 6, 7, 8, 6, 9, 8, 7],
    ![5, 15, 13, 14, 13, 14, 5, 15, 15, 5, 14, 13, 14, 13, 15, 5],
    ![12, 16, 16, 12, 16, 12, 12, 16, 16, 12, 12, 16, 12, 16, 16, 12],
    ![4, 11, 11, 10, 11, 10, 4, 11, 11, 4, 10, 11, 10, 11, 11, 4]]) (actorIndex x.right) (vectorIndex x.left)

private def conjugator (x : TwistedModel) : TwistedModel :=
  element ((![![0, 0, 112, 256, 128, 208, 48, 144, 176, 192, 32, 160, 0, 96, 16, 0],
    ![0, 0, 4, 4, 4, 4, 0, 0, 1, 1, 5, 5, 5, 5, 1, 1],
    ![48, 48, 52, 52, 49, 49, 53, 53, 52, 52, 48, 48, 53, 53, 49, 49],
    ![0, 0, 4, 4, 6, 6, 2, 2, 2, 2, 6, 6, 4, 4, 0, 0],
    ![16, 16, 20, 20, 18, 18, 22, 22, 22, 22, 18, 18, 20, 20, 16, 16],
    ![32, 33, 37, 36, 37, 36, 32, 33, 32, 33, 37, 36, 37, 36, 32, 33],
    ![256, 260, 257, 261, 256, 260, 257, 261, 260, 256, 261, 257, 260, 256, 261, 257],
    ![0, 0, 1, 1, 256, 1, 0, 260, 257, 5, 4, 261, 4, 4, 5, 5],
    ![144, 148, 150, 146, 146, 150, 148, 144, 144, 148, 150, 146, 146, 150, 148, 144],
    ![64, 64, 66, 66, 70, 70, 68, 68, 71, 71, 69, 69, 65, 65, 67, 67],
    ![80, 83, 81, 82, 84, 87, 85, 86, 85, 86, 84, 87, 81, 82, 80, 83],
    ![128, 132, 134, 130, 128, 132, 134, 130, 130, 134, 132, 128, 130, 134, 132, 128],
    ![176, 180, 178, 182, 182, 178, 180, 176, 176, 180, 178, 182, 182, 178, 180, 176],
    ![48, 48, 55, 55, 50, 50, 53, 53, 54, 54, 49, 49, 52, 52, 51, 51],
    ![208, 213, 209, 212, 208, 213, 209, 212, 213, 208, 212, 209, 213, 208, 212, 209],
    ![96, 100, 96, 100, 102, 98, 102, 98, 98, 102, 98, 102, 100, 96, 100, 96],
    ![32, 37, 213, 33, 36, 33, 32, 209, 212, 37, 36, 33, 36, 208, 32, 37],
    ![16, 19, 21, 22, 17, 18, 20, 23, 20, 23, 17, 18, 21, 22, 16, 19],
    ![32, 35, 36, 39, 37, 38, 33, 34, 33, 34, 37, 38, 36, 39, 32, 35],
    ![160, 164, 162, 166, 160, 164, 162, 166, 166, 162, 164, 160, 166, 162, 164, 160],
    ![112, 116, 112, 116, 114, 118, 114, 118, 118, 114, 118, 114, 116, 112, 116, 112],
    ![192, 196, 192, 196, 196, 192, 196, 192, 193, 197, 193, 197, 197, 193, 197, 193],
    ![0, 0, 6, 6, 7, 7, 1, 1, 2, 2, 4, 4, 5, 5, 3, 3],
    ![48, 48, 192, 49, 193, 53, 52, 52, 49, 49, 48, 196, 52, 197, 53, 53]]) (actorIndex x.right) (vectorIndex x.left))

/-- Each element is conjugate to the representative selected by its coordinates. -/
public theorem localClass_conjugate (x : TwistedModel) :
    IsConj x (localRepresentative (localClass x)) := by
  have h : ∀ x : TwistedModel,
      conjugator x * x * (conjugator x)⁻¹ = localRepresentative (localClass x) := by
    decide +kernel
  exact isConj_iff.mpr ⟨conjugator x, h x⟩

/-- The coordinate Sylow two-group is the inverse image of the centralizer
of the double transposition `a` in S4. -/
@[expose] public def modelSylow : Subgroup TwistedModel :=
  (centralizer ({a.right} : Set SymmetricFour)).comap SemidirectProduct.rightHom

local instance : DecidablePred (· ∈ modelSylow) := fun x =>
  decidable_of_iff (x.right * a.right = a.right * x.right)
    mem_centralizer_singleton_iff.symm

public theorem modelSylow_card : Nat.card modelSylow = 128 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

public theorem localClass_card : ∀ i : Fin 17,
    Nat.card {x : TwistedModel // localClass x = i} =
      ![1, 1, 8, 6, 12, 24, 32, 32, 32, 32, 12, 24, 48, 24, 24, 24, 48] i := by
  intro i
  rw [Nat.card_eq_fintype_card]
  have h : ∀ i : Fin 17,
      Fintype.card {x : TwistedModel // localClass x = i} =
        ![1, 1, 8, 6, 12, 24, 32, 32, 32, 32, 12, 24, 48, 24, 24, 24, 48] i := by decide +kernel
  exact h i

public theorem localClass_sylow_card : ∀ i : Fin 17,
    Nat.card {x : modelSylow // localClass x.val = i} =
      ![1, 1, 8, 6, 12, 8, 0, 0, 0, 0, 12, 24, 16, 8, 8, 8, 16] i := by
  intro i
  rw [Nat.card_eq_fintype_card]
  have h : ∀ i : Fin 17,
      Fintype.card {x : modelSylow // localClass x.val = i} =
        ![1, 1, 8, 6, 12, 8, 0, 0, 0, 0, 12, 24, 16, 8, 8, 8, 16] i := by decide +kernel
  exact h i

/-- Either possible assignment of the last two order-four classes gives the
same distribution. No assignment is asserted without an ambient fusion proof. -/
@[expose] public def mergedClass (swap : Bool) : Fin 17 → Fin 7 :=
  ![0, 1, 1, 1, 1, 1, 2, 5, 5, 5, 3, 4, 3, 4,
    if swap then 4 else 3, if swap then 3 else 4, 6]

public theorem mergedClass_card : ∀ (swap : Bool) (i : Fin 7),
    Nat.card {x : TwistedModel // mergedClass swap (localClass x) = i} =
      ![1, 51, 32, 84, 72, 96, 48] i := by
  intro swap i
  rw [Nat.card_eq_fintype_card]
  have h : ∀ (swap : Bool) (i : Fin 7),
      Fintype.card {x : TwistedModel // mergedClass swap (localClass x) = i} =
        ![1, 51, 32, 84, 72, 96, 48] i := by decide +kernel
  exact h swap i

public theorem mergedClass_sylow_card : ∀ (swap : Bool) (i : Fin 7),
    Nat.card {x : modelSylow // mergedClass swap (localClass x.val) = i} =
      ![1, 35, 0, 36, 40, 0, 16] i := by
  intro swap i
  rw [Nat.card_eq_fintype_card]
  have h : ∀ (swap : Bool) (i : Fin 7),
      Fintype.card {x : modelSylow // mergedClass swap (localClass x.val) = i} =
        ![1, 35, 0, 36, 40, 0, 16] i := by decide +kernel
  exact h swap i

public theorem localRepresentative_order : ∀ i : Fin 17,
    orderOf (localRepresentative i) =
      ![1, 2, 2, 2, 2, 2, 3, 6, 6, 6, 4, 4, 4, 4, 4, 4, 8] i := by
  let n : Fin 17 → ℕ := ![1, 2, 2, 2, 2, 2, 3, 6, 6, 6, 4, 4, 4, 4, 4, 4, 8]
  have hpos : ∀ i, 0 < n i := by decide
  have h : ∀ i : Fin 17, (localRepresentative i) ^ n i = 1 ∧
      ∀ m : Fin (n i), 0 < m.val → (localRepresentative i) ^ m.val ≠ 1 := by
    decide +kernel
  intro i
  exact (orderOf_eq_iff (hpos i)).mpr ⟨(h i).1, fun m hm hpos => (h i).2 ⟨m, hm⟩ hpos⟩

public theorem classRepresentative_order : ∀ i : Fin 7,
    orderOf (classRepresentative i) = ![1, 2, 3, 4, 4, 6, 8] i := by
  intro i
  have h := localRepresentative_order (![0, 1, 6, 10, 13, 7, 16] i)
  fin_cases i <;> exact h

end Distribution
end CaseII
end Theory.GroupTheory.HeldM22A10.M22Identification
