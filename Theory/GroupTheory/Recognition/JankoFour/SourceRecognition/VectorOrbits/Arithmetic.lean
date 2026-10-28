module

public import Theory.Representation.Mathieu.M22James.Model
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness

/-!
# Binary coordinates for the source J₄ involution orbits

The twelve-bit words enumerate the native triple-cover module. XOR evaluates
its vector addition, and the checked columns of the two native generators
connect packed computation with the actual group representation.

This prepares the module calculation in Aschbacher–Segev, *The uniqueness of
groups of type J₄*, Invent. Math. 105 (1991), (4.2), p.597,
DOI 10.1007/BF01232280. The matrices and ATLAS attribution are inherited from
`M22James.Model`. The coordinate and XOR proofs follow the existing
`BinaryQuarticMathieu.RankRecognition` implementation, in dimension twelve.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.VectorOrbits
open Sporadic.Mathieu M22TripleCover
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

abbrev Word := Fin 4096

def vector (n : Nat) : BinarySpace := fun i => if n.testBit i.val then 1 else 0

def decode (n : Word) : BinarySpace := vector n.val

theorem decode_injective : Function.Injective decode := by
  intro a b hab
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · have hh := congrFun hab ⟨i, hi⟩
    change (if a.val.testBit i then (1 : ZMod 2) else 0) =
      (if b.val.testBit i then (1 : ZMod 2) else 0) at hh
    cases ha : a.val.testBit i <;> cases hb : b.val.testBit i <;> simp_all
  · have hpow : 4096 ≤ 2 ^ i := by
      calc
        4096 = 2 ^ 12 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt hpow)]

theorem decode_bijective : Function.Bijective decode := by
  apply (Nat.bijective_iff_injective_and_card decode).mpr
  exact ⟨decode_injective, by simp [BinarySpace]⟩

noncomputable def decodeEquiv : Word ≃ BinarySpace := Equiv.ofBijective decode decode_bijective

theorem vector_xor (a b : Nat) : vector (Nat.xor a b) = vector a + vector b := by
  funext i
  change (if (a ^^^ b).testBit i.val then (1 : ZMod 2) else 0) =
    (if a.testBit i.val then 1 else 0) + (if b.testBit i.val then 1 else 0)
  rw [Nat.testBit_xor]
  cases a.testBit i.val <;> cases b.testBit i.val <;> decide +kernel

theorem vector_zero : vector 0 = 0 := by decide +kernel

private theorem vector_xor_fold (l : List Nat) :
    vector (l.foldr Nat.xor 0) = (l.map vector).sum := by
  induction l with
  | nil => exact vector_zero
  | cons a l ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, vector_xor, ih]

def columnMap (c : Fin 12 → Nat) : BinarySpace →ₗ[ZMod 2] BinarySpace where
  toFun v := ∑ i, v i • vector (c i)
  map_add' v w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

def packedAction (c : Fin 12 → Nat) (n : Nat) : Nat :=
  (List.ofFn (fun i : Fin 12 => if n.testBit i.val then c i else 0)).foldr Nat.xor 0

theorem vector_packedAction (c : Fin 12 → Nat) (n : Nat) :
    vector (packedAction c n) = columnMap c (vector n) := by
  rw [packedAction, vector_xor_fold, List.map_ofFn]
  simp only [List.sum_ofFn]
  change (∑ i, vector (if n.testBit i.val then c i else 0)) =
    ∑ i, (if n.testBit i.val then (1 : ZMod 2) else 0) • vector (c i)
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all only [one_smul, zero_smul, vector_zero]

def columnsA : Fin 12 → Nat := ![320,864,2374,581,68,384,256,2184,2704,896,2304,1152]

def columnsB : Fin 12 → Nat := ![1044,1446,4,1452,1029,384,3840,128,160,928,1024,1856]

theorem columnMap_generatorA : columnMap columnsA = binaryRepresentation coreGeneratorA := by
  apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
  intro i
  simp only [Pi.basisFun_apply]
  revert i
  decide +kernel

theorem columnMap_generatorB : columnMap columnsB = binaryRepresentation coreGeneratorB := by
  apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
  intro i
  simp only [Pi.basisFun_apply]
  revert i
  decide +kernel

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.VectorOrbits
end
