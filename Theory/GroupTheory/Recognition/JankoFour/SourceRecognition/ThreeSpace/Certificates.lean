module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.SecondStabilizer.Certificates
public import Mathlib.LinearAlgebra.QuadraticForm.Basis

/-!
# Linear constraints on a singular stabilizer-invariant subspace

Five words in the genuine full cubic matrix action fix the first singular
vector. Six checked identities express independent linear forms as sums of
quadratic displacement forms for words in those five elements. Consequently,
a totally singular subspace invariant under that stabilizer satisfies all six
linear constraints. Every identity is checked on a basis and on sums of two
basis vectors; the original native quadratic form is retained exactly.

These certificates prove the linear uniqueness step in Aschbacher–Segev,
*The uniqueness of groups of type J₄*, Invent. Math. 105 (1991), proof of
(4.3)(2), p.597, DOI 10.1007/BF01232280. The imported native matrix model
retains its ATLAS source attribution and license. Polynomial coordinates
avoid repeatedly reducing the Hermitian construction in displacement checks.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open M22TripleCover.Ambient
open Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.Native
open VectorOrbits

theorem quadratic_ext (q r : QuadraticForm (ZMod 2) M22TripleCover.BinarySpace)
    (hb : ∀ i : Fin 12, q (vector (2 ^ i.val)) = r (vector (2 ^ i.val)))
    (hp : ∀ i j : Fin 12, q (vector (2 ^ i.val) + vector (2 ^ j.val)) =
      r (vector (2 ^ i.val) + vector (2 ^ j.val))) : q = r := by
  let b := Pi.basisFun (ZMod 2) (Fin 12)
  have he : q.toBilin b = r.toBilin b := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    change q.toBilin b (b i) (b j) = r.toBilin b (b i) (b j)
    rw [QuadraticMap.toBilin_apply,QuadraticMap.toBilin_apply]
    simp only [b, Pi.basisFun_apply,
      SecondStabilizer.Certificates.basis_vector, QuadraticMap.polar, hp, hb]
  rw [← q.toQuadraticMap_toBilin b, ← r.toQuadraticMap_toBilin b, he]


abbrev A : actionGroup := SecondStabilizer.Certificates.A
abbrev B : actionGroup := SecondStabilizer.Certificates.B

def generatorWords : Fin 5 → List (Fin 5) := ![
  [1],
  [2,2,3,2,1,0,1,0,0],
  [2,2,2,3,2,1,0,1,0,0,0],
  [2,2,2,2,3,2,1,0,1,0,0,0,0],
  [2,3,2,3,2,3,2,2,2,3,4]]

def generators (j : Fin 5) : actionGroup :=
  SecondStabilizer.Certificates.nativeWord (generatorWords j)

def columns : Fin 5 → Fin 12 → Nat := ![
  ![1044,1446,4,1452,1029,384,3840,128,160,928,1024,1856],
  ![1331,3522,4,679,3536,633,1412,1821,2308,3481,3677,2048],
  ![3136,2,4,3831,2112,3992,1105,2455,2384,512,17,1089],
  ![3672,504,4,777,3400,1628,833,635,2341,1148,2392,37],
  ![3924,1848,4,2581,163,3442,1713,1411,3200,2004,788,1922]]

theorem generators_action (j : Fin 5) : binaryAction (generators j) = columnMap (columns j) := by
  apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
  intro i
  simp only [Pi.basisFun_apply, SecondStabilizer.Certificates.basis_vector]
  rw [generators, SecondStabilizer.Certificates.nativeWord_vector, ← vector_packedAction]
  revert j i
  decide +kernel

def word (l : List (Fin 5)) : actionGroup := (l.map generators).prod

def wordPacked (l : List (Fin 5)) (n : Nat) : Nat :=
  l.foldr (fun j v => packedAction (columns j) v) n

theorem word_vector (l : List (Fin 5)) (n : Nat) :
    binaryAction (word l) (vector n) = vector (wordPacked l n) := by
  induction l with
  | nil => change binaryAction 1 _ = _; rw [map_one]; rfl
  | cons j l ih =>
    change binaryAction (generators j * word l) _ = _
    rw [map_mul,Module.End.mul_apply,ih,generators_action,← vector_packedAction]
    rfl

theorem generators_mem (j : Fin 5) : generators j ∈ nativeVectorStabilizer (decode 4) := by
  change binaryAction (generators j) (vector 4) = vector 4
  rw [generators_action,← vector_packedAction]
  revert j
  decide +kernel

theorem word_mem (l : List (Fin 5)) : word l ∈ nativeVectorStabilizer (decode 4) := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
  exact generators_mem j

def quadraticMatrix : Matrix (Fin 12) (Fin 12) (ZMod 2) := ![
  ![1,1,0,1,0,0,1,0,1,1,0,1],
  ![0,1,1,1,0,1,1,0,1,1,1,1],
  ![0,0,0,1,0,0,0,1,1,1,0,0],
  ![0,0,0,0,0,1,0,1,0,1,1,1],
  ![0,0,0,0,1,1,0,0,0,0,0,0],
  ![0,0,0,0,0,1,1,1,1,1,0,1],
  ![0,0,0,0,0,0,1,0,1,0,1,0],
  ![0,0,0,0,0,0,0,1,1,0,1,0],
  ![0,0,0,0,0,0,0,0,1,1,1,1],
  ![0,0,0,0,0,0,0,0,0,1,1,0],
  ![0,0,0,0,0,0,0,0,0,0,0,1],
  ![0,0,0,0,0,0,0,0,0,0,0,0]]

def quadratic : QuadraticForm (ZMod 2) M22TripleCover.BinarySpace :=
  quadraticMatrix.toQuadraticForm'

theorem quadratic_apply (v : M22TripleCover.BinarySpace) :
    quadratic v = v 0 * v 0 +
    v 1 * v 1 +
    v 4 * v 4 +
    v 5 * v 5 +
    v 6 * v 6 +
    v 7 * v 7 +
    v 8 * v 8 +
    v 9 * v 9 +
    v 0 * v 1 +
    v 0 * v 3 +
    v 0 * v 6 +
    v 0 * v 8 +
    v 0 * v 9 +
    v 0 * v 11 +
    v 1 * v 2 +
    v 1 * v 3 +
    v 1 * v 5 +
    v 1 * v 6 +
    v 1 * v 8 +
    v 1 * v 9 +
    v 1 * v 10 +
    v 1 * v 11 +
    v 2 * v 3 +
    v 2 * v 7 +
    v 2 * v 8 +
    v 2 * v 9 +
    v 3 * v 5 +
    v 3 * v 7 +
    v 3 * v 9 +
    v 3 * v 10 +
    v 3 * v 11 +
    v 4 * v 5 +
    v 5 * v 6 +
    v 5 * v 7 +
    v 5 * v 8 +
    v 5 * v 9 +
    v 5 * v 11 +
    v 6 * v 8 +
    v 6 * v 10 +
    v 7 * v 8 +
    v 7 * v 10 +
    v 8 * v 9 +
    v 8 * v 10 +
    v 8 * v 11 +
    v 9 * v 10 +
    v 10 * v 11 := by
  change Matrix.toLinearMap₂' (ZMod 2) quadraticMatrix v v = _
  rw [Matrix.toLinearMap₂'_apply']
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,quadraticMatrix]
  ring

def packedQuadratic (n : Nat) : ZMod 2 :=
  (fun i => if n.testBit i then (1 : ZMod 2) else 0) 0 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 0 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 1 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 1 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 4 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 4 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 5 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 5 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 6 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 6 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 7 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 7 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 8 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 8 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 9 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 9 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 0 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 1 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 0 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 3 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 0 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 6 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 0 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 8 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 0 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 9 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 0 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 11 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 1 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 2 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 1 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 3 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 1 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 5 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 1 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 6 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 1 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 8 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 1 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 9 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 1 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 10 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 1 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 11 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 2 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 3 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 2 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 7 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 2 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 8 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 2 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 9 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 3 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 5 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 3 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 7 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 3 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 9 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 3 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 10 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 3 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 11 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 4 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 5 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 5 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 6 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 5 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 7 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 5 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 8 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 5 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 9 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 5 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 11 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 6 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 8 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 6 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 10 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 7 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 8 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 7 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 10 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 8 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 9 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 8 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 10 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 8 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 11 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 9 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 10 +
    (fun i => if n.testBit i then (1 : ZMod 2) else 0) 10 * (fun i => if n.testBit i then (1 : ZMod 2) else 0) 11

theorem quadratic_vector (n : Nat) : quadratic (vector n) = packedQuadratic n :=
  quadratic_apply _

theorem quadratic_eq_native : quadratic = M22TripleCover.Unitary.quadraticForm := by
  apply quadratic_ext
  · intro i
    revert i
    decide +kernel
  · intro i j
    simp only [← vector_xor]
    revert i j
    decide +kernel

def linear (n : Nat) : M22TripleCover.BinarySpace →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ i, vector n i * v i
  map_add' v w := by simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum,mul_left_comm]

def displacement (l : List (Fin 5)) : QuadraticForm (ZMod 2) M22TripleCover.BinarySpace :=
  quadratic.comp (LinearMap.id + binaryAction (word l))

def identityWords : Fin 6 → List (List (Fin 5)) := ![
  [[1,4],[4,1,0],[1,4,0],[2,4,0],[4,0,1],[4,0,2]],
  [[4],[4,0],[4,1],[4,3],[0,4],[4,1,0],[4,2,0],[4,3,0],[1,4,0],[2,4,0],[1,4,1],[4,3,2],[0,4,2]],
  [[4,0],[4,1],[4,3],[0,4],[4,1,0],[4,3,0],[2,4,0],[4,3,1],[1,4,1],[4,0,2],[4,3,2],[0,4,2]],
  [[4],[4,2,0],[4,3,0],[0,4,0],[1,4,0],[4,3,1],[4,0,2],[4,3,2],[0,4,2]],
  [[4],[4,0],[0,4],[1,4],[4,1,0],[0,4,0],[1,4,0],[2,4,0],[4,0,1],[4,0,2]],
  [[4],[4,0],[4,1],[0,4],[4,1,0],[4,2,0],[0,4,0],[2,4,0],[4,0,1],[4,3,1],[1,4,1]]]

def masks : Fin 6 → Nat := ![2058,539,275,130,74,34]

def sumDisplacement (j : Fin 6) : QuadraticForm (ZMod 2) M22TripleCover.BinarySpace :=
  ((identityWords j).map displacement).sum

theorem displacement_vector (l : List (Fin 5)) (n : Nat) :
    displacement l (vector n) = quadratic (vector (n ^^^ wordPacked l n)) := by
  change quadratic (vector n + binaryAction (word l) (vector n)) = _
  rw [word_vector,← vector_xor]
  rfl

theorem sumDisplacement_vector (j : Fin 6) (n : Nat) :
    sumDisplacement j (vector n) =
      ((identityWords j).map (fun l => quadratic (vector (n ^^^ wordPacked l n)))).sum := by
  change QuadraticMap.evalAddMonoidHom (vector n)
    ((identityWords j).map displacement).sum = _
  rw [map_list_sum,List.map_map]
  exact congrArg List.sum (List.map_congr_left (fun l _ => displacement_vector l n))

theorem linear_identity (k : Fin 6) : sumDisplacement k = QuadraticMap.linMulLin (linear (masks k)) (linear (masks k)) := by
  apply quadratic_ext
  · intro i
    rw [sumDisplacement_vector]
    simp only [quadratic_vector]
    revert k i
    decide +kernel
  · intro i j
    rw [← vector_xor,sumDisplacement_vector]
    simp only [quadratic_vector]
    revert k i j
    decide +kernel

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.Native
