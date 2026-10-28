module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeStabilizers

/-!
# Checked five-involution data in the second native stabilizer

Words in the genuine 3.M₂₂.2 matrix generators construct five elements and
sixteen distinct commuting square-one elements. Two additional words conjugate
the five elements as a 5-cycle and a transposition. Each equality is checked on
twelve binary basis vectors. Packed columns avoid repeated large matrix-word
reductions; the columns themselves are verified against the native generators.

These certificates supply the kernel and quotient argument for the second
stabilizer in Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), (4.2), p.597, DOI 10.1007/BF01232280. Generator attribution
and licensing are inherited from the imported M₂₂ triple-cover matrix model.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open M22TripleCover.Ambient
open Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.SecondStabilizer.Certificates
abbrev A : actionGroup := coverInclusion coreGeneratorA
abbrev B : actionGroup := coverInclusion coreGeneratorB

def generators : Fin 4 → actionGroup := ![
  (A * B * A * B)⁻¹ * B * (A * B * A * B),
  (A * A * A * B * A)⁻¹ * B * (A * A * A * B * A),
  (A * A * A * B * A * A)⁻¹ * B * (A * A * A * B * A * A),
  outerElement]

def word (l : List (Fin 4)) : actionGroup := (l.map generators).prod

def five : Fin 5 → actionGroup := ![
  word [1,0,1,0], word [2,1,0,1,0,2], word [0,2,1,0,1,0,2,0],
  word [2,0,3,2,1,2,3,0], word [3,2,1,2,3,0,2,0]]

def columns : Fin 4 → Fin 12 → Nat := ![
  ![3604,756,3303,2876,2514,2836,64,959,1822,3548,1855,4055],
  ![3274,3453,432,2703,145,3423,3518,3147,385,2355,2558,4088],
  ![3038,1325,3828,1919,3269,3317,536,1490,856,3066,3578,3850],
  ![2054,5,2052,2080,2112,2056,2064,512,3072,128,2304,2048]]

def nativeGenerators : Fin 5 → actionGroup := ![A,B,A⁻¹,B⁻¹,outerElement]

def nativeColumns : Fin 5 → Fin 12 → Nat := ![
  VectorOrbits.columnsA, VectorOrbits.columnsB,
  ![568,1044,81,1184,1792,547,65,96,64,544,2144,1088],
  VectorOrbits.columnsB,
  ![2054,5,2052,2080,2112,2056,2064,512,3072,128,2304,2048]]

theorem nativeGenerators_action (j : Fin 5) : binaryAction (nativeGenerators j) =
    VectorOrbits.columnMap (nativeColumns j) := by
  apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
  intro i
  simp only [Pi.basisFun_apply]
  revert j i
  decide +kernel

def nativeWord (l : List (Fin 5)) : actionGroup := (l.map nativeGenerators).prod

def nativePacked (l : List (Fin 5)) (n : Nat) : Nat :=
  l.foldr (fun j v => VectorOrbits.packedAction (nativeColumns j) v) n

theorem nativeWord_vector (l : List (Fin 5)) (n : Nat) :
    binaryAction (nativeWord l) (VectorOrbits.vector n) =
      VectorOrbits.vector (nativePacked l n) := by
  induction l with
  | nil => change binaryAction 1 _ = _; rw [map_one]; rfl
  | cons j l ih =>
    change binaryAction (nativeGenerators j * nativeWord l) _ = _
    rw [map_mul,Module.End.mul_apply,ih,nativeGenerators_action,
      ← VectorOrbits.vector_packedAction]
    rfl

def generatorWords : Fin 4 → List (Fin 5) := ![
  [3,2,3,2,1,0,1,0,1], [2,3,2,2,2,1,0,0,0,1,0],
  [2,2,3,2,2,2,1,0,0,0,1,0,0], [4]]

theorem generator_word (j : Fin 4) : generators j = nativeWord (generatorWords j) := by
  fin_cases j <;> simp [generators,nativeWord,nativeGenerators,generatorWords,mul_inv_rev,mul_assoc]

theorem basis_vector (i : Fin 12) :
    Pi.single i (1 : ZMod 2) = VectorOrbits.vector (2 ^ i.val) := by
  revert i
  decide +kernel

theorem generators_action (j : Fin 4) : binaryAction (generators j) =
    VectorOrbits.columnMap (columns j) := by
  apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
  intro i
  simp only [Pi.basisFun_apply,basis_vector]
  rw [generator_word,nativeWord_vector,← VectorOrbits.vector_packedAction]
  revert j i
  decide +kernel

def wordPacked (l : List (Fin 4)) (n : Nat) : Nat :=
  l.foldr (fun j v => VectorOrbits.packedAction (columns j) v) n

theorem word_vector (l : List (Fin 4)) (n : Nat) :
    binaryAction (word l) (VectorOrbits.vector n) = VectorOrbits.vector (wordPacked l n) := by
  induction l with
  | nil => change binaryAction 1 _ = _; rw [map_one]; rfl
  | cons j l ih =>
    change binaryAction (generators j * word l) _ = _
    rw [map_mul,Module.End.mul_apply,ih,generators_action,← VectorOrbits.vector_packedAction]
    rfl

def fiveWords : Fin 5 → List (Fin 4) := ![
  [1,0,1,0], [2,1,0,1,0,2], [0,2,1,0,1,0,2,0],
  [2,0,3,2,1,2,3,0], [3,2,1,2,3,0,2,0]]

def fiveColumns : Fin 5 → Fin 12 → Nat := ![
  ![3274,5,3272,2876,1545,2836,1630,3147,3114,2355,3797,4088],
  ![2771,1503,3851,3262,1482,2802,1571,2540,3599,3343,2225,2055],
  ![1095,5,1093,1930,16,2802,3351,2642,2065,2261,3345,1367],
  ![2188,2733,550,2778,591,90,536,2642,381,2261,3797,687],
  ![2771,3952,1444,2778,396,2926,3890,1319,2633,1596,416,2055]]

theorem five_action (j : Fin 5) : binaryAction (five j) =
    VectorOrbits.columnMap (fiveColumns j) := by
  apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
  intro i
  simp only [Pi.basisFun_apply, basis_vector]
  have hf : five j = word (fiveWords j) := by fin_cases j <;> rfl
  rw [hf, word_vector, ← VectorOrbits.vector_packedAction]
  revert j i
  decide +kernel

theorem five_vector (j : Fin 5) (n : Nat) :
    binaryAction (five j) (VectorOrbits.vector n) =
      VectorOrbits.vector (VectorOrbits.packedAction (fiveColumns j) n) := by
  rw [five_action,VectorOrbits.vector_packedAction]

theorem action_injective : Function.Injective binaryAction :=
  Matrix.toLinAlgEquiv'.injective.comp (Units.val_injective.comp Subtype.val_injective)

theorem eq_of_basis (g h : actionGroup)
    (he : ∀ i : Fin 12, binaryAction g (VectorOrbits.vector (2 ^ i.val)) =
      binaryAction h (VectorOrbits.vector (2 ^ i.val))) : g = h := by
  apply action_injective
  apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
  intro i
  simpa only [Pi.basisFun_apply,basis_vector] using he i

theorem five_injective : Function.Injective five := by
  intro i j he
  have hh := congrArg (fun g => binaryAction g (VectorOrbits.vector 3)) he
  simp only [five_vector] at hh
  have hf : Function.Injective (fun j : Fin 5 =>
      VectorOrbits.vector (VectorOrbits.packedAction (fiveColumns j) 3)) := by
    decide +kernel
  exact hf hh

def frameWord (l : List (Fin 5)) : actionGroup := (l.map five).prod

def framePacked (l : List (Fin 5)) (n : Nat) : Nat :=
  l.foldr (fun j v => VectorOrbits.packedAction (fiveColumns j) v) n

theorem frame_vector (l : List (Fin 5)) (n : Nat) :
    binaryAction (frameWord l) (VectorOrbits.vector n) =
      VectorOrbits.vector (framePacked l n) := by
  induction l with
  | nil => change binaryAction 1 _ = _; rw [map_one]; rfl
  | cons j l ih =>
    change binaryAction (five j * frameWord l) _ = _
    rw [map_mul,Module.End.mul_apply,ih,five_vector]
    rfl

def kernelWord (i : Fin 16) : List (Fin 5) :=
  [0,1,2,3].filter (fun j => i.val.testBit j.val)

def kernelElement (i : Fin 16) : actionGroup := frameWord (kernelWord i)

theorem kernel_injective : Function.Injective kernelElement := by
  intro i j he
  have hh := congrArg (fun g => binaryAction g (VectorOrbits.vector 3)) he
  simp only [kernelElement,frame_vector] at hh
  have hf : Function.Injective (fun i : Fin 16 =>
      VectorOrbits.vector (framePacked (kernelWord i) 3)) := by
    decide +kernel
  exact hf hh

theorem five_sq (j : Fin 5) : five j ^ 2 = 1 := by
  apply eq_of_basis
  intro i
  simp only [pow_two,map_mul,Module.End.mul_apply,map_one,Module.End.one_apply,five_vector]
  revert j i
  decide +kernel

theorem five_commute (j k : Fin 5) : Commute (five j) (five k) := by
  change five j * five k = five k * five j
  apply eq_of_basis
  intro i
  simp only [map_mul,Module.End.mul_apply,five_vector]
  revert j k i
  decide +kernel

theorem frame_commute (l : List (Fin 5)) (j : Fin 5) : Commute (frameWord l) (five j) := by
  apply Commute.list_prod_left
  intro x hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  exact five_commute i j

theorem frame_sq (l : List (Fin 5)) : frameWord l ^ 2 = 1 := by
  induction l with
  | nil => change (1 : actionGroup)^2 = 1; exact one_pow _
  | cons j l ih =>
    change (five j * frameWord l)^2 = 1
    rw [(frame_commute l j).symm.mul_pow,five_sq,ih,one_mul]

theorem kernel_sq (j : Fin 16) : kernelElement j ^ 2 = 1 := frame_sq _

theorem kernel_comm (j : Fin 16) (k : Fin 5) :
    kernelElement j * five k = five k * kernelElement j := (frame_commute _ k).eq

theorem cycle_conj (j : Fin 5) :
    word [2,1] * five j * (word [2,1])⁻¹ =
      five (List.formPerm [0,1,2,3,4] j) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply eq_of_basis
  intro i
  simp only [map_mul,Module.End.mul_apply,word_vector,five_vector]
  revert j i
  decide +kernel

theorem swap_conj (j : Fin 5) :
    word [0,2,3,2,0] * five j * (word [0,2,3,2,0])⁻¹ =
      five (Equiv.swap 0 1 j) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply eq_of_basis
  intro i
  simp only [map_mul,Module.End.mul_apply,word_vector,five_vector]
  revert j i
  decide +kernel

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.SecondStabilizer.Certificates
end
