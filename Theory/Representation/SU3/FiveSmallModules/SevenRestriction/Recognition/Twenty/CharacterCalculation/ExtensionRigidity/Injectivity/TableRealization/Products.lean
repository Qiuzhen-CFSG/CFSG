module
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.TableRealization.ProductData
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.TableRealization.Marking
public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.CycleSimplicity.Arithmetic

/-!
# Checked group and module products for the nine Bruhat terms

Each of the 69 nodes is checked both in the actual three-dimensional table
matrices and in the packed binary quotient matrices. The general product
soundness theorem identifies both evaluations under any representation with
the two prescribed actor matrices. Small final checks match the literal
left root–torus and right root actors, with their exact center enumeration.
Scalar extension preserves the entire calculation.

Source: Huppert II.10.12; the retained coefficient and coset data, described
in source/README.md. The generator supplies witnesses only. Declarations are
checked sequentially to bound memory without changing Lean's thread count.
-/

set_option Elab.async false

@[expose] public section
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.InvolutionConjugateBounds.Five.Embedding
open Matrix Thompson.BinaryMatrix
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.TableRealization.ProductCertificate
open Degrees.TrivialCalculation.MiddleFactors
open Realization

def BinaryStep (n : Nat) : Prop :=
  match operations[n]! with
  | .one => ∀ r : Fin 20, (binaryRows[n]!)[r.val]! = 2 ^ r.val
  | .actor a => binaryRows[n]! = factorRows20 a
  | .mul i j => i < n ∧ j < n ∧
      ∀ r : Fin 20, rowProduct (binaryRows[i]!)[r.val]! binaryRows[j]! 20 = (binaryRows[n]!)[r.val]!
instance (n : Nat) : Decidable (BinaryStep n) := by
  unfold BinaryStep
  split <;> infer_instance

theorem BinaryStep.sound (n : Nat) (h : BinaryStep n) :
    Step factor20 binaryValue operations n := by
  cases he : operations[n]! with
  | one =>
    simp only [BinaryStep, Step, he] at h ⊢
    ext i j
    change bit (binaryRows[n]!)[i.val]! j.val = _
    rw [h i]
    simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]
  | actor a =>
    simp only [BinaryStep, Step, he] at h ⊢
    change decode 20 binaryRows[n]! = decode 20 (factorRows20 a)
    rw [h]
  | mul i j =>
    simp only [BinaryStep, Step, he] at h ⊢
    exact ⟨h.1, h.2.1, decode_mul 20 _ _ _ h.2.2⟩

private theorem binary_step_0 : BinaryStep 0 := by decide +kernel
private theorem group_step_0 : Step tableActorMatrix groupValue operations 0 := by decide +kernel
private theorem binary_step_1 : BinaryStep 1 := by rfl
private theorem group_step_1 : Step tableActorMatrix groupValue operations 1 := by decide +kernel
private theorem binary_step_2 : BinaryStep 2 := by rfl
private theorem group_step_2 : Step tableActorMatrix groupValue operations 2 := by decide +kernel
private theorem binary_step_3 : BinaryStep 3 := by decide +kernel
private theorem group_step_3 : Step tableActorMatrix groupValue operations 3 := by decide +kernel
private theorem binary_step_4 : BinaryStep 4 := by decide +kernel
private theorem group_step_4 : Step tableActorMatrix groupValue operations 4 := by decide +kernel
private theorem binary_step_5 : BinaryStep 5 := by decide +kernel
private theorem group_step_5 : Step tableActorMatrix groupValue operations 5 := by decide +kernel
private theorem binary_step_6 : BinaryStep 6 := by decide +kernel
private theorem group_step_6 : Step tableActorMatrix groupValue operations 6 := by decide +kernel
private theorem binary_step_7 : BinaryStep 7 := by decide +kernel
private theorem group_step_7 : Step tableActorMatrix groupValue operations 7 := by decide +kernel
private theorem binary_step_8 : BinaryStep 8 := by decide +kernel
private theorem group_step_8 : Step tableActorMatrix groupValue operations 8 := by decide +kernel
private theorem binary_step_9 : BinaryStep 9 := by decide +kernel
private theorem group_step_9 : Step tableActorMatrix groupValue operations 9 := by decide +kernel
private theorem binary_step_10 : BinaryStep 10 := by decide +kernel
private theorem group_step_10 : Step tableActorMatrix groupValue operations 10 := by decide +kernel
private theorem binary_step_11 : BinaryStep 11 := by decide +kernel
private theorem group_step_11 : Step tableActorMatrix groupValue operations 11 := by decide +kernel
private theorem binary_step_12 : BinaryStep 12 := by decide +kernel
private theorem group_step_12 : Step tableActorMatrix groupValue operations 12 := by decide +kernel
private theorem binary_step_13 : BinaryStep 13 := by decide +kernel
private theorem group_step_13 : Step tableActorMatrix groupValue operations 13 := by decide +kernel
private theorem binary_step_14 : BinaryStep 14 := by decide +kernel
private theorem group_step_14 : Step tableActorMatrix groupValue operations 14 := by decide +kernel
private theorem binary_step_15 : BinaryStep 15 := by decide +kernel
private theorem group_step_15 : Step tableActorMatrix groupValue operations 15 := by decide +kernel
private theorem binary_step_16 : BinaryStep 16 := by decide +kernel
private theorem group_step_16 : Step tableActorMatrix groupValue operations 16 := by decide +kernel
private theorem binary_step_17 : BinaryStep 17 := by decide +kernel
private theorem group_step_17 : Step tableActorMatrix groupValue operations 17 := by decide +kernel
private theorem binary_step_18 : BinaryStep 18 := by decide +kernel
private theorem group_step_18 : Step tableActorMatrix groupValue operations 18 := by decide +kernel
private theorem binary_step_19 : BinaryStep 19 := by decide +kernel
private theorem group_step_19 : Step tableActorMatrix groupValue operations 19 := by decide +kernel
private theorem binary_step_20 : BinaryStep 20 := by decide +kernel
private theorem group_step_20 : Step tableActorMatrix groupValue operations 20 := by decide +kernel
private theorem binary_step_21 : BinaryStep 21 := by decide +kernel
private theorem group_step_21 : Step tableActorMatrix groupValue operations 21 := by decide +kernel
private theorem binary_step_22 : BinaryStep 22 := by decide +kernel
private theorem group_step_22 : Step tableActorMatrix groupValue operations 22 := by decide +kernel
private theorem binary_step_23 : BinaryStep 23 := by decide +kernel
private theorem group_step_23 : Step tableActorMatrix groupValue operations 23 := by decide +kernel
private theorem binary_step_24 : BinaryStep 24 := by decide +kernel
private theorem group_step_24 : Step tableActorMatrix groupValue operations 24 := by decide +kernel
private theorem binary_step_25 : BinaryStep 25 := by decide +kernel
private theorem group_step_25 : Step tableActorMatrix groupValue operations 25 := by decide +kernel
private theorem binary_step_26 : BinaryStep 26 := by decide +kernel
private theorem group_step_26 : Step tableActorMatrix groupValue operations 26 := by decide +kernel
private theorem binary_step_27 : BinaryStep 27 := by decide +kernel
private theorem group_step_27 : Step tableActorMatrix groupValue operations 27 := by decide +kernel
private theorem binary_step_28 : BinaryStep 28 := by decide +kernel
private theorem group_step_28 : Step tableActorMatrix groupValue operations 28 := by decide +kernel
private theorem binary_step_29 : BinaryStep 29 := by decide +kernel
private theorem group_step_29 : Step tableActorMatrix groupValue operations 29 := by decide +kernel
private theorem binary_step_30 : BinaryStep 30 := by decide +kernel
private theorem group_step_30 : Step tableActorMatrix groupValue operations 30 := by decide +kernel
private theorem binary_step_31 : BinaryStep 31 := by decide +kernel
private theorem group_step_31 : Step tableActorMatrix groupValue operations 31 := by decide +kernel
private theorem binary_step_32 : BinaryStep 32 := by decide +kernel
private theorem group_step_32 : Step tableActorMatrix groupValue operations 32 := by decide +kernel
private theorem binary_step_33 : BinaryStep 33 := by decide +kernel
private theorem group_step_33 : Step tableActorMatrix groupValue operations 33 := by decide +kernel
private theorem binary_step_34 : BinaryStep 34 := by decide +kernel
private theorem group_step_34 : Step tableActorMatrix groupValue operations 34 := by decide +kernel
private theorem binary_step_35 : BinaryStep 35 := by decide +kernel
private theorem group_step_35 : Step tableActorMatrix groupValue operations 35 := by decide +kernel
private theorem binary_step_36 : BinaryStep 36 := by decide +kernel
private theorem group_step_36 : Step tableActorMatrix groupValue operations 36 := by decide +kernel
private theorem binary_step_37 : BinaryStep 37 := by decide +kernel
private theorem group_step_37 : Step tableActorMatrix groupValue operations 37 := by decide +kernel
private theorem binary_step_38 : BinaryStep 38 := by decide +kernel
private theorem group_step_38 : Step tableActorMatrix groupValue operations 38 := by decide +kernel
private theorem binary_step_39 : BinaryStep 39 := by decide +kernel
private theorem group_step_39 : Step tableActorMatrix groupValue operations 39 := by decide +kernel
private theorem binary_step_40 : BinaryStep 40 := by decide +kernel
private theorem group_step_40 : Step tableActorMatrix groupValue operations 40 := by decide +kernel
private theorem binary_step_41 : BinaryStep 41 := by decide +kernel
private theorem group_step_41 : Step tableActorMatrix groupValue operations 41 := by decide +kernel
private theorem binary_step_42 : BinaryStep 42 := by decide +kernel
private theorem group_step_42 : Step tableActorMatrix groupValue operations 42 := by decide +kernel
private theorem binary_step_43 : BinaryStep 43 := by decide +kernel
private theorem group_step_43 : Step tableActorMatrix groupValue operations 43 := by decide +kernel
private theorem binary_step_44 : BinaryStep 44 := by decide +kernel
private theorem group_step_44 : Step tableActorMatrix groupValue operations 44 := by decide +kernel
private theorem binary_step_45 : BinaryStep 45 := by decide +kernel
private theorem group_step_45 : Step tableActorMatrix groupValue operations 45 := by decide +kernel
private theorem binary_step_46 : BinaryStep 46 := by decide +kernel
private theorem group_step_46 : Step tableActorMatrix groupValue operations 46 := by decide +kernel
private theorem binary_step_47 : BinaryStep 47 := by decide +kernel
private theorem group_step_47 : Step tableActorMatrix groupValue operations 47 := by decide +kernel
private theorem binary_step_48 : BinaryStep 48 := by decide +kernel
private theorem group_step_48 : Step tableActorMatrix groupValue operations 48 := by decide +kernel
private theorem binary_step_49 : BinaryStep 49 := by decide +kernel
private theorem group_step_49 : Step tableActorMatrix groupValue operations 49 := by decide +kernel
private theorem binary_step_50 : BinaryStep 50 := by decide +kernel
private theorem group_step_50 : Step tableActorMatrix groupValue operations 50 := by decide +kernel
private theorem binary_step_51 : BinaryStep 51 := by decide +kernel
private theorem group_step_51 : Step tableActorMatrix groupValue operations 51 := by decide +kernel
private theorem binary_step_52 : BinaryStep 52 := by decide +kernel
private theorem group_step_52 : Step tableActorMatrix groupValue operations 52 := by decide +kernel
private theorem binary_step_53 : BinaryStep 53 := by decide +kernel
private theorem group_step_53 : Step tableActorMatrix groupValue operations 53 := by decide +kernel
private theorem binary_step_54 : BinaryStep 54 := by decide +kernel
private theorem group_step_54 : Step tableActorMatrix groupValue operations 54 := by decide +kernel
private theorem binary_step_55 : BinaryStep 55 := by decide +kernel
private theorem group_step_55 : Step tableActorMatrix groupValue operations 55 := by decide +kernel
private theorem binary_step_56 : BinaryStep 56 := by decide +kernel
private theorem group_step_56 : Step tableActorMatrix groupValue operations 56 := by decide +kernel
private theorem binary_step_57 : BinaryStep 57 := by decide +kernel
private theorem group_step_57 : Step tableActorMatrix groupValue operations 57 := by decide +kernel
private theorem binary_step_58 : BinaryStep 58 := by decide +kernel
private theorem group_step_58 : Step tableActorMatrix groupValue operations 58 := by decide +kernel
private theorem binary_step_59 : BinaryStep 59 := by decide +kernel
private theorem group_step_59 : Step tableActorMatrix groupValue operations 59 := by decide +kernel
private theorem binary_step_60 : BinaryStep 60 := by decide +kernel
private theorem group_step_60 : Step tableActorMatrix groupValue operations 60 := by decide +kernel
private theorem binary_step_61 : BinaryStep 61 := by decide +kernel
private theorem group_step_61 : Step tableActorMatrix groupValue operations 61 := by decide +kernel
private theorem binary_step_62 : BinaryStep 62 := by decide +kernel
private theorem group_step_62 : Step tableActorMatrix groupValue operations 62 := by decide +kernel
private theorem binary_step_63 : BinaryStep 63 := by decide +kernel
private theorem group_step_63 : Step tableActorMatrix groupValue operations 63 := by decide +kernel
private theorem binary_step_64 : BinaryStep 64 := by decide +kernel
private theorem group_step_64 : Step tableActorMatrix groupValue operations 64 := by decide +kernel
private theorem binary_step_65 : BinaryStep 65 := by decide +kernel
private theorem group_step_65 : Step tableActorMatrix groupValue operations 65 := by decide +kernel
private theorem binary_step_66 : BinaryStep 66 := by decide +kernel
private theorem group_step_66 : Step tableActorMatrix groupValue operations 66 := by decide +kernel
private theorem binary_step_67 : BinaryStep 67 := by decide +kernel
private theorem group_step_67 : Step tableActorMatrix groupValue operations 67 := by decide +kernel
private theorem binary_step_68 : BinaryStep 68 := by decide +kernel
private theorem group_step_68 : Step tableActorMatrix groupValue operations 68 := by decide +kernel

private theorem binary_steps_raw (n : Fin 69) : BinaryStep n.val := by
  fin_cases n
  · exact binary_step_0
  · exact binary_step_1
  · exact binary_step_2
  · exact binary_step_3
  · exact binary_step_4
  · exact binary_step_5
  · exact binary_step_6
  · exact binary_step_7
  · exact binary_step_8
  · exact binary_step_9
  · exact binary_step_10
  · exact binary_step_11
  · exact binary_step_12
  · exact binary_step_13
  · exact binary_step_14
  · exact binary_step_15
  · exact binary_step_16
  · exact binary_step_17
  · exact binary_step_18
  · exact binary_step_19
  · exact binary_step_20
  · exact binary_step_21
  · exact binary_step_22
  · exact binary_step_23
  · exact binary_step_24
  · exact binary_step_25
  · exact binary_step_26
  · exact binary_step_27
  · exact binary_step_28
  · exact binary_step_29
  · exact binary_step_30
  · exact binary_step_31
  · exact binary_step_32
  · exact binary_step_33
  · exact binary_step_34
  · exact binary_step_35
  · exact binary_step_36
  · exact binary_step_37
  · exact binary_step_38
  · exact binary_step_39
  · exact binary_step_40
  · exact binary_step_41
  · exact binary_step_42
  · exact binary_step_43
  · exact binary_step_44
  · exact binary_step_45
  · exact binary_step_46
  · exact binary_step_47
  · exact binary_step_48
  · exact binary_step_49
  · exact binary_step_50
  · exact binary_step_51
  · exact binary_step_52
  · exact binary_step_53
  · exact binary_step_54
  · exact binary_step_55
  · exact binary_step_56
  · exact binary_step_57
  · exact binary_step_58
  · exact binary_step_59
  · exact binary_step_60
  · exact binary_step_61
  · exact binary_step_62
  · exact binary_step_63
  · exact binary_step_64
  · exact binary_step_65
  · exact binary_step_66
  · exact binary_step_67
  · exact binary_step_68

theorem binary_steps (n : Fin 69) : Step factor20 binaryValue operations n.val :=
  (binary_steps_raw n).sound n.val

theorem group_steps (n : Fin 69) : Step tableActorMatrix groupValue operations n.val := by
  fin_cases n
  · exact group_step_0
  · exact group_step_1
  · exact group_step_2
  · exact group_step_3
  · exact group_step_4
  · exact group_step_5
  · exact group_step_6
  · exact group_step_7
  · exact group_step_8
  · exact group_step_9
  · exact group_step_10
  · exact group_step_11
  · exact group_step_12
  · exact group_step_13
  · exact group_step_14
  · exact group_step_15
  · exact group_step_16
  · exact group_step_17
  · exact group_step_18
  · exact group_step_19
  · exact group_step_20
  · exact group_step_21
  · exact group_step_22
  · exact group_step_23
  · exact group_step_24
  · exact group_step_25
  · exact group_step_26
  · exact group_step_27
  · exact group_step_28
  · exact group_step_29
  · exact group_step_30
  · exact group_step_31
  · exact group_step_32
  · exact group_step_33
  · exact group_step_34
  · exact group_step_35
  · exact group_step_36
  · exact group_step_37
  · exact group_step_38
  · exact group_step_39
  · exact group_step_40
  · exact group_step_41
  · exact group_step_42
  · exact group_step_43
  · exact group_step_44
  · exact group_step_45
  · exact group_step_46
  · exact group_step_47
  · exact group_step_48
  · exact group_step_49
  · exact group_step_50
  · exact group_step_51
  · exact group_step_52
  · exact group_step_53
  · exact group_step_54
  · exact group_step_55
  · exact group_step_56
  · exact group_step_57
  · exact group_step_58
  · exact group_step_59
  · exact group_step_60
  · exact group_step_61
  · exact group_step_62
  · exact group_step_63
  · exact group_step_64
  · exact group_step_65
  · exact group_step_66
  · exact group_step_67
  · exact group_step_68

/-- The actual matrix homomorphism on the standard SU carrier. -/
def groupMatrix : TableGroup →* Matrix (Fin 3) (Fin 3) F25 where
  toFun g := g.val.val
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Each program node is a genuine group element. -/
def element (n : Nat) : TableGroup := eval tableActor operations n

theorem element_matrix (n : Nat) (hn : n < 69) : groupMatrix (element n) = groupValue n :=
  map_eval tableActor groupMatrix groupValue operations 69 group_steps n hn

theorem leftIndex_lt (s : Fin 2) (c : Fin 5) : leftIndex s c < 69 := by
  revert s c; decide +kernel

theorem rightIndex_lt (s : Fin 2) (c : Fin 5) : rightIndex s c < 69 := by
  revert s c; decide +kernel

/-- Literal left Bruhat matrices, including the prescribed torus convention. -/
theorem left_marked_matrix : ∀ (s : Fin 2) (c : Fin 5)
    (hz : (marked s c).val.2 ≠ 0),
    groupValue (leftIndex s c) =
      hermitianUnipotentMatrix form (hermitianBruhatLeft form (marked s c) hz) *
        hermitianTorusMatrix form (Units.mk0 (marked s c).val.2 hz) := by
  decide +kernel

/-- Literal right Bruhat matrices in the same marked coordinates. -/
theorem right_marked_matrix : ∀ (s : Fin 2) (c : Fin 5)
    (hz : (marked s c).val.2 ≠ 0),
    groupValue (rightIndex s c) =
      hermitianUnipotentMatrix form (hermitianBruhatRight form (marked s c) hz) := by
  decide +kernel

theorem left_element (s : Fin 2) (c : Fin 5) (hz : (marked s c).val.2 ≠ 0) :
    element (leftIndex s c) =
      hermitianUnipotentSU form rfl (hermitianBruhatLeft form (marked s c) hz) *
        hermitianTorusSU form rfl (Units.mk0 (marked s c).val.2 hz) := by
  apply Subtype.ext
  apply Units.ext
  exact (element_matrix _ (leftIndex_lt s c)).trans (left_marked_matrix s c hz)

theorem right_element (s : Fin 2) (c : Fin 5) (hz : (marked s c).val.2 ≠ 0) :
    element (rightIndex s c) =
      hermitianUnipotentSU form rfl (hermitianBruhatRight form (marked s c) hz) := by
  apply Subtype.ext
  apply Units.ext
  exact (element_matrix _ (rightIndex_lt s c)).trans (right_marked_matrix s c hz)

theorem left_binary_matrix : ∀ (s : Fin 2) (c : Fin 5),
    (marked s c).val.2 ≠ 0 →
    binaryValue (leftIndex s c) = Certificate.matrix (K := ZMod 2) (Certificate.Data.leftRows s c) := by
  decide +kernel

theorem right_binary_matrix : ∀ (s : Fin 2) (c : Fin 5),
    (marked s c).val.2 ≠ 0 →
    binaryValue (rightIndex s c) = Certificate.matrix (K := ZMod 2) (Certificate.Data.rightRows s c) := by
  decide +kernel

variable (K : Type*) [Field K] [CharP K 2]
theorem cast_certificate (rows : Fin 20 → Nat) :
    CycleCertificate.castMatrix K (Certificate.matrix (K := ZMod 2) rows) =
      Certificate.matrix (K := K) rows := by
  ext i j
  change (ZMod.castHom (dvd_refl 2) K) (if (rows i).testBit j.val then 1 else 0) =
    (if (rows i).testBit j.val then 1 else 0)
  split <;> simp

/-- Every action with the two proved actor matrices has the checked images. -/
theorem element_image (f : TableGroup →* Matrix (Fin 20) (Fin 20) K)
    (ha : ∀ j, f (tableActor j) = CycleCertificate.castMatrix K (factor20 j))
    (n : Nat) (hn : n < 69) : f (element n) = CycleCertificate.castMatrix K (binaryValue n) := by
  apply map_eval tableActor f _ operations 69 _ n hn
  intro k
  simp_rw [ha]
  exact Step.map (CycleCertificate.castMatrix K).toMonoidHom
    factor20 binaryValue operations k.val (binary_steps k)

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.TableRealization.ProductCertificate
