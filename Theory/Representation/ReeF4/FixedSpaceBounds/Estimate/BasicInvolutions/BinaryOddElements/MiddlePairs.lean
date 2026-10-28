module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusWeights

/-!
# Twenty disjoint moving-weight pairs in the larger basic F4 factors

For either highest weight `(1,b)` and each simple root i, the tables give
twenty distinct Weyl translates having i-th coroot coordinate one. Reflection
in i gives twenty further weights with coordinate minus one. Each pair
differs by exactly the i-th Cartan row, so a nontrivial i-th root character
moves at least one vector in each pair. The selected twenty weights are
still distinct and hence give twenty independent vectors in the displacement
space. All tables use kernel-checked integer calculations.

This proves the needed bound for every nonidentity coroot-torus parameter,
without any assertion about the exact dimensions of the larger modules or
any restriction on the order of the parameter.

Source: GLS3, Sections 1.8 and 1.14 and Definition 2.8.1(b). This supplies the
larger-weight cases that the degree-26 calculation in Guralnick--Malle II,
Lemma 8.8, does not cover.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem

open ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle

namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements

private def words0_0 : Fin 20 → List (Fin 4) :=
  ![[2, 1],
  [2, 1, 2],
  [2, 1, 3],
  [2, 1, 2, 3],
  [2, 1, 3, 2],
  [2, 1, 2, 3, 2],
  [2, 1, 0, 3, 2, 1],
  [2, 1, 0, 2, 3, 2, 1],
  [2, 1, 0, 3, 2, 1, 2],
  [2, 1, 0, 2, 3, 2, 1, 2],
  [2, 1, 0, 3, 2, 1, 2, 3],
  [2, 1, 0, 2, 3, 2, 1, 2, 3],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 2],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 3],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 2, 3],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 3, 2],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2],
  [2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 1, 3, 2, 1],
  [2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 3, 2, 1]]

private def weights0_0 (n : Fin 20) := reflectWord (words0_0 n) ![0, 0, 1, 0]

private theorem injective0_0 : Function.Injective weights0_0 := by decide

private theorem coefficient0_0 : ∀ n, weights0_0 n 0 = 1 := by decide

private def words0_1 : Fin 20 → List (Fin 4) :=
  ![[2],
  [2, 3],
  [2, 1, 0, 2],
  [2, 1, 3, 2],
  [2, 1, 0, 2, 3],
  [2, 1, 2, 3, 2],
  [2, 1, 3, 2, 1, 0],
  [2, 1, 2, 3, 2, 1, 0],
  [2, 1, 0, 2, 3, 2, 1, 2],
  [2, 1, 0, 3, 2, 1, 0, 2],
  [2, 1, 0, 2, 3, 2, 1, 2, 3],
  [2, 1, 0, 3, 2, 1, 0, 2, 3],
  [2, 1, 0, 2, 1, 3, 2, 1, 0, 2],
  [2, 1, 2, 3, 2, 1, 0, 2, 1, 2],
  [2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 3],
  [2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 3, 2],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2],
  [2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 3, 2],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 3, 2, 1, 0]]

private def weights0_1 (n : Fin 20) := reflectWord (words0_1 n) ![0, 0, 1, 0]

private theorem injective0_1 : Function.Injective weights0_1 := by decide

private theorem coefficient0_1 : ∀ n, weights0_1 n 1 = 1 := by decide

private def words0_2 : Fin 20 → List (Fin 4) :=
  ![[],
  [2, 1],
  [2, 1, 0],
  [2, 1, 2, 3],
  [2, 1, 0, 2, 1],
  [2, 1, 0, 2, 3],
  [2, 1, 2, 3, 2, 1],
  [2, 1, 2, 3, 2, 1, 0],
  [2, 1, 0, 2, 1, 3, 2, 1],
  [2, 1, 0, 3, 2, 1, 2, 3],
  [2, 1, 0, 2, 1, 3, 2, 1, 0],
  [2, 1, 0, 3, 2, 1, 0, 2, 3],
  [2, 1, 0, 2, 1, 3, 2, 1, 2, 3],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1],
  [2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 1],
  [2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 3],
  [2, 1, 0, 3, 2, 1, 0, 2, 1, 3, 2, 1],
  [2, 1, 0, 3, 2, 1, 0, 2, 1, 3, 2, 1, 0],
  [2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3],
  [2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 1, 3, 2, 1]]

private def weights0_2 (n : Fin 20) := reflectWord (words0_2 n) ![0, 0, 1, 0]

private theorem injective0_2 : Function.Injective weights0_2 := by decide

private theorem coefficient0_2 : ∀ n, weights0_2 n 2 = 1 := by decide

private def words0_3 : Fin 20 → List (Fin 4) :=
  ![[2],
  [2, 1],
  [2, 1, 0],
  [2, 1, 3, 2],
  [2, 1, 0, 3, 2],
  [2, 1, 3, 2, 1],
  [2, 1, 0, 3, 2, 1],
  [2, 1, 3, 2, 1, 0],
  [2, 1, 0, 2, 1, 3, 2],
  [2, 1, 0, 3, 2, 1, 0],
  [2, 1, 0, 2, 1, 3, 2, 1],
  [2, 1, 0, 2, 1, 3, 2, 1, 0],
  [2, 1, 0, 2, 1, 2, 3, 2, 1, 2],
  [2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2],
  [2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 3, 2],
  [2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 1, 3, 2],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 3, 2, 1],
  [2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 1, 3, 2, 1],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 3, 2, 1, 0]]

private def weights0_3 (n : Fin 20) := reflectWord (words0_3 n) ![0, 0, 1, 0]

private theorem injective0_3 : Function.Injective weights0_3 := by decide

private theorem coefficient0_3 : ∀ n, weights0_3 n 3 = 1 := by decide

private def words1_0 : Fin 20 → List (Fin 4) :=
  ![[2, 1],
  [2, 1, 2],
  [2, 1, 3],
  [2, 1, 2, 3],
  [2, 1, 3, 2],
  [2, 1, 2, 3, 2],
  [2, 3, 2, 1, 0, 2, 1],
  [2, 3, 2, 1, 0, 2, 1, 2],
  [2, 3, 2, 1, 0, 2, 1, 3],
  [2, 3, 2, 1, 0, 2, 1, 2, 3],
  [2, 3, 2, 1, 0, 2, 1, 3, 2],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1],
  [2, 3, 2, 1, 0, 2, 1, 2, 3, 2],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 2],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 3],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 2, 3],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 3, 2],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2],
  [2, 1, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1],
  [2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1]]

private def weights1_0 (n : Fin 20) := reflectWord (words1_0 n) ![0, 0, 1, 1]

private theorem injective1_0 : Function.Injective weights1_0 := by decide

private theorem coefficient1_0 : ∀ n, weights1_0 n 0 = 1 := by decide

private def words1_1 : Fin 20 → List (Fin 4) :=
  ![[2],
  [2, 3],
  [2, 1, 0, 2],
  [2, 1, 0, 2, 3],
  [2, 3, 2, 1, 2],
  [2, 1, 3, 2, 1, 0],
  [2, 3, 2, 1, 2, 3],
  [2, 1, 2, 3, 2, 1, 0],
  [2, 1, 0, 2, 3, 2, 1, 2],
  [2, 1, 0, 2, 3, 2, 1, 2, 3],
  [2, 1, 3, 2, 1, 0, 2, 1, 2],
  [2, 1, 2, 3, 2, 1, 0, 2, 1, 2],
  [2, 1, 3, 2, 1, 0, 2, 1, 2, 3],
  [2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3],
  [2, 3, 2, 1, 0, 2, 1, 3, 2, 1, 0],
  [2, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0],
  [2, 1, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 2],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 3, 2, 1, 0],
  [2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 2],
  [2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0]]

private def weights1_1 (n : Fin 20) := reflectWord (words1_1 n) ![0, 0, 1, 1]

private theorem injective1_1 : Function.Injective weights1_1 := by decide

private theorem coefficient1_1 : ∀ n, weights1_1 n 1 = 1 := by decide

private def words1_2 : Fin 20 → List (Fin 4) :=
  ![[],
  [2, 1],
  [2, 3],
  [2, 1, 0],
  [2, 1, 0, 2, 1],
  [2, 1, 3, 2, 1],
  [3, 2, 1, 2, 3],
  [2, 1, 3, 2, 1, 0],
  [3, 2, 1, 0, 2, 3],
  [2, 1, 3, 2, 1, 2, 3],
  [2, 1, 0, 3, 2, 1, 2, 3],
  [2, 1, 3, 2, 1, 0, 2, 3],
  [2, 1, 0, 3, 2, 1, 0, 2, 1],
  [2, 1, 0, 3, 2, 1, 0, 2, 3],
  [3, 2, 1, 0, 2, 1, 3, 2, 1],
  [2, 1, 0, 2, 1, 3, 2, 1, 2, 3],
  [3, 2, 1, 0, 2, 1, 3, 2, 1, 0],
  [2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 3],
  [2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3],
  [2, 1, 3, 2, 1, 0, 2, 1, 3, 2, 1]]

private def weights1_2 (n : Fin 20) := reflectWord (words1_2 n) ![0, 0, 1, 1]

private theorem injective1_2 : Function.Injective weights1_2 := by decide

private theorem coefficient1_2 : ∀ n, weights1_2 n 2 = 1 := by decide

private def words1_3 : Fin 20 → List (Fin 4) :=
  ![[],
  [3, 2],
  [3, 2, 1],
  [2, 1, 3, 2],
  [3, 2, 1, 0],
  [2, 1, 0, 3, 2],
  [2, 1, 3, 2, 1],
  [2, 1, 0, 3, 2, 1],
  [2, 1, 3, 2, 1, 0],
  [2, 1, 0, 2, 1, 3, 2],
  [2, 1, 0, 3, 2, 1, 0],
  [2, 1, 2, 3, 2, 1, 2],
  [2, 1, 0, 2, 1, 3, 2, 1],
  [2, 1, 2, 3, 2, 1, 0, 2],
  [2, 1, 0, 2, 1, 3, 2, 1, 0],
  [2, 1, 2, 3, 2, 1, 0, 2, 1],
  [2, 1, 0, 3, 2, 1, 0, 2, 1, 3, 2],
  [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 2],
  [2, 1, 0, 3, 2, 1, 0, 2, 1, 3, 2, 1],
  [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2]]

private def weights1_3 (n : Fin 20) := reflectWord (words1_3 n) ![0, 0, 1, 1]

private theorem injective1_3 : Function.Injective weights1_3 := by decide

private theorem coefficient1_3 : ∀ n, weights1_3 n 3 = 1 := by decide
end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements

namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements

open Theory.AlgebraicGroup.StandardRootSystem
open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle

private def middlePairWord : Fin 2 → Fin 4 → Fin 20 → List (Fin 4)
  | 0, 0 => words0_0
  | 0, 1 => words0_1
  | 0, 2 => words0_2
  | 0, 3 => words0_3
  | 1, 0 => words1_0
  | 1, 1 => words1_1
  | 1, 2 => words1_2
  | 1, 3 => words1_3

private def middlePairWeight (b : Fin 2) (i : Fin 4) (n : Fin 20) : CorootWeight :=
  reflectWord (middlePairWord b i n) ![0, 0, 1, (b.val : ℤ)]

private theorem middlePairWeight_injective (b : Fin 2) (i : Fin 4) :
    Function.Injective (middlePairWeight b i) := by
  fin_cases b <;> fin_cases i
  all_goals first
    | exact injective0_0 | exact injective0_1 | exact injective0_2 | exact injective0_3
    | exact injective1_0 | exact injective1_1 | exact injective1_2 | exact injective1_3

private theorem middlePairWeight_coordinate (b : Fin 2) (i : Fin 4) (n : Fin 20) :
    middlePairWeight b i n i = 1 := by
  fin_cases b <;> fin_cases i
  all_goals first
    | exact coefficient0_0 n | exact coefficient0_1 n
    | exact coefficient0_2 n | exact coefficient0_3 n
    | exact coefficient1_0 n | exact coefficient1_1 n
    | exact coefficient1_2 n | exact coefficient1_3 n

private theorem reflectWeight_involutive (i : Fin 4) :
    Function.Involutive (reflectWeight i) := by
  have hii : typeF4CartanMatrix i i = 2 := by fin_cases i <;> rfl
  intro μ
  funext j
  dsimp [reflectWeight]
  rw [hii]
  ring

variable {F : Type*} [Field F] [IsAlgClosed F]

theorem middle_torus_displacement (B : AlgebraicFactor F) (b : Fin 2)
    (hB : B.HasBasicHighestWeight (1, b)) (t : Fin 4 → Fˣ) (ht : t ≠ 1) :
    20 ≤ Module.finrank F (LinearMap.range
      ((B.action.action (corootTorusElement t) : Module.End F B.Space) - 1)) := by
  classical
  obtain ⟨i, hi⟩ := exists_nontrivial_rootCharacter t ht
  let μ : Fin 20 → CorootWeight := fun n =>
    if corootCharacter t (middlePairWeight b i n) = 1 then
      reflectWeight i (middlePairWeight b i n) else middlePairWeight b i n
  have hii : typeF4CartanMatrix i i = 2 := by fin_cases i <;> rfl
  have hinj : Function.Injective μ := by
    intro n m he
    dsimp only [μ] at he
    split_ifs at he with hn hm
    · exact middlePairWeight_injective b i ((reflectWeight_involutive i).injective he)
    · have hh := congrFun he i
      simp only [reflectWeight, middlePairWeight_coordinate, hii] at hh
      norm_num at hh
    · have hh := congrFun he i
      simp only [reflectWeight, middlePairWeight_coordinate, hii] at hh
      norm_num at hh
    · exact middlePairWeight_injective b i he
  have hbase (n : Fin 20) : ∃ v, IsCorootWeightVector B (middlePairWeight b i n) v := by
    have hcoeff : (fun j => (basicCoefficient (1, b) j : ℤ)) =
        ![0, 0, 1, (b.val : ℤ)] := by
      funext j
      fin_cases j <;> simp [basicCoefficient]
    simpa only [middlePairWeight, hcoeff] using
      highestWeight_word_occurs B (1, b) hB (middlePairWord b i n)
  have hocc (n : Fin 20) : ∃ v, IsCorootWeightVector B (μ n) v := by
    dsimp only [μ]
    split_ifs
    · obtain ⟨v, hv⟩ := hbase n
      exact ⟨_, hv.reflect i⟩
    · exact hbase n
  have hmove (n : Fin 20) : corootCharacter t (μ n) ≠ 1 := by
    dsimp only [μ]
    split_ifs with hn
    · have he : reflectWeight i (middlePairWeight b i n) =
          middlePairWeight b i n - typeF4CartanMatrix i := by
        funext j
        simp [reflectWeight, middlePairWeight_coordinate]
      rw [he, corootCharacter_sub, hn, one_div]
      exact fun h => hi (inv_eq_one.mp h)
    · exact hn
  simpa only [Fintype.card_fin] using
    displacement_ge_of_weights B t μ hinj hocc hmove

end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements
