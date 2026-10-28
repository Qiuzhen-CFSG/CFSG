module

public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.Max6Core.Maps

/-!
# Normality and the two-group property of the max6 seed

Five conjugates of x^5, where x and y are the unchanged ATLAS max6 generators,
provide a normal abelian two-subgroup. The numerical maps below are witnesses;
all identities are checked in Lean on the original degree-4060 carrier.

Source: Aschbacher--Smith, Theorem 0.1.2(5), printed p.4 (also p.482), and
GLS3 Table 5.3r, p.279. The ATLAS words and permutation conventions are attributed
in Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Definitions and
Model.PermutationData. Witness generation is documented in Max6Core/source/.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.RuEven.Max6Core
open Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.CentralizerCertificate

set_option maxRecDepth 30000
set_option Elab.async false
open Rudvalis.OuterNormalizer.InvarianceCertificate

private def fourth_checkFacts (x : Fin 4060) : Prop :=
    ∀ i : Fin 5,
    seedMap i (seedMap i (seedMap i (seedMap i x))) = x

private instance (x : Fin 4060) : Decidable (fourth_checkFacts x) := by
  unfold fourth_checkFacts
  infer_instance

private theorem fourth_check_block0 : checkBlock fourth_checkFacts 0 = true := by decide +kernel
private theorem fourth_check_block1 : checkBlock fourth_checkFacts 1 = true := by decide +kernel
private theorem fourth_check_block2 : checkBlock fourth_checkFacts 2 = true := by decide +kernel
private theorem fourth_check_block3 : checkBlock fourth_checkFacts 3 = true := by decide +kernel
private theorem fourth_check_block4 : checkBlock fourth_checkFacts 4 = true := by decide +kernel
private theorem fourth_check_block5 : checkBlock fourth_checkFacts 5 = true := by decide +kernel
private theorem fourth_check_block6 : checkBlock fourth_checkFacts 6 = true := by decide +kernel
private theorem fourth_check_block7 : checkBlock fourth_checkFacts 7 = true := by decide +kernel
private theorem fourth_check_block8 : checkBlock fourth_checkFacts 8 = true := by decide +kernel
private theorem fourth_check_block9 : checkBlock fourth_checkFacts 9 = true := by decide +kernel
private theorem fourth_check_block10 : checkBlock fourth_checkFacts 10 = true := by decide +kernel
private theorem fourth_check_block11 : checkBlock fourth_checkFacts 11 = true := by decide +kernel
private theorem fourth_check_block12 : checkBlock fourth_checkFacts 12 = true := by decide +kernel
private theorem fourth_check_block13 : checkBlock fourth_checkFacts 13 = true := by decide +kernel
private theorem fourth_check_block14 : checkBlock fourth_checkFacts 14 = true := by decide +kernel
private theorem fourth_check_block15 : checkBlock fourth_checkFacts 15 = true := by decide +kernel
private theorem fourth_check_block16 : checkBlock fourth_checkFacts 16 = true := by decide +kernel
private theorem fourth_check_block17 : checkBlock fourth_checkFacts 17 = true := by decide +kernel
private theorem fourth_check_block18 : checkBlock fourth_checkFacts 18 = true := by decide +kernel
private theorem fourth_check_block19 : checkBlock fourth_checkFacts 19 = true := by decide +kernel
private theorem fourth_check_block20 : checkBlock fourth_checkFacts 20 = true := by decide +kernel
private theorem fourth_check_block21 : checkBlock fourth_checkFacts 21 = true := by decide +kernel
private theorem fourth_check_block22 : checkBlock fourth_checkFacts 22 = true := by decide +kernel
private theorem fourth_check_block23 : checkBlock fourth_checkFacts 23 = true := by decide +kernel
private theorem fourth_check_block24 : checkBlock fourth_checkFacts 24 = true := by decide +kernel
private theorem fourth_check_block25 : checkBlock fourth_checkFacts 25 = true := by decide +kernel
private theorem fourth_check_block26 : checkBlock fourth_checkFacts 26 = true := by decide +kernel
private theorem fourth_check_block27 : checkBlock fourth_checkFacts 27 = true := by decide +kernel
private theorem fourth_check_block28 : checkBlock fourth_checkFacts 28 = true := by decide +kernel
private theorem fourth_check_block29 : checkBlock fourth_checkFacts 29 = true := by decide +kernel
private theorem fourth_check_block30 : checkBlock fourth_checkFacts 30 = true := by decide +kernel
private theorem fourth_check_block31 : checkBlock fourth_checkFacts 31 = true := by decide +kernel
private theorem fourth_check_block32 : checkBlock fourth_checkFacts 32 = true := by decide +kernel
private theorem fourth_check_block33 : checkBlock fourth_checkFacts 33 = true := by decide +kernel
private theorem fourth_check_block34 : checkBlock fourth_checkFacts 34 = true := by decide +kernel
private theorem fourth_check_block35 : checkBlock fourth_checkFacts 35 = true := by decide +kernel
private theorem fourth_check_block36 : checkBlock fourth_checkFacts 36 = true := by decide +kernel
private theorem fourth_check_block37 : checkBlock fourth_checkFacts 37 = true := by decide +kernel
private theorem fourth_check_block38 : checkBlock fourth_checkFacts 38 = true := by decide +kernel
private theorem fourth_check_block39 : checkBlock fourth_checkFacts 39 = true := by decide +kernel
private theorem fourth_check_block40 : checkBlock fourth_checkFacts 40 = true := by decide +kernel
private theorem fourth_check_block41 : checkBlock fourth_checkFacts 41 = true := by decide +kernel
private theorem fourth_check_block42 : checkBlock fourth_checkFacts 42 = true := by decide +kernel
private theorem fourth_check_block43 : checkBlock fourth_checkFacts 43 = true := by decide +kernel
private theorem fourth_check_block44 : checkBlock fourth_checkFacts 44 = true := by decide +kernel
private theorem fourth_check_block45 : checkBlock fourth_checkFacts 45 = true := by decide +kernel
private theorem fourth_check_block46 : checkBlock fourth_checkFacts 46 = true := by decide +kernel
private theorem fourth_check_block47 : checkBlock fourth_checkFacts 47 = true := by decide +kernel
private theorem fourth_check_block48 : checkBlock fourth_checkFacts 48 = true := by decide +kernel
private theorem fourth_check_block49 : checkBlock fourth_checkFacts 49 = true := by decide +kernel
private theorem fourth_check_block50 : checkBlock fourth_checkFacts 50 = true := by decide +kernel
private theorem fourth_check_block51 : checkBlock fourth_checkFacts 51 = true := by decide +kernel
private theorem fourth_check_block52 : checkBlock fourth_checkFacts 52 = true := by decide +kernel
private theorem fourth_check_block53 : checkBlock fourth_checkFacts 53 = true := by decide +kernel
private theorem fourth_check_block54 : checkBlock fourth_checkFacts 54 = true := by decide +kernel
private theorem fourth_check_block55 : checkBlock fourth_checkFacts 55 = true := by decide +kernel
private theorem fourth_check_block56 : checkBlock fourth_checkFacts 56 = true := by decide +kernel
private theorem fourth_check_block57 : checkBlock fourth_checkFacts 57 = true := by decide +kernel
private theorem fourth_check_block58 : checkBlock fourth_checkFacts 58 = true := by decide +kernel
private theorem fourth_check_block59 : checkBlock fourth_checkFacts 59 = true := by decide +kernel
private theorem fourth_check_block60 : checkBlock fourth_checkFacts 60 = true := by decide +kernel
private theorem fourth_check_block61 : checkBlock fourth_checkFacts 61 = true := by decide +kernel
private theorem fourth_check_block62 : checkBlock fourth_checkFacts 62 = true := by decide +kernel
private theorem fourth_check_block63 : checkBlock fourth_checkFacts 63 = true := by decide +kernel

private theorem fourth_check : ∀ x : Fin 4060, ∀ i : Fin 5,
    seedMap i (seedMap i (seedMap i (seedMap i x))) = x := by
  apply allFinBlocks fourth_checkFacts
  intro b
  fin_cases b
  · exact fourth_check_block0
  · exact fourth_check_block1
  · exact fourth_check_block2
  · exact fourth_check_block3
  · exact fourth_check_block4
  · exact fourth_check_block5
  · exact fourth_check_block6
  · exact fourth_check_block7
  · exact fourth_check_block8
  · exact fourth_check_block9
  · exact fourth_check_block10
  · exact fourth_check_block11
  · exact fourth_check_block12
  · exact fourth_check_block13
  · exact fourth_check_block14
  · exact fourth_check_block15
  · exact fourth_check_block16
  · exact fourth_check_block17
  · exact fourth_check_block18
  · exact fourth_check_block19
  · exact fourth_check_block20
  · exact fourth_check_block21
  · exact fourth_check_block22
  · exact fourth_check_block23
  · exact fourth_check_block24
  · exact fourth_check_block25
  · exact fourth_check_block26
  · exact fourth_check_block27
  · exact fourth_check_block28
  · exact fourth_check_block29
  · exact fourth_check_block30
  · exact fourth_check_block31
  · exact fourth_check_block32
  · exact fourth_check_block33
  · exact fourth_check_block34
  · exact fourth_check_block35
  · exact fourth_check_block36
  · exact fourth_check_block37
  · exact fourth_check_block38
  · exact fourth_check_block39
  · exact fourth_check_block40
  · exact fourth_check_block41
  · exact fourth_check_block42
  · exact fourth_check_block43
  · exact fourth_check_block44
  · exact fourth_check_block45
  · exact fourth_check_block46
  · exact fourth_check_block47
  · exact fourth_check_block48
  · exact fourth_check_block49
  · exact fourth_check_block50
  · exact fourth_check_block51
  · exact fourth_check_block52
  · exact fourth_check_block53
  · exact fourth_check_block54
  · exact fourth_check_block55
  · exact fourth_check_block56
  · exact fourth_check_block57
  · exact fourth_check_block58
  · exact fourth_check_block59
  · exact fourth_check_block60
  · exact fourth_check_block61
  · exact fourth_check_block62
  · exact fourth_check_block63

public theorem seedGenerator_fourth (i : Fin 5) : seedGenerator i ^ 4 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (seedGenerator i).val ((seedGenerator i).val
    ((seedGenerator i).val ((seedGenerator i).val x))) = x
  simpa only [seedMap_eq] using fourth_check x i

private def commute_checkFacts (x : Fin 4060) : Prop :=
    ∀ i j : Fin 5,
    seedMap i (seedMap j x) = seedMap j (seedMap i x)

private instance (x : Fin 4060) : Decidable (commute_checkFacts x) := by
  unfold commute_checkFacts
  infer_instance

private theorem commute_check_block0 : checkBlock commute_checkFacts 0 = true := by decide +kernel
private theorem commute_check_block1 : checkBlock commute_checkFacts 1 = true := by decide +kernel
private theorem commute_check_block2 : checkBlock commute_checkFacts 2 = true := by decide +kernel
private theorem commute_check_block3 : checkBlock commute_checkFacts 3 = true := by decide +kernel
private theorem commute_check_block4 : checkBlock commute_checkFacts 4 = true := by decide +kernel
private theorem commute_check_block5 : checkBlock commute_checkFacts 5 = true := by decide +kernel
private theorem commute_check_block6 : checkBlock commute_checkFacts 6 = true := by decide +kernel
private theorem commute_check_block7 : checkBlock commute_checkFacts 7 = true := by decide +kernel
private theorem commute_check_block8 : checkBlock commute_checkFacts 8 = true := by decide +kernel
private theorem commute_check_block9 : checkBlock commute_checkFacts 9 = true := by decide +kernel
private theorem commute_check_block10 : checkBlock commute_checkFacts 10 = true := by decide +kernel
private theorem commute_check_block11 : checkBlock commute_checkFacts 11 = true := by decide +kernel
private theorem commute_check_block12 : checkBlock commute_checkFacts 12 = true := by decide +kernel
private theorem commute_check_block13 : checkBlock commute_checkFacts 13 = true := by decide +kernel
private theorem commute_check_block14 : checkBlock commute_checkFacts 14 = true := by decide +kernel
private theorem commute_check_block15 : checkBlock commute_checkFacts 15 = true := by decide +kernel
private theorem commute_check_block16 : checkBlock commute_checkFacts 16 = true := by decide +kernel
private theorem commute_check_block17 : checkBlock commute_checkFacts 17 = true := by decide +kernel
private theorem commute_check_block18 : checkBlock commute_checkFacts 18 = true := by decide +kernel
private theorem commute_check_block19 : checkBlock commute_checkFacts 19 = true := by decide +kernel
private theorem commute_check_block20 : checkBlock commute_checkFacts 20 = true := by decide +kernel
private theorem commute_check_block21 : checkBlock commute_checkFacts 21 = true := by decide +kernel
private theorem commute_check_block22 : checkBlock commute_checkFacts 22 = true := by decide +kernel
private theorem commute_check_block23 : checkBlock commute_checkFacts 23 = true := by decide +kernel
private theorem commute_check_block24 : checkBlock commute_checkFacts 24 = true := by decide +kernel
private theorem commute_check_block25 : checkBlock commute_checkFacts 25 = true := by decide +kernel
private theorem commute_check_block26 : checkBlock commute_checkFacts 26 = true := by decide +kernel
private theorem commute_check_block27 : checkBlock commute_checkFacts 27 = true := by decide +kernel
private theorem commute_check_block28 : checkBlock commute_checkFacts 28 = true := by decide +kernel
private theorem commute_check_block29 : checkBlock commute_checkFacts 29 = true := by decide +kernel
private theorem commute_check_block30 : checkBlock commute_checkFacts 30 = true := by decide +kernel
private theorem commute_check_block31 : checkBlock commute_checkFacts 31 = true := by decide +kernel
private theorem commute_check_block32 : checkBlock commute_checkFacts 32 = true := by decide +kernel
private theorem commute_check_block33 : checkBlock commute_checkFacts 33 = true := by decide +kernel
private theorem commute_check_block34 : checkBlock commute_checkFacts 34 = true := by decide +kernel
private theorem commute_check_block35 : checkBlock commute_checkFacts 35 = true := by decide +kernel
private theorem commute_check_block36 : checkBlock commute_checkFacts 36 = true := by decide +kernel
private theorem commute_check_block37 : checkBlock commute_checkFacts 37 = true := by decide +kernel
private theorem commute_check_block38 : checkBlock commute_checkFacts 38 = true := by decide +kernel
private theorem commute_check_block39 : checkBlock commute_checkFacts 39 = true := by decide +kernel
private theorem commute_check_block40 : checkBlock commute_checkFacts 40 = true := by decide +kernel
private theorem commute_check_block41 : checkBlock commute_checkFacts 41 = true := by decide +kernel
private theorem commute_check_block42 : checkBlock commute_checkFacts 42 = true := by decide +kernel
private theorem commute_check_block43 : checkBlock commute_checkFacts 43 = true := by decide +kernel
private theorem commute_check_block44 : checkBlock commute_checkFacts 44 = true := by decide +kernel
private theorem commute_check_block45 : checkBlock commute_checkFacts 45 = true := by decide +kernel
private theorem commute_check_block46 : checkBlock commute_checkFacts 46 = true := by decide +kernel
private theorem commute_check_block47 : checkBlock commute_checkFacts 47 = true := by decide +kernel
private theorem commute_check_block48 : checkBlock commute_checkFacts 48 = true := by decide +kernel
private theorem commute_check_block49 : checkBlock commute_checkFacts 49 = true := by decide +kernel
private theorem commute_check_block50 : checkBlock commute_checkFacts 50 = true := by decide +kernel
private theorem commute_check_block51 : checkBlock commute_checkFacts 51 = true := by decide +kernel
private theorem commute_check_block52 : checkBlock commute_checkFacts 52 = true := by decide +kernel
private theorem commute_check_block53 : checkBlock commute_checkFacts 53 = true := by decide +kernel
private theorem commute_check_block54 : checkBlock commute_checkFacts 54 = true := by decide +kernel
private theorem commute_check_block55 : checkBlock commute_checkFacts 55 = true := by decide +kernel
private theorem commute_check_block56 : checkBlock commute_checkFacts 56 = true := by decide +kernel
private theorem commute_check_block57 : checkBlock commute_checkFacts 57 = true := by decide +kernel
private theorem commute_check_block58 : checkBlock commute_checkFacts 58 = true := by decide +kernel
private theorem commute_check_block59 : checkBlock commute_checkFacts 59 = true := by decide +kernel
private theorem commute_check_block60 : checkBlock commute_checkFacts 60 = true := by decide +kernel
private theorem commute_check_block61 : checkBlock commute_checkFacts 61 = true := by decide +kernel
private theorem commute_check_block62 : checkBlock commute_checkFacts 62 = true := by decide +kernel
private theorem commute_check_block63 : checkBlock commute_checkFacts 63 = true := by decide +kernel

private theorem commute_check : ∀ x : Fin 4060, ∀ i j : Fin 5,
    seedMap i (seedMap j x) = seedMap j (seedMap i x) := by
  apply allFinBlocks commute_checkFacts
  intro b
  fin_cases b
  · exact commute_check_block0
  · exact commute_check_block1
  · exact commute_check_block2
  · exact commute_check_block3
  · exact commute_check_block4
  · exact commute_check_block5
  · exact commute_check_block6
  · exact commute_check_block7
  · exact commute_check_block8
  · exact commute_check_block9
  · exact commute_check_block10
  · exact commute_check_block11
  · exact commute_check_block12
  · exact commute_check_block13
  · exact commute_check_block14
  · exact commute_check_block15
  · exact commute_check_block16
  · exact commute_check_block17
  · exact commute_check_block18
  · exact commute_check_block19
  · exact commute_check_block20
  · exact commute_check_block21
  · exact commute_check_block22
  · exact commute_check_block23
  · exact commute_check_block24
  · exact commute_check_block25
  · exact commute_check_block26
  · exact commute_check_block27
  · exact commute_check_block28
  · exact commute_check_block29
  · exact commute_check_block30
  · exact commute_check_block31
  · exact commute_check_block32
  · exact commute_check_block33
  · exact commute_check_block34
  · exact commute_check_block35
  · exact commute_check_block36
  · exact commute_check_block37
  · exact commute_check_block38
  · exact commute_check_block39
  · exact commute_check_block40
  · exact commute_check_block41
  · exact commute_check_block42
  · exact commute_check_block43
  · exact commute_check_block44
  · exact commute_check_block45
  · exact commute_check_block46
  · exact commute_check_block47
  · exact commute_check_block48
  · exact commute_check_block49
  · exact commute_check_block50
  · exact commute_check_block51
  · exact commute_check_block52
  · exact commute_check_block53
  · exact commute_check_block54
  · exact commute_check_block55
  · exact commute_check_block56
  · exact commute_check_block57
  · exact commute_check_block58
  · exact commute_check_block59
  · exact commute_check_block60
  · exact commute_check_block61
  · exact commute_check_block62
  · exact commute_check_block63

public theorem seedGenerator_commute (i j : Fin 5) :
    Commute (seedGenerator i) (seedGenerator j) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (seedGenerator i).val ((seedGenerator j).val x) =
    (seedGenerator j).val ((seedGenerator i).val x)
  simpa only [seedMap_eq] using commute_check x i j

public instance seed_commutative : IsMulCommutative seed :=
  Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (seedGenerator_commute i j).eq)

public theorem seed_isPGroup : IsPGroup 2 seed := by
  have hh : ∀ x (_hx : x ∈ seed), x ^ 4 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact seedGenerator_fourth i
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hc : Commute x y := congrArg Subtype.val
        (mul_comm' (⟨x, hx⟩ : seed) ⟨y, hy⟩)
      rw [hc.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  intro x
  exact ⟨2, Subtype.ext (hh x.val x.property)⟩

@[expose] public def firstConjugate : Fin 5 → Fin 64 := ![1, 8, 32, 15, 56]
@[expose] public def secondConjugate : Fin 5 → Fin 64 := ![4, 16, 41, 23, 52]

private def first_conjugation_checkFacts (x : Fin 4060) : Prop :=
    ∀ i : Fin 5,
    firstMap (seedMap i x) = wordMap (firstConjugate i) (firstMap x)

private instance (x : Fin 4060) : Decidable (first_conjugation_checkFacts x) := by
  unfold first_conjugation_checkFacts
  infer_instance

private theorem first_conjugation_check_block0 : checkBlock first_conjugation_checkFacts 0 = true := by decide +kernel
private theorem first_conjugation_check_block1 : checkBlock first_conjugation_checkFacts 1 = true := by decide +kernel
private theorem first_conjugation_check_block2 : checkBlock first_conjugation_checkFacts 2 = true := by decide +kernel
private theorem first_conjugation_check_block3 : checkBlock first_conjugation_checkFacts 3 = true := by decide +kernel
private theorem first_conjugation_check_block4 : checkBlock first_conjugation_checkFacts 4 = true := by decide +kernel
private theorem first_conjugation_check_block5 : checkBlock first_conjugation_checkFacts 5 = true := by decide +kernel
private theorem first_conjugation_check_block6 : checkBlock first_conjugation_checkFacts 6 = true := by decide +kernel
private theorem first_conjugation_check_block7 : checkBlock first_conjugation_checkFacts 7 = true := by decide +kernel
private theorem first_conjugation_check_block8 : checkBlock first_conjugation_checkFacts 8 = true := by decide +kernel
private theorem first_conjugation_check_block9 : checkBlock first_conjugation_checkFacts 9 = true := by decide +kernel
private theorem first_conjugation_check_block10 : checkBlock first_conjugation_checkFacts 10 = true := by decide +kernel
private theorem first_conjugation_check_block11 : checkBlock first_conjugation_checkFacts 11 = true := by decide +kernel
private theorem first_conjugation_check_block12 : checkBlock first_conjugation_checkFacts 12 = true := by decide +kernel
private theorem first_conjugation_check_block13 : checkBlock first_conjugation_checkFacts 13 = true := by decide +kernel
private theorem first_conjugation_check_block14 : checkBlock first_conjugation_checkFacts 14 = true := by decide +kernel
private theorem first_conjugation_check_block15 : checkBlock first_conjugation_checkFacts 15 = true := by decide +kernel
private theorem first_conjugation_check_block16 : checkBlock first_conjugation_checkFacts 16 = true := by decide +kernel
private theorem first_conjugation_check_block17 : checkBlock first_conjugation_checkFacts 17 = true := by decide +kernel
private theorem first_conjugation_check_block18 : checkBlock first_conjugation_checkFacts 18 = true := by decide +kernel
private theorem first_conjugation_check_block19 : checkBlock first_conjugation_checkFacts 19 = true := by decide +kernel
private theorem first_conjugation_check_block20 : checkBlock first_conjugation_checkFacts 20 = true := by decide +kernel
private theorem first_conjugation_check_block21 : checkBlock first_conjugation_checkFacts 21 = true := by decide +kernel
private theorem first_conjugation_check_block22 : checkBlock first_conjugation_checkFacts 22 = true := by decide +kernel
private theorem first_conjugation_check_block23 : checkBlock first_conjugation_checkFacts 23 = true := by decide +kernel
private theorem first_conjugation_check_block24 : checkBlock first_conjugation_checkFacts 24 = true := by decide +kernel
private theorem first_conjugation_check_block25 : checkBlock first_conjugation_checkFacts 25 = true := by decide +kernel
private theorem first_conjugation_check_block26 : checkBlock first_conjugation_checkFacts 26 = true := by decide +kernel
private theorem first_conjugation_check_block27 : checkBlock first_conjugation_checkFacts 27 = true := by decide +kernel
private theorem first_conjugation_check_block28 : checkBlock first_conjugation_checkFacts 28 = true := by decide +kernel
private theorem first_conjugation_check_block29 : checkBlock first_conjugation_checkFacts 29 = true := by decide +kernel
private theorem first_conjugation_check_block30 : checkBlock first_conjugation_checkFacts 30 = true := by decide +kernel
private theorem first_conjugation_check_block31 : checkBlock first_conjugation_checkFacts 31 = true := by decide +kernel
private theorem first_conjugation_check_block32 : checkBlock first_conjugation_checkFacts 32 = true := by decide +kernel
private theorem first_conjugation_check_block33 : checkBlock first_conjugation_checkFacts 33 = true := by decide +kernel
private theorem first_conjugation_check_block34 : checkBlock first_conjugation_checkFacts 34 = true := by decide +kernel
private theorem first_conjugation_check_block35 : checkBlock first_conjugation_checkFacts 35 = true := by decide +kernel
private theorem first_conjugation_check_block36 : checkBlock first_conjugation_checkFacts 36 = true := by decide +kernel
private theorem first_conjugation_check_block37 : checkBlock first_conjugation_checkFacts 37 = true := by decide +kernel
private theorem first_conjugation_check_block38 : checkBlock first_conjugation_checkFacts 38 = true := by decide +kernel
private theorem first_conjugation_check_block39 : checkBlock first_conjugation_checkFacts 39 = true := by decide +kernel
private theorem first_conjugation_check_block40 : checkBlock first_conjugation_checkFacts 40 = true := by decide +kernel
private theorem first_conjugation_check_block41 : checkBlock first_conjugation_checkFacts 41 = true := by decide +kernel
private theorem first_conjugation_check_block42 : checkBlock first_conjugation_checkFacts 42 = true := by decide +kernel
private theorem first_conjugation_check_block43 : checkBlock first_conjugation_checkFacts 43 = true := by decide +kernel
private theorem first_conjugation_check_block44 : checkBlock first_conjugation_checkFacts 44 = true := by decide +kernel
private theorem first_conjugation_check_block45 : checkBlock first_conjugation_checkFacts 45 = true := by decide +kernel
private theorem first_conjugation_check_block46 : checkBlock first_conjugation_checkFacts 46 = true := by decide +kernel
private theorem first_conjugation_check_block47 : checkBlock first_conjugation_checkFacts 47 = true := by decide +kernel
private theorem first_conjugation_check_block48 : checkBlock first_conjugation_checkFacts 48 = true := by decide +kernel
private theorem first_conjugation_check_block49 : checkBlock first_conjugation_checkFacts 49 = true := by decide +kernel
private theorem first_conjugation_check_block50 : checkBlock first_conjugation_checkFacts 50 = true := by decide +kernel
private theorem first_conjugation_check_block51 : checkBlock first_conjugation_checkFacts 51 = true := by decide +kernel
private theorem first_conjugation_check_block52 : checkBlock first_conjugation_checkFacts 52 = true := by decide +kernel
private theorem first_conjugation_check_block53 : checkBlock first_conjugation_checkFacts 53 = true := by decide +kernel
private theorem first_conjugation_check_block54 : checkBlock first_conjugation_checkFacts 54 = true := by decide +kernel
private theorem first_conjugation_check_block55 : checkBlock first_conjugation_checkFacts 55 = true := by decide +kernel
private theorem first_conjugation_check_block56 : checkBlock first_conjugation_checkFacts 56 = true := by decide +kernel
private theorem first_conjugation_check_block57 : checkBlock first_conjugation_checkFacts 57 = true := by decide +kernel
private theorem first_conjugation_check_block58 : checkBlock first_conjugation_checkFacts 58 = true := by decide +kernel
private theorem first_conjugation_check_block59 : checkBlock first_conjugation_checkFacts 59 = true := by decide +kernel
private theorem first_conjugation_check_block60 : checkBlock first_conjugation_checkFacts 60 = true := by decide +kernel
private theorem first_conjugation_check_block61 : checkBlock first_conjugation_checkFacts 61 = true := by decide +kernel
private theorem first_conjugation_check_block62 : checkBlock first_conjugation_checkFacts 62 = true := by decide +kernel
private theorem first_conjugation_check_block63 : checkBlock first_conjugation_checkFacts 63 = true := by decide +kernel

private theorem first_conjugation_check : ∀ x : Fin 4060, ∀ i : Fin 5,
    firstMap (seedMap i x) = wordMap (firstConjugate i) (firstMap x) := by
  apply allFinBlocks first_conjugation_checkFacts
  intro b
  fin_cases b
  · exact first_conjugation_check_block0
  · exact first_conjugation_check_block1
  · exact first_conjugation_check_block2
  · exact first_conjugation_check_block3
  · exact first_conjugation_check_block4
  · exact first_conjugation_check_block5
  · exact first_conjugation_check_block6
  · exact first_conjugation_check_block7
  · exact first_conjugation_check_block8
  · exact first_conjugation_check_block9
  · exact first_conjugation_check_block10
  · exact first_conjugation_check_block11
  · exact first_conjugation_check_block12
  · exact first_conjugation_check_block13
  · exact first_conjugation_check_block14
  · exact first_conjugation_check_block15
  · exact first_conjugation_check_block16
  · exact first_conjugation_check_block17
  · exact first_conjugation_check_block18
  · exact first_conjugation_check_block19
  · exact first_conjugation_check_block20
  · exact first_conjugation_check_block21
  · exact first_conjugation_check_block22
  · exact first_conjugation_check_block23
  · exact first_conjugation_check_block24
  · exact first_conjugation_check_block25
  · exact first_conjugation_check_block26
  · exact first_conjugation_check_block27
  · exact first_conjugation_check_block28
  · exact first_conjugation_check_block29
  · exact first_conjugation_check_block30
  · exact first_conjugation_check_block31
  · exact first_conjugation_check_block32
  · exact first_conjugation_check_block33
  · exact first_conjugation_check_block34
  · exact first_conjugation_check_block35
  · exact first_conjugation_check_block36
  · exact first_conjugation_check_block37
  · exact first_conjugation_check_block38
  · exact first_conjugation_check_block39
  · exact first_conjugation_check_block40
  · exact first_conjugation_check_block41
  · exact first_conjugation_check_block42
  · exact first_conjugation_check_block43
  · exact first_conjugation_check_block44
  · exact first_conjugation_check_block45
  · exact first_conjugation_check_block46
  · exact first_conjugation_check_block47
  · exact first_conjugation_check_block48
  · exact first_conjugation_check_block49
  · exact first_conjugation_check_block50
  · exact first_conjugation_check_block51
  · exact first_conjugation_check_block52
  · exact first_conjugation_check_block53
  · exact first_conjugation_check_block54
  · exact first_conjugation_check_block55
  · exact first_conjugation_check_block56
  · exact first_conjugation_check_block57
  · exact first_conjugation_check_block58
  · exact first_conjugation_check_block59
  · exact first_conjugation_check_block60
  · exact first_conjugation_check_block61
  · exact first_conjugation_check_block62
  · exact first_conjugation_check_block63

private def second_conjugation_checkFacts (x : Fin 4060) : Prop :=
    ∀ i : Fin 5,
    secondMap (seedMap i x) = wordMap (secondConjugate i) (secondMap x)

private instance (x : Fin 4060) : Decidable (second_conjugation_checkFacts x) := by
  unfold second_conjugation_checkFacts
  infer_instance

private theorem second_conjugation_check_block0 : checkBlock second_conjugation_checkFacts 0 = true := by decide +kernel
private theorem second_conjugation_check_block1 : checkBlock second_conjugation_checkFacts 1 = true := by decide +kernel
private theorem second_conjugation_check_block2 : checkBlock second_conjugation_checkFacts 2 = true := by decide +kernel
private theorem second_conjugation_check_block3 : checkBlock second_conjugation_checkFacts 3 = true := by decide +kernel
private theorem second_conjugation_check_block4 : checkBlock second_conjugation_checkFacts 4 = true := by decide +kernel
private theorem second_conjugation_check_block5 : checkBlock second_conjugation_checkFacts 5 = true := by decide +kernel
private theorem second_conjugation_check_block6 : checkBlock second_conjugation_checkFacts 6 = true := by decide +kernel
private theorem second_conjugation_check_block7 : checkBlock second_conjugation_checkFacts 7 = true := by decide +kernel
private theorem second_conjugation_check_block8 : checkBlock second_conjugation_checkFacts 8 = true := by decide +kernel
private theorem second_conjugation_check_block9 : checkBlock second_conjugation_checkFacts 9 = true := by decide +kernel
private theorem second_conjugation_check_block10 : checkBlock second_conjugation_checkFacts 10 = true := by decide +kernel
private theorem second_conjugation_check_block11 : checkBlock second_conjugation_checkFacts 11 = true := by decide +kernel
private theorem second_conjugation_check_block12 : checkBlock second_conjugation_checkFacts 12 = true := by decide +kernel
private theorem second_conjugation_check_block13 : checkBlock second_conjugation_checkFacts 13 = true := by decide +kernel
private theorem second_conjugation_check_block14 : checkBlock second_conjugation_checkFacts 14 = true := by decide +kernel
private theorem second_conjugation_check_block15 : checkBlock second_conjugation_checkFacts 15 = true := by decide +kernel
private theorem second_conjugation_check_block16 : checkBlock second_conjugation_checkFacts 16 = true := by decide +kernel
private theorem second_conjugation_check_block17 : checkBlock second_conjugation_checkFacts 17 = true := by decide +kernel
private theorem second_conjugation_check_block18 : checkBlock second_conjugation_checkFacts 18 = true := by decide +kernel
private theorem second_conjugation_check_block19 : checkBlock second_conjugation_checkFacts 19 = true := by decide +kernel
private theorem second_conjugation_check_block20 : checkBlock second_conjugation_checkFacts 20 = true := by decide +kernel
private theorem second_conjugation_check_block21 : checkBlock second_conjugation_checkFacts 21 = true := by decide +kernel
private theorem second_conjugation_check_block22 : checkBlock second_conjugation_checkFacts 22 = true := by decide +kernel
private theorem second_conjugation_check_block23 : checkBlock second_conjugation_checkFacts 23 = true := by decide +kernel
private theorem second_conjugation_check_block24 : checkBlock second_conjugation_checkFacts 24 = true := by decide +kernel
private theorem second_conjugation_check_block25 : checkBlock second_conjugation_checkFacts 25 = true := by decide +kernel
private theorem second_conjugation_check_block26 : checkBlock second_conjugation_checkFacts 26 = true := by decide +kernel
private theorem second_conjugation_check_block27 : checkBlock second_conjugation_checkFacts 27 = true := by decide +kernel
private theorem second_conjugation_check_block28 : checkBlock second_conjugation_checkFacts 28 = true := by decide +kernel
private theorem second_conjugation_check_block29 : checkBlock second_conjugation_checkFacts 29 = true := by decide +kernel
private theorem second_conjugation_check_block30 : checkBlock second_conjugation_checkFacts 30 = true := by decide +kernel
private theorem second_conjugation_check_block31 : checkBlock second_conjugation_checkFacts 31 = true := by decide +kernel
private theorem second_conjugation_check_block32 : checkBlock second_conjugation_checkFacts 32 = true := by decide +kernel
private theorem second_conjugation_check_block33 : checkBlock second_conjugation_checkFacts 33 = true := by decide +kernel
private theorem second_conjugation_check_block34 : checkBlock second_conjugation_checkFacts 34 = true := by decide +kernel
private theorem second_conjugation_check_block35 : checkBlock second_conjugation_checkFacts 35 = true := by decide +kernel
private theorem second_conjugation_check_block36 : checkBlock second_conjugation_checkFacts 36 = true := by decide +kernel
private theorem second_conjugation_check_block37 : checkBlock second_conjugation_checkFacts 37 = true := by decide +kernel
private theorem second_conjugation_check_block38 : checkBlock second_conjugation_checkFacts 38 = true := by decide +kernel
private theorem second_conjugation_check_block39 : checkBlock second_conjugation_checkFacts 39 = true := by decide +kernel
private theorem second_conjugation_check_block40 : checkBlock second_conjugation_checkFacts 40 = true := by decide +kernel
private theorem second_conjugation_check_block41 : checkBlock second_conjugation_checkFacts 41 = true := by decide +kernel
private theorem second_conjugation_check_block42 : checkBlock second_conjugation_checkFacts 42 = true := by decide +kernel
private theorem second_conjugation_check_block43 : checkBlock second_conjugation_checkFacts 43 = true := by decide +kernel
private theorem second_conjugation_check_block44 : checkBlock second_conjugation_checkFacts 44 = true := by decide +kernel
private theorem second_conjugation_check_block45 : checkBlock second_conjugation_checkFacts 45 = true := by decide +kernel
private theorem second_conjugation_check_block46 : checkBlock second_conjugation_checkFacts 46 = true := by decide +kernel
private theorem second_conjugation_check_block47 : checkBlock second_conjugation_checkFacts 47 = true := by decide +kernel
private theorem second_conjugation_check_block48 : checkBlock second_conjugation_checkFacts 48 = true := by decide +kernel
private theorem second_conjugation_check_block49 : checkBlock second_conjugation_checkFacts 49 = true := by decide +kernel
private theorem second_conjugation_check_block50 : checkBlock second_conjugation_checkFacts 50 = true := by decide +kernel
private theorem second_conjugation_check_block51 : checkBlock second_conjugation_checkFacts 51 = true := by decide +kernel
private theorem second_conjugation_check_block52 : checkBlock second_conjugation_checkFacts 52 = true := by decide +kernel
private theorem second_conjugation_check_block53 : checkBlock second_conjugation_checkFacts 53 = true := by decide +kernel
private theorem second_conjugation_check_block54 : checkBlock second_conjugation_checkFacts 54 = true := by decide +kernel
private theorem second_conjugation_check_block55 : checkBlock second_conjugation_checkFacts 55 = true := by decide +kernel
private theorem second_conjugation_check_block56 : checkBlock second_conjugation_checkFacts 56 = true := by decide +kernel
private theorem second_conjugation_check_block57 : checkBlock second_conjugation_checkFacts 57 = true := by decide +kernel
private theorem second_conjugation_check_block58 : checkBlock second_conjugation_checkFacts 58 = true := by decide +kernel
private theorem second_conjugation_check_block59 : checkBlock second_conjugation_checkFacts 59 = true := by decide +kernel
private theorem second_conjugation_check_block60 : checkBlock second_conjugation_checkFacts 60 = true := by decide +kernel
private theorem second_conjugation_check_block61 : checkBlock second_conjugation_checkFacts 61 = true := by decide +kernel
private theorem second_conjugation_check_block62 : checkBlock second_conjugation_checkFacts 62 = true := by decide +kernel
private theorem second_conjugation_check_block63 : checkBlock second_conjugation_checkFacts 63 = true := by decide +kernel

private theorem second_conjugation_check : ∀ x : Fin 4060, ∀ i : Fin 5,
    secondMap (seedMap i x) = wordMap (secondConjugate i) (secondMap x) := by
  apply allFinBlocks second_conjugation_checkFacts
  intro b
  fin_cases b
  · exact second_conjugation_check_block0
  · exact second_conjugation_check_block1
  · exact second_conjugation_check_block2
  · exact second_conjugation_check_block3
  · exact second_conjugation_check_block4
  · exact second_conjugation_check_block5
  · exact second_conjugation_check_block6
  · exact second_conjugation_check_block7
  · exact second_conjugation_check_block8
  · exact second_conjugation_check_block9
  · exact second_conjugation_check_block10
  · exact second_conjugation_check_block11
  · exact second_conjugation_check_block12
  · exact second_conjugation_check_block13
  · exact second_conjugation_check_block14
  · exact second_conjugation_check_block15
  · exact second_conjugation_check_block16
  · exact second_conjugation_check_block17
  · exact second_conjugation_check_block18
  · exact second_conjugation_check_block19
  · exact second_conjugation_check_block20
  · exact second_conjugation_check_block21
  · exact second_conjugation_check_block22
  · exact second_conjugation_check_block23
  · exact second_conjugation_check_block24
  · exact second_conjugation_check_block25
  · exact second_conjugation_check_block26
  · exact second_conjugation_check_block27
  · exact second_conjugation_check_block28
  · exact second_conjugation_check_block29
  · exact second_conjugation_check_block30
  · exact second_conjugation_check_block31
  · exact second_conjugation_check_block32
  · exact second_conjugation_check_block33
  · exact second_conjugation_check_block34
  · exact second_conjugation_check_block35
  · exact second_conjugation_check_block36
  · exact second_conjugation_check_block37
  · exact second_conjugation_check_block38
  · exact second_conjugation_check_block39
  · exact second_conjugation_check_block40
  · exact second_conjugation_check_block41
  · exact second_conjugation_check_block42
  · exact second_conjugation_check_block43
  · exact second_conjugation_check_block44
  · exact second_conjugation_check_block45
  · exact second_conjugation_check_block46
  · exact second_conjugation_check_block47
  · exact second_conjugation_check_block48
  · exact second_conjugation_check_block49
  · exact second_conjugation_check_block50
  · exact second_conjugation_check_block51
  · exact second_conjugation_check_block52
  · exact second_conjugation_check_block53
  · exact second_conjugation_check_block54
  · exact second_conjugation_check_block55
  · exact second_conjugation_check_block56
  · exact second_conjugation_check_block57
  · exact second_conjugation_check_block58
  · exact second_conjugation_check_block59
  · exact second_conjugation_check_block60
  · exact second_conjugation_check_block61
  · exact second_conjugation_check_block62
  · exact second_conjugation_check_block63

public theorem first_conjugation (i : Fin 5) :
    first * seedGenerator i * first⁻¹ = seedWord (firstConjugate i) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change firstMap ((seedGenerator i).val x) = (seedWord (firstConjugate i)).val (firstMap x)
  simpa only [seedMap_eq, wordMap_eq] using first_conjugation_check x i

public theorem second_conjugation (i : Fin 5) :
    second * seedGenerator i * second⁻¹ = seedWord (secondConjugate i) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change secondMap ((seedGenerator i).val x) = (seedWord (secondConjugate i)).val (secondMap x)
  simpa only [seedMap_eq, wordMap_eq] using second_conjugation_check x i

private theorem normalizes_seed (g : Model)
    (h : ∀ i, g * seedGenerator i * g⁻¹ ∈ seed) :
    g ∈ Subgroup.normalizer (seed : Set Model) := by
  have hh : seed ≤ seed.comap (MulAut.conj g).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  exact Subgroup.mem_normalizer_fintype (fun k hk => hh hk)

public theorem max6_normalizes_seed : max6 ≤ Subgroup.normalizer (seed : Set Model) := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · rw [← first_model_eq]
    exact normalizes_seed first (fun i => (first_conjugation i).symm ▸ seedWord_mem (firstConjugate i))
  · have he := Set.mem_singleton_iff.mp hg
    subst g
    rw [← second_model_eq]
    exact normalizes_seed second (fun i => (second_conjugation i).symm ▸ seedWord_mem (secondConjugate i))

public instance normalSeed_normal : normalSeed.Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer seed_le_max6).mpr max6_normalizes_seed

public theorem normalSeed_isPGroup : IsPGroup 2 normalSeed :=
  seed_isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe seed_le_max6).symm
@[expose] public def wordPointInverseData : Array Nat := #[
6465202073327226348019969225908670921305929960365520326726031699611073461162933881929728,
370699266673321297176671457446519921762510735809932871615174640926720,
0,
216172782113783808,
47719632162314975222494106294163164644499340103373817892535533568,
0,
624420865558857447963000111634154122167451648,
161261621436801903160135844200927988024758475800894766512799215269393014724971588095757378412773583618048,
854394814368364032958008682467820845841081808942661107978816643128887890312256220009184834774630400,
1079997746575244146734343236477779968,
0,
167329879230126280997564823109632,
0,
0,
0,
0,
4413587157693759912072039438192890448821968671888774266880,
0,
1187100371647976971438778008311648377821590743213306487487954166493478912,
18014398509481984,
167125767421952,
0,
0,
1822247737828085677756325560320,
0,
3394200909562557497344,
1545991181681086355815189111249163469116317604379770667580926802209538048,
962659876864,
23871515347669758823458347911047400324821895238272690437142270890871655856601602025586688,
3607361407140607838038242196668421674049048395123179321406398932273473062576038569160241661519004727857052123136,
36939380809119833026534401995789860233230195977271773685782588943346044025123969015609939833966978556306138761003008,
2624,
330259346672595337484670934815990475752055019176122012893519225552896,
349400179779737456846960995768677307387029353714439606042405795233185620172038800431400315631151150530560,
28301828225954001260626263335817484980392658440132291608637353443165663179003226192089452860407808,
54187310716521807872,
0,
0,
2560,
11742712913869166139447402984509897858928718719081848624618712841459350330986717920806416680538332977728323584,
6772219815005301114610460017212183622748080187111248646053612928854733429476083073836827012558344875763639185833984,
0,
66571993088,
0,
0,
37108440010354956907515435205686873545951412224,
0,
76957043352332967211482500195592995713046365762627825523350303015035218334680714598662841561724669513050097713152,
21711016731996786641919559689128982722488122124807605757398297001483711807488,
528579759153961793691556378214152867854892297674422131482632872880970309308818326641678942517863905230848,
65373341396800220194582007614550094340680456928953345586918632767174475776,
23158417847463239084714197001737581570653996933128112807891516801582625927987200,
0,
117440512,
4278320775770274230051373318144,
1503067252975253265849267581945175697520437255920484724875242987786101396632532513601792013980268547322299809792,
5411042110710911757057363295002632511073572592684768982109598398410209593864057853740362492426081044375254597632,
0,
0,
197097537311646770529054920690023096478285421673380103418928253826058479362696596437135889190547999424512,
0,
407069128042501728001435929086800876898727579330019328,
61203283968,
0]

@[expose] public def wordPointInverse (x : Fin 4060) : Fin 64 :=
  ⟨((wordPointInverseData[x.val / 64]! >>> (6 * (x.val % 64))) % 64) % 64, Nat.mod_lt _ (by decide)⟩

private theorem wordPoint_leftInverse : ∀ i : Fin 64,
    wordPointInverse (wordMap i 0) = i := by decide +kernel

public theorem seedWord_injective : Function.Injective seedWord := by
  intro i j hij
  have hp : wordMap i 0 = wordMap j 0 := by
    simpa only [wordMap_eq] using congrArg (fun g : Model => g.val 0) hij
  have := congrArg wordPointInverse hp
  simpa only [wordPoint_leftInverse] using this

public theorem normalSeed_card_ge : 64 ≤ Nat.card normalSeed := by
  let f : Fin 64 → normalSeed := fun i =>
    ⟨⟨seedWord i, seed_le_max6 (seedWord_mem i)⟩, seedWord_mem i⟩
  have hf : Function.Injective f := fun i j h =>
    seedWord_injective (congrArg (fun g : normalSeed => (g : max6).val) h)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

end CFSG.Quasithin.MainConverse.SporadicLocal.RuEven.Max6Core
