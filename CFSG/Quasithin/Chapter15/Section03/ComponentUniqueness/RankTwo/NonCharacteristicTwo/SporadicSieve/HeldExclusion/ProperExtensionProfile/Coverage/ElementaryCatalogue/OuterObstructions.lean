module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.ElementaryCatalogue.Model

/-!
# Excluding outer elements from normal elementary Held subgroups

A member of a normal elementary subgroup squares to one and commutes with
every conjugate. For each of the 1024 outer-coset words, either its square moves
point 0 or 1, or it fails to commute with its conjugate by one of the first three
pure generators. The differences are checked on points 0 and 1 of the original
ATLAS permutation action, then transported through the faithful normalizer action.

The finite reduction is checked in sixteen blocks of 64. Only this certificate
section elaborates sequentially: measurement reduced its peak memory from 2.9 GB
to 2.0 GB at approximately 22 seconds, including import preparation.
No ambient order, simplicity, or elementary subgroup catalogue is assumed.
Source: Aschbacher--Smith 15.3.41--42, printed p.1138; GLS3 Table 5.3p;
`ElementaryCatalogue/source/README.md` and the unchanged ATLAS Held carrier.
-/

public section
open Subgroup Held Held.LocalPairs Held.LocalPairs.PairCoverage.LocalActions
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData.ElementaryCatalogue
open RepresentativeImages Exhaustion.CandidateOrderCertificate.Factors
open Exhaustion.CandidateOrderCertificate

private def perm (n : Fin 1024) : Equiv.Perm (Fin 2058) :=
  Pair00Two.normalTable n * PureActors.Actor0.perm

private def conjugate (n : Fin 1024) (k : Fin 3) : Equiv.Perm (Fin 2058) :=
  (Pair00Two.inputTable k.castSucc)⁻¹ * perm n * Pair00Two.inputTable k.castSucc

private def check (n : Fin 1024) : Prop :=
  (perm n * perm n) 0 ≠ 0 ∨ (perm n * perm n) 1 ≠ 1 ∨
    ∃ k : Fin 3, (perm n * conjugate n k) 0 ≠ (conjugate n k * perm n) 0 ∨
      (perm n * conjugate n k) 1 ≠ (conjugate n k * perm n) 1

private instance (n : Fin 1024) : Decidable (check n) := by
  unfold check
  infer_instance

section Checks
set_option Elab.async false

set_option maxRecDepth 8192 in
private theorem check_block0 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 0 j.val))) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check_block1 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 1 j.val))) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check_block2 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 2 j.val))) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check_block3 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 3 j.val))) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check_block4 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 4 j.val))) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check_block5 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 5 j.val))) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check_block6 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 6 j.val))) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check_block7 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 7 j.val))) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check_block8 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 8 j.val))) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check_block9 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 9 j.val))) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check_block10 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 10 j.val))) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check_block11 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 11 j.val))) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check_block12 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 12 j.val))) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check_block13 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 13 j.val))) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check_block14 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 14 j.val))) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check_block15 : checkFin 64 (fun j => decide
    (check (blockIndex 1024 64 (by decide) 15 j.val))) = true := by decide +kernel

private theorem checked : ∀ n, check n := by
  apply allBlocks (b := 16) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ check_block0
  · exact allFin _ _ check_block1
  · exact allFin _ _ check_block2
  · exact allFin _ _ check_block3
  · exact allFin _ _ check_block4
  · exact allFin _ _ check_block5
  · exact allFin _ _ check_block6
  · exact allFin _ _ check_block7
  · exact allFin _ _ check_block8
  · exact allFin _ _ check_block9
  · exact allFin _ _ check_block10
  · exact allFin _ _ check_block11
  · exact allFin _ _ check_block12
  · exact allFin _ _ check_block13
  · exact allFin _ _ check_block14
  · exact allFin _ _ check_block15

end Checks

private theorem check_implies_obstruction (n : Fin 1024) (h : check n) : outerObstruction n := by
  have hp : (elementLift (true, n)).val = perm n := elementLift_val (true, n)
  have ht (k : Fin 3) : Pair00Two.inputTable k.castSucc =
      (testLift (k.castLE (by decide : 3 ≤ 5))).val := by
    fin_cases k
    · exact Pair00Two.inputTable_eq 0
    · exact Pair00Two.inputTable_eq 1
    · exact Pair00Two.inputTable_eq 2
  apply outerObstruction_of_lifts n
  have square (p : Fin 2058) (hs : (perm n * perm n) p ≠ p) :
      elementLift (true, n) ^ 2 ≠ 1 := by
    intro he
    apply hs
    have hf := congrArg (fun g : PermutationNormalizer => g.val p) he
    change ((elementLift (true, n)).val ^ 2) p = p at hf
    rw [pow_two, hp] at hf
    exact hf
  have conjugates (k : Fin 3) (p : Fin 2058)
      (hc : (perm n * conjugate n k) p ≠ (conjugate n k * perm n) p) :
      ¬Commute (elementLift (true, n))
        ((testLift (k.castLE (by decide : 3 ≤ 5)))⁻¹ * elementLift (true, n) *
          testLift (k.castLE (by decide : 3 ≤ 5))) := by
    intro he
    apply hc
    have hf := congrArg (fun g : PermutationNormalizer => g.val p) he.eq
    change ((elementLift (true, n)).val *
      ((testLift (k.castLE (by decide : 3 ≤ 5))).val⁻¹ *
        (elementLift (true, n)).val * (testLift (k.castLE (by decide : 3 ≤ 5))).val)) p =
      (((testLift (k.castLE (by decide : 3 ≤ 5))).val⁻¹ * (elementLift (true, n)).val *
        (testLift (k.castLE (by decide : 3 ≤ 5))).val) * (elementLift (true, n)).val) p at hf
    rw [hp, ← ht] at hf
    exact hf
  rcases h with h | h | ⟨k, h | h⟩
  · exact Or.inl (square 0 h)
  · exact Or.inl (square 1 h)
  · exact Or.inr ⟨_, conjugates k 0 h⟩
  · exact Or.inr ⟨_, conjugates k 1 h⟩

/-- Every outer-coset word fails a necessary condition for normal elementary membership.
All 1024 branches are checked by kernel reduction on the original 2058 letters. -/
theorem outer_obstructions (n : Fin 1024) : outerObstruction n :=
  check_implies_obstruction n (checked n)

/-- No normal elementary subgroup contains any of the outer-coset words. -/
theorem outer_element_not_mem (n : Fin 1024) (R : Subgroup outerRepresentative)
    (hn : R.Normal) (he : IsElementaryAbelian 2 R) : element (true, n) ∉ R :=
  not_mem_of_outerObstruction n (outer_obstructions n) R hn he

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData.ElementaryCatalogue
