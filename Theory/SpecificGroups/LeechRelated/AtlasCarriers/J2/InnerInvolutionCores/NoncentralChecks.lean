module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.NoncentralData

/-!
# Checking the two factors of the noncentral J₂ centralizer

The five-letter tables enumerate A₅ and respect the supplied multiplication
table. The original degree-100 words respect the same multiplication on the
pair of points (0,1); the coverage module proves this pair is faithful for the
whole centralizer. The remaining checks verify the E₄ factor, commutation,
coverage of all 240 words, and the trivial product kernel.

The largest checks use nested Boolean traversal of packed rows; this avoids
materializing proofs during the finite computation. The measured 18000-entry
multiplication check fits below the compiler memory limit.

The permutation and enumeration bodies below are exposed so the companion
homomorphism construction can reduce their applications. Their proofs remain
private. Adapted, with the original files preserved, from
`CFSG/Quasithin/Chapter16/Section01To02/OtherPreliminaries/
JankoTwoHigmanSims/J2Inner/NoncentralChecks.lean`. Only intrinsic carrier
mathematics is used here; the chapter hypotheses are not imported.

Source: Aschbacher–Smith 16.1.5(8), p.1172, and the retained ATLAS
J2G1-p100B0 words. Every finite check is performed by the Lean kernel.
-/

public section

namespace Sporadic.LeechRelated.J2.InnerInvolutionCores.NoncentralData
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate

-- Keep the independent finite checks sequential within this certificate module.
set_option Elab.async false

private theorem checkedAt {n : ℕ} {f : Fin n → Bool}
    (h : checkFin f = true) (i : Fin n) : f i = true := by
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt] using hi

set_option maxRecDepth 100000 in
private theorem simple_left : ∀ i x, simpleInvMap i (simpleMap i x) = x := by
  decide +kernel
set_option maxRecDepth 100000 in
private theorem simple_right : ∀ i x, simpleMap i (simpleInvMap i x) = x := by
  decide +kernel

@[expose] def simplePerm (i : Fin 60) : Equiv.Perm (Fin 5) :=
  ⟨simpleMap i, simpleInvMap i, by exact simple_left i, by exact simple_right i⟩

set_option maxRecDepth 100000 in
private theorem simple_even : ∀ i, simplePerm i ∈ alternatingGroup (Fin 5) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

@[expose] def simpleEnum (i : Fin 60) : A5 := ⟨simplePerm i, by exact simple_even i⟩

set_option maxRecDepth 100000 in
private theorem simpleEnum_injective : Function.Injective simpleEnum := by
  have h : checkFin (fun i : Fin 60 => checkFin (fun j : Fin 60 =>
      decide ((∀ x, simpleMap i x = simpleMap j x) → i = j))) = true := by
    decide +kernel
  intro i j he
  exact (of_decide_eq_true (checkedAt (checkedAt h i) j))
    (fun x => congrArg (fun a : A5 => a.val x) he)

@[expose] noncomputable def simpleEquiv : Fin 60 ≃ A5 :=
  Equiv.ofBijective simpleEnum (by
    exact simpleEnum_injective.bijective_of_nat_card_le (by
      rw [nat_card_alternatingGroup, Nat.card_fin, Nat.card_fin]
      decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem simpleEnum_mul : ∀ i j,
    simpleEnum (simpleMul i j) = simpleEnum i * simpleEnum j := by
  have h : checkFin (fun i : Fin 60 => checkFin (fun j : Fin 60 =>
      checkFin (fun x : Fin 5 => decide
        (simpleMap (simpleMul i j) x = simpleMap i (simpleMap j x))))) = true := by
    decide +kernel
  intro i j
  exact Subtype.ext (Equiv.ext (fun x =>
    of_decide_eq_true (checkedAt (checkedAt (checkedAt h i) j) x)))


set_option maxRecDepth 100000 in
theorem simpleTable_mul : ∀ i j,
    conjugatorTable (simpleIndex (simpleMul i j)) 0 =
      (conjugatorTable (simpleIndex i) * conjugatorTable (simpleIndex j)) 0 ∧
    conjugatorTable (simpleIndex (simpleMul i j)) 1 =
      (conjugatorTable (simpleIndex i) * conjugatorTable (simpleIndex j)) 1 := by
  have h : checkFin (fun i : Fin 60 => checkFin (fun j : Fin 60 => decide
      (conjugatorTable (simpleIndex (simpleMul i j)) 0 =
        (conjugatorTable (simpleIndex i) * conjugatorTable (simpleIndex j)) 0 ∧
      conjugatorTable (simpleIndex (simpleMul i j)) 1 =
        (conjugatorTable (simpleIndex i) * conjugatorTable (simpleIndex j)) 1))) = true := by
    decide +kernel
  intro i j
  exact of_decide_eq_true (checkedAt (checkedAt h i) j)

set_option maxRecDepth 100000 in
theorem centerTable_mul : ∀ x y : E4,
    conjugatorTable (centerIndex (x * y)) 0 =
      (conjugatorTable (centerIndex x) * conjugatorTable (centerIndex y)) 0 ∧
    conjugatorTable (centerIndex (x * y)) 1 =
      (conjugatorTable (centerIndex x) * conjugatorTable (centerIndex y)) 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem factors_commute : ∀ (x : E4) (i : Fin 60),
    (conjugatorTable (centerIndex x) * conjugatorTable (simpleIndex i)) 0 =
      (conjugatorTable (simpleIndex i) * conjugatorTable (centerIndex x)) 0 ∧
    (conjugatorTable (centerIndex x) * conjugatorTable (simpleIndex i)) 1 =
      (conjugatorTable (simpleIndex i) * conjugatorTable (centerIndex x)) 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem product_cover : ∀ i,
    (conjugatorTable (centerIndex (factorCenter i)) *
      conjugatorTable (simpleIndex (factorSimple i))) 0 = conjugatorTable i 0 ∧
    (conjugatorTable (centerIndex (factorCenter i)) *
      conjugatorTable (simpleIndex (factorSimple i))) 1 = conjugatorTable i 1 := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem product_kernel : ∀ (x : E4) (i : Fin 60),
    (conjugatorTable (centerIndex x) * conjugatorTable (simpleIndex i)) 0 = 0 →
    (conjugatorTable (centerIndex x) * conjugatorTable (simpleIndex i)) 1 = 1 →
    x = 1 ∧ i = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem simpleEnum_zero : simpleEnum 0 = 1 := by
  apply Subtype.ext
  decide +kernel

end Sporadic.LeechRelated.J2.InnerInvolutionCores.NoncentralData
