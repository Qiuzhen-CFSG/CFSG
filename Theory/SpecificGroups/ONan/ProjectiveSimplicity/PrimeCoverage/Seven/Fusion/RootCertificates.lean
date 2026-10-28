module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Seven.Fusion.RootCertificates.WordRealization
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Seven.Fusion.RootCertificates.Values
import Mathlib.Tactic.FinCases

/-!
# Certified fusion of the seven-coordinate roots

The checked matrix products establish intertwining equations for the literal
ambient/local conjugators and the central bridge. Cancellation gives their
conjugation equations in GL(45,7), and projectivization proves `RootIdentities`.
No scalar correction or group-order assumption is used.

The witness words are fixed in `Fusion/Witnesses.lean`; original ATLAS matrix
attribution is preserved in `refs/original/onan/README.md`.
-/

namespace ONan.Simplicity.Seven.Fusion
open ONan.OrderCertificate
open Certificate (LinearGroup)
open RootCertificate

private theorem map_word {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) (w : List ℤ) :
    f (word a b w) = word (f a) (f b) w := by
  simp only [word, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  split_ifs <;> simp_all

private theorem project_word (a b : LinearGroup) (a' b' : Model)
    (ha : Matrix.ProjGenLinGroup.mk a = a'.val)
    (hb : Matrix.ProjGenLinGroup.mk b = b'.val) (w : List ℤ) :
    Matrix.ProjGenLinGroup.mk (word a b w) = (word a' b' w).val := by
  rw [map_word, ha, hb]
  exact (map_word modelInclusion a' b' w).symm

private theorem project_ambient_word (w : List ℤ) :
    Matrix.ProjGenLinGroup.mk (word linearA linearB w) =
      (word generatorA generatorB w).val :=
  project_word _ _ _ _ rfl rfl w

private theorem project_local_word (w : List ℤ) :
    Matrix.ProjGenLinGroup.mk (word linearLocalA linearLocalB w) =
      (word localA localB w).val :=
  project_word _ _ _ _ mk_linearLocalA mk_linearLocalB w

private def linearRoot : Fin 3 → LinearGroup := ![lift_r74, lift_r137, lift_r189]
private def linearPrime : Fin 3 → LinearGroup := ![lift_r199, lift_r199, lift_r197]
private def linearTarget : Fin 3 → LinearGroup := ![linearX, linearY, linearX * linearY]

private theorem inclusion_val (g : Model) : modelInclusion g = g.val := rfl

private theorem project_root (r : Fin 3) :
    Matrix.ProjGenLinGroup.mk (linearRoot r) = (rootConjugator r).val := by
  change Matrix.ProjGenLinGroup.mk (linearRoot r) = modelInclusion (rootConjugator r)
  fin_cases r <;>
    dsimp only [linearRoot, rootConjugator] <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ',
      root_word_0, root_word_1, root_word_2, map_mul,
      project_ambient_word, project_local_word, inclusion_val]

private theorem map_cyclicWords {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) (i : Fin 10) :
    f (cyclicWords a b i) = cyclicWords (f a) (f b) i := by
  fin_cases i <;> simp [cyclicWords, map_mul]

private theorem project_prime_three :
    Matrix.ProjGenLinGroup.mk lift_r199 = modelInclusion (primeRepresentative 3) := by
  change Matrix.ProjGenLinGroup.mk lift_r199 =
    modelInclusion (cyclicWords generatorA generatorB 8 ^ 4)
  rw [representative_word_3, map_pow, map_pow, map_cyclicWords, map_cyclicWords]
  rfl

private theorem project_prime_four :
    Matrix.ProjGenLinGroup.mk lift_r197 = modelInclusion (primeRepresentative 4) := by
  rw [representative_word_4]
  have h : primeRepresentative 4 = cyclicWords generatorA generatorB 0 := by
    simp only [primeRepresentative, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons]
  rw [h, map_cyclicWords, map_cyclicWords]
  rfl

private theorem project_prime (r : Fin 3) :
    Matrix.ProjGenLinGroup.mk (linearPrime r) =
      (primeRepresentative (rootRepresentative r)).val := by
  fin_cases r
  · exact project_prime_three
  · exact project_prime_three
  · exact project_prime_four

private theorem evaluate_origin (r : Fin 3) :
    evaluate (origin ⟨r.val, by omega⟩) =
      ![generatorX, generatorY, generatorX * generatorY] r := by
  fin_cases r
  · exact evaluate_x
  · exact evaluate_y
  · change generatorX ^ 1 * generatorY ^ 1 * generatorZ ^ 0 = generatorX * generatorY
    simp

private theorem project_target (r : Fin 3) :
    Matrix.ProjGenLinGroup.mk (linearTarget r) =
      (evaluate (origin ⟨r.val, by omega⟩)).val := by
  rw [evaluate_origin]
  fin_cases r
  · exact project_linearX
  · exact project_linearY
  · change Matrix.ProjGenLinGroup.mk (linearX * linearY) =
      modelInclusion (generatorX * generatorY)
    rw [map_mul, map_mul, project_linearX, project_linearY]
    rfl

private theorem linear_intertwining (r : Fin 3) :
    linearPrime r * linearRoot r = linearRoot r * linearTarget r := by
  fin_cases r
  · exact intertwining_0
  · exact intertwining_1
  · exact intertwining_2

/-- The three full matrix identities descend to the required fixed representatives. -/
public theorem root_identities : ∀ r : Fin 3,
    primeRepresentative (rootRepresentative r) =
      rootConjugator r * evaluate (origin ⟨r.val, by omega⟩) * (rootConjugator r)⁻¹ := by
  intro r
  have h : linearPrime r = linearRoot r * linearTarget r * (linearRoot r)⁻¹ :=
    eq_mul_inv_iff_mul_eq.mpr (linear_intertwining r)
  have hp := congrArg Matrix.ProjGenLinGroup.mk h
  rw [map_mul, map_mul, map_inv, project_prime, project_root, project_target] at hp
  exact Subtype.ext hp

/-- The full matrix equation for the central bridge descends to the model. -/
public theorem central_identity : centralBridge⁻¹ * generatorZ * centralBridge = generatorY := by
  have h : linearZ * lift_r5 = lift_r5 * linearY := intertwining_3
  have hc : lift_r5⁻¹ * linearZ * lift_r5 = linearY := by
    rw [mul_assoc, h, inv_mul_cancel_left]
  have hp := congrArg Matrix.ProjGenLinGroup.mk hc
  rw [map_mul, map_mul, map_inv, central_word, project_local_word,
    project_linearZ, project_linearY] at hp
  exact Subtype.ext hp

/-- Unconditional certificates for all four fixed seven-root fusion witnesses. -/
public theorem rootIdentities : RootIdentities :=
  ⟨root_identities, central_identity⟩

end ONan.Simplicity.Seven.Fusion
