module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.Basic
public import Theory.GroupTheory.CosetWordCertificateBoolean
import Mathlib.Tactic.Group

/-!
# Conjugations and central translations for the commutator calculation

Centrality of a² implies [a,w]⁻¹a = a[a,w]. It turns the square and cube
commutator defects into explicit translations in the conjugation orbit of a.
The four resulting stabilizer words are the subgroup inputs of the checked
coset calculation. All operations act on F/[F,R] itself.

Source: the literal seven words of ATLAS S62G1-P1.M, in the convention
[x,y] = x⁻¹y⁻¹xy; attribution and reproduction in `source/README.md`.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.CommutatorIdentities
open Subgroup.CosetWordCertificate

private lemma move_commutator {G : Type*} [Group G] (a b : G)
    (ha : a ^ 2 ∈ Subgroup.center G) :
    (sourceCommutator a b)⁻¹ * a = a * sourceCommutator a b := by
  calc
    _ = b⁻¹ * a⁻¹ * (b * a ^ 2) := by dsimp [sourceCommutator]; rw [pow_two]; group
    _ = b⁻¹ * a⁻¹ * (a ^ 2 * b) := by rw [Subgroup.mem_center_iff.mp ha b]
    _ = _ := by dsimp [sourceCommutator]; rw [pow_two]; group

private lemma cubic_conjugation {G : Type*} [Group G] (a b : G)
    (ha : a ^ 2 ∈ Subgroup.center G) :
    (b * sourceCommutator a b)⁻¹ * a * (b * sourceCommutator a b) =
      a * sourceCommutator a b ^ 3 := by
  calc
    _ = ((sourceCommutator a b)⁻¹ * a) * sourceCommutator a b ^ 2 := by
      dsimp [sourceCommutator]; rw [pow_two]; group
    _ = _ := by rw [move_commutator a b ha]; simp only [pow_succ, pow_zero]; group

private lemma square_conjugation {G : Type*} [Group G] (a b : G)
    (ha : a ^ 2 ∈ Subgroup.center G) :
    (b⁻¹ * a * b)⁻¹ * a * (b⁻¹ * a * b) =
      a * sourceCommutator a b ^ 2 := by
  calc
    _ = (sourceCommutator a b)⁻¹ * a * sourceCommutator a b := by
      dsimp [sourceCommutator]; group
    _ = _ := by rw [move_commutator a b ha, pow_two]; group

private lemma left_of_right {G : Type*} [Group G] (a q z : G)
    (hz : z ∈ Subgroup.center G) (hz2 : z ^ 2 = 1)
    (h : q⁻¹ * a * q = a * z) : q * a * q⁻¹ = a * z := by
  have hq := congrArg (fun x => q * x * q⁻¹ * z) h
  simp only [mul_assoc, mul_inv_cancel_left] at hq
  have hc := Subgroup.mem_center_iff.mp hz q⁻¹
  have zz : z * z = 1 := by simpa [pow_two] using hz2
  simpa only [hc, ← mul_assoc z z, zz, one_mul, mul_assoc] using hq.symm

private lemma inverse_commutator_square {G : Type*} [Group G] (a b : G)
    (hz : sourceCommutator a b ^ 2 ∈ Subgroup.center G) :
    sourceCommutator a b⁻¹ ^ 2 = (sourceCommutator a b ^ 2)⁻¹ := by
  calc
    _ = b * (sourceCommutator a b ^ 2)⁻¹ * b⁻¹ := by
      dsimp [sourceCommutator]; simp only [pow_two]; group
    _ = _ := by rw [Subgroup.mem_center_iff.mp ((Subgroup.center G).inv_mem hz) b]; group

abbrev a : Central := centralGenerator false
abbrev b : Central := centralGenerator true
abbrev Ambient := Equiv.Perm Central

def conjugation : Central →* Ambient := (MulAut.toPerm Central).comp MulAut.conj

def translation : Subgroup.center Central →* Ambient :=
  (MulAction.toPermHom Central Central).comp (Subgroup.center Central).subtype

@[simp] theorem conjugation_apply (q x : Central) : conjugation q x = q * x * q⁻¹ := rfl
@[simp] theorem translation_apply (z : Subgroup.center Central) (x : Central) :
    translation z x = (z : Central) * x := rfl

theorem conjugation_central (z : Subgroup.center Central) : conjugation z = 1 := by
  ext x
  change (z : Central) * x * (z : Central)⁻¹ = x
  rw [← Subgroup.mem_center_iff.mp z.property x]
  simp [mul_assoc]

theorem translation_commute (q : Central) (z : Subgroup.center Central) :
    Commute (conjugation q) (translation z) := by
  apply Equiv.ext
  intro x
  change q * ((z : Central) * x) * q⁻¹ = (z : Central) * (q * x * q⁻¹)
  rw [← mul_assoc, Subgroup.mem_center_iff.mp z.property q]
  group

theorem conjugation_word (i : Fin 7) : word (conjugation a) (conjugation b) i = 1 := by
  rw [← map_word, ← centralRelator_val]
  exact conjugation_central (centralRelator i)

private theorem a_sq_central : a ^ 2 ∈ Subgroup.center Central := by
  simpa only [centralRelator_val, word, Matrix.cons_val_zero] using (centralRelator 0).property

private theorem right_five :
    (b * a * b⁻¹ * a * b)⁻¹ * a * (b * a * b⁻¹ * a * b) =
      a * (centralRelator 5 : Central) := by
  have he : b * a * b⁻¹ * a * b = a ^ 2 * (b * sourceCommutator a b) := by
    calc
      _ = b * a ^ 2 * (a⁻¹ * b⁻¹ * a * b) := by rw [pow_two]; group
      _ = _ := by rw [Subgroup.mem_center_iff.mp a_sq_central b]; rfl
  rw [he]
  calc
    _ = (b * sourceCommutator a b)⁻¹ * a * (b * sourceCommutator a b) := by rw [pow_two]; group
    _ = _ := by simpa [centralRelator_val, word] using cubic_conjugation a b a_sq_central

private theorem right_six :
    ((b ^ 2)⁻¹ * a * b ^ 2)⁻¹ * a * ((b ^ 2)⁻¹ * a * b ^ 2) =
      a * (centralRelator 6 : Central) := by
  simpa [centralRelator_val, word] using square_conjugation a (b ^ 2) a_sq_central

private theorem right_six_inverse :
    (b ^ 2 * a * (b ^ 2)⁻¹)⁻¹ * a * (b ^ 2 * a * (b ^ 2)⁻¹) =
      a * (centralRelator 6 : Central) := by
  have hz : sourceCommutator a (b ^ 2) ^ 2 ∈ Subgroup.center Central := by
    simpa [centralRelator_val, word] using (centralRelator 6).property
  have hinv : (centralRelator 6)⁻¹ = centralRelator 6 := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using centralRelator_six_sq
  have h := square_conjugation a ((b ^ 2)⁻¹) a_sq_central
  rw [inv_inv, inverse_commutator_square a (b ^ 2) hz] at h
  have he : sourceCommutator a (b ^ 2) ^ 2 = (centralRelator 6 : Central) :=
    (centralRelator_val 6).symm
  rw [he, ← Subgroup.coe_inv, hinv] at h
  exact h

private theorem right_four :
    (sourceCommutator a (b * a * b * a * b))⁻¹ * a *
      sourceCommutator a (b * a * b * a * b) = a * (centralRelator 4 : Central) := by
  rw [move_commutator a _ a_sq_central]
  simp [centralRelator_val, word, pow_two, mul_assoc]

/-- Two conjugations, three central translations, and four named stabilizer words. -/
def traceGenerator : Nat → Ambient
  | 0 => conjugation a
  | 1 => conjugation b
  | 2 => translation (centralRelator 4)
  | 3 => translation (centralRelator 5)
  | 4 => translation (centralRelator 6)
  | 5 => conjugation (b * a * b⁻¹ * a * b) * translation (centralRelator 5)
  | 6 => conjugation ((b ^ 2)⁻¹ * a * b ^ 2) * translation (centralRelator 6)
  | 7 => conjugation (b ^ 2 * a * (b ^ 2)⁻¹) * translation (centralRelator 6)
  | _ => conjugation (sourceCommutator a (b * a * b * a * b)) *
      translation (centralRelator 4)

def stabilizer : Subgroup Ambient := MulAction.stabilizer Ambient a

private theorem stabilizes (q : Central) (i : Fin 7)
    (hi : centralRelator i ^ 2 = 1)
    (hq : q⁻¹ * a * q = a * (centralRelator i : Central)) :
    conjugation q * translation (centralRelator i) ∈ stabilizer := by
  have hi' : (centralRelator i : Central) ^ 2 = 1 := congrArg Subtype.val hi
  have h := left_of_right a q (centralRelator i) (centralRelator i).property hi' hq
  change q * ((centralRelator i : Central) * a) * q⁻¹ = a
  let z : Central := centralRelator i
  have hc := Subgroup.mem_center_iff.mp (centralRelator i).property
  change q * (z * a) * q⁻¹ = a
  calc
    _ = z * (q * a * q⁻¹) := by
      rw [← mul_assoc q z, hc q]
      dsimp [z]; group
    _ = z * (a * z) := by rw [h]
    _ = a * (z * z) := by dsimp [z]; rw [← mul_assoc, ← hc a, mul_assoc]
    _ = a := by rw [← pow_two, hi', mul_one]

theorem generator_zero_mem : traceGenerator 0 ∈ stabilizer := by
  change a * a * a⁻¹ = a
  group

theorem generator_five_mem : traceGenerator 5 ∈ stabilizer :=
  stabilizes _ 5 centralRelator_five_sq right_five

theorem generator_six_mem : traceGenerator 6 ∈ stabilizer :=
  stabilizes _ 6 centralRelator_six_sq right_six

theorem generator_seven_mem : traceGenerator 7 ∈ stabilizer :=
  stabilizes _ 6 centralRelator_six_sq right_six_inverse

theorem generator_eight_mem : traceGenerator 8 ∈ stabilizer :=
  stabilizes _ 4 centralRelator_four_sq right_four

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.CommutatorIdentities
