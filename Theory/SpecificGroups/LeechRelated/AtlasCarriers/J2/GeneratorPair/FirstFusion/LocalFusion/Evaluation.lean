module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.LocalFusion.Data
import Mathlib.Tactic.FinCases

/-!
# Evaluation of the packed J₂ centralizer letters

The packed three-letter alphabet is checked against the literal carrier
permutations. Word evaluation then transports point calculations to `Carrier`.
Source: ATLAS `J2G1-p100B0`, in the convention of `GeneratorPair`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.LocalCertificate
open Theory.GroupTheory
set_option maxRecDepth 100000
set_option Elab.async false

def wordValue : List (Fin 3) → Fin 100 → Fin 100
  | [], p => p
  | s :: w, p => letterValue s (wordValue w p)

theorem wordValue_spec (w : List (Fin 3)) (p : Fin 100) :
    wordValue w p = inclusion (evalWord letter w) p := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    rw [wordValue, ih, letterValue_eq]
    simp only [evalWord, map_mul, inclusion_letter, Equiv.Perm.mul_apply]

theorem inclusion_word (w : List (Fin 3)) :
    inclusion (evalWord letter w) = evalWord permLetter w := by
  induction w with
  | nil => exact map_one _
  | cons s w ih => simp only [evalWord, map_mul, inclusion_letter, ih]

def cPerm : Equiv.Perm (Fin 100) :=
  evalWord permLetter (OrbitData.words 263) * tableB *
    (evalWord permLetter (OrbitData.words 273))⁻¹

theorem inclusion_c : inclusion c = cPerm := by
  have hn : OrbitData.next 263 1 = 273 := by decide +kernel
  simp only [c, schreier, hn, map_mul, map_inv, rep, inclusion_word, inclusion_letter]
  rfl

theorem localLetterValue_eq : ∀ (s : Fin 3) (p : Fin 100),
    localLetterValue s p = inclusion (centralizerLetter s) p := by
  intro s
  fin_cases s
  · change ∀ p, localLetterValue 0 p = generatorA p
    rw [generatorA_eq_table]
    apply allFin
    decide +kernel
  · change ∀ p, localLetterValue 1 p = inclusion c p
    rw [inclusion_c]
    apply allFin
    decide +kernel
  · change ∀ p, localLetterValue 2 p = inclusion (c⁻¹) p
    rw [map_inv, inclusion_c]
    apply allFin
    decide +kernel

theorem checkedAt {n : Nat} {f : Fin n → Bool} (h : checkFin f = true) (i : Fin n) :
    f i = true := by
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt] using hi

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.LocalCertificate
