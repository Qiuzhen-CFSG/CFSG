module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.OrbitData
import Mathlib.Tactic.FinCases

/-!
# Actual J₂ elements representing the two proposed partner orbits

The five supplied words define elements of the actual ATLAS-generated carrier.
Their permutation tables are checked against those words and are checked to
centralize `a`. The 240 further words therefore give actual centralizing
elements. Conjugating `b` and `b⁻¹` gives a family of 480 partners, each with
its required witness inside J₂. Exhaustiveness is a separate finite check.

Source: the retained ATLAS `J2G1-p100B0` permutations; GLS3, Table 5.3g for
the outer-group application. GAP supplies word witnesses only; all equalities
used below are checked in Lean.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
open Theory.GroupTheory
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

/-- The signed alphabet consists of elements of the actual carrier. -/
def carrierLetter : Fin 4 → Carrier := ![a, b, a⁻¹, b⁻¹]

/-- The same signed alphabet using the verified generator tables. -/
def tableLetter : Fin 4 → Equiv.Perm (Fin 100) :=
  ![tableA, tableB, tableA⁻¹, tableB⁻¹]

theorem a_inclusion : inclusion a = tableA := generatorA_eq_table

theorem b_inclusion : inclusion b = tableB := generatorB_eq_table

theorem carrierLetter_inclusion (i : Fin 4) :
    inclusion (carrierLetter i) = tableLetter i := by
  fin_cases i <;>
    simp [carrierLetter, tableLetter, map_inv, a_inclusion, b_inclusion]

private theorem inclusion_evalWord {n : Nat} (gen : Fin n → Carrier)
    (w : List (Fin n)) :
    inclusion (evalWord gen w) = evalWord (fun i => inclusion (gen i)) w := by
  induction w with
  | nil => exact map_one inclusion
  | cons i w ih => rw [evalWord, map_mul, ih, evalWord]

/-- Five explicit words in the defining generators. -/
def centralizerGenerator (i : Fin 5) : Carrier :=
  evalWord carrierLetter (centralizerGeneratorWord i)

private theorem centralizerGenerator_word_check : ∀ i,
    evalWord tableLetter (centralizerGeneratorWord i) = centralizerGeneratorTable i := by
  apply allFin
  decide +kernel

theorem centralizerGenerator_inclusion (i : Fin 5) :
    inclusion (centralizerGenerator i) = centralizerGeneratorTable i := by
  rw [centralizerGenerator, inclusion_evalWord]
  simpa only [carrierLetter_inclusion] using centralizerGenerator_word_check i

private theorem centralizerGenerator_conj_check : ∀ i,
    MulAut.conj (centralizerGeneratorTable i) tableA = tableA := by
  apply allFin
  decide +kernel

theorem centralizerGenerator_centralizes (i : Fin 5) :
    MulAut.conj (centralizerGenerator i) a = a := by
  apply inclusion_injective
  simpa only [MulAut.conj_apply, map_mul, map_inv, centralizerGenerator_inclusion,
    a_inclusion] using centralizerGenerator_conj_check i

/-- The supplied 240 words, interpreted inside J₂. -/
def conjugator (i : Fin 240) : Carrier :=
  evalWord centralizerGenerator (conjugatorWord i)

private theorem conjugator_word_check : ∀ i,
    evalWord centralizerGeneratorTable (conjugatorWord i) = conjugatorTable i := by
  apply allFin
  decide +kernel

theorem conjugator_inclusion (i : Fin 240) :
    inclusion (conjugator i) = conjugatorTable i := by
  rw [conjugator, inclusion_evalWord]
  simpa only [centralizerGenerator_inclusion] using conjugator_word_check i

theorem conjugator_centralizes (i : Fin 240) : MulAut.conj (conjugator i) a = a := by
  have hw (w : List (Fin 5)) : MulAut.conj (evalWord centralizerGenerator w) a = a := by
    induction w with
    | nil => simp [evalWord]
    | cons j w ih =>
      rw [evalWord, map_mul, MulAut.mul_apply, ih, centralizerGenerator_centralizes]
  exact hw (conjugatorWord i)

/-- False selects the orbit of `b`; true selects the orbit of `b⁻¹`. -/
def partner (i : Fin 240) (inverse : Bool) : Carrier :=
  MulAut.conj (conjugator i) (if inverse then b⁻¹ else b)

/-- The table interpretation used by the exhaustive finite search. -/
def partnerTable (i : Fin 240) (inverse : Bool) : Equiv.Perm (Fin 100) :=
  MulAut.conj (conjugatorTable i) (if inverse then tableB⁻¹ else tableB)

theorem partner_inclusion (i : Fin 240) (inverse : Bool) :
    inclusion (partner i inverse) = partnerTable i inverse := by
  cases inverse <;>
    simp only [partner, partnerTable, Bool.false_eq_true, ↓reduceIte,
      MulAut.conj_apply, map_mul, map_inv, conjugator_inclusion, b_inclusion]

/-- Every supplied partner has a centralizing conjugator in the exact carrier. -/
theorem partner_has_orbit (i : Fin 240) (inverse : Bool) :
    ∃ c : Carrier, MulAut.conj c a = a ∧
      (partner i inverse = MulAut.conj c b ∨
       partner i inverse = MulAut.conj c b⁻¹) := by
  refine ⟨conjugator i, conjugator_centralizes i, ?_⟩
  cases inverse
  · exact Or.inl rfl
  · exact Or.inr rfl

end Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
