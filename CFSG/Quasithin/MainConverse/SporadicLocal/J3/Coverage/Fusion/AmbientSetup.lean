module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Fusion.ClassData
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.S0
import Mathlib.Tactic.FinCases

/-!
# Fast permutation expressions for the J₃ ambient fusion certificate

The five packed Sylow generators have already been checked against the fixed
model words. Reusing them makes the 58 remaining generator-image checks short.
The ambient conjugator is still the supplied word in the certified stabilizer
chain, with its equality to the model element proved here.

Source: GLS, Number 3, Table 5.3h, printed p.269; the retained ATLAS model.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.Fusion
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal
open Theory.GroupTheory Sporadic.Janko3.OrderCertificate
open Sporadic.Janko3.TwoLocal.CentralizerCertificate

@[expose] public def fastSylowGenerator (i : Fin 5) : Equiv.Perm (Fin 6156) :=
  S0Gen ⟨i.val, by omega⟩

public theorem fastSylowGenerator_eq (i : Fin 5) :
    fastSylowGenerator i = embedding (sylowGenerator i) := by
  fin_cases i <;>
    simp only [fastSylowGenerator, S0Gen, S0G0_eq_generator, S0G1_eq_generator,
      S0G2_eq_generator, S0G3_eq_generator, S0G4_eq_generator]
  all_goals rfl

@[expose] public def fastElement (i : Fin 128) : Equiv.Perm (Fin 6156) :=
  evalWord fastSylowGenerator (sylowEnumerationWord i)

private theorem fastWord_eq (w : List (Fin 5)) :
    evalWord fastSylowGenerator w = embedding (evalWord sylowGenerator w) := by
  induction w with
  | nil => exact (map_one embedding).symm
  | cons i w ih => simp only [evalWord, map_mul, ← fastSylowGenerator_eq, ← ih]

public theorem fastElement_eq (i : Fin 128) : fastElement i = embedding (element i) :=
  fastWord_eq _

public theorem fastElement_elementary (j : Fin 4) :
    fastElement (elementaryGeneratorIndex j) = embedding (elementaryGenerator j) := by
  rw [fastElement_eq]
  exact congrArg embedding (elementaryGenerator_eq_sylowEnumeration j).symm

@[expose] public def fastConjugator (c : Fin 28) : Equiv.Perm (Fin 6156) :=
  evalWord fastL0Gen (conjugatorWord0 c) * evalWord L1Gen (conjugatorWord1 c) *
    evalWord L2Gen (conjugatorWord2 c)

public theorem fastConjugator_eq (c : Fin 28) :
    fastConjugator c = embedding (ambientConjugator c) := by
  rw [fastConjugator, fastL0Gen_eq]
  rfl

/-- A commuting-square check on all 6156 letters proves a model conjugacy
identity, without constructing or evaluating a new inverse permutation. -/
public theorem generator_image_of_pointwise (c : Fin 28) (j : Fin 4)
    (h : ∀ x : Fin 6156,
      fastConjugator c (fastElement (elementaryGeneratorIndex j) x) =
        fastElement (generatorImage c j) (fastConjugator c x)) :
    (MulAut.conj (ambientConjugator c)) (elementaryGenerator j) =
      element (generatorImage c j) := by
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change embedding (ambientConjugator c * elementaryGenerator j) =
    embedding (element (generatorImage c j) * ambientConjugator c)
  simp only [map_mul, ← fastConjugator_eq, ← fastElement_elementary, ← fastElement_eq]
  exact Equiv.ext h

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.Fusion
