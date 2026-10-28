module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.Representatives
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Base
public import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Tactic.FinCases

/-!
# Seven adjacent transpositions in the exact HS centralizer

The seven involutions below are words in the two defining HS generators.
Their Coxeter relations of type A₇ and commutation with `symmetricPermutation`
are checked on all 100 letters. Thus they define a homomorphism from S₈
via its Coxeter presentation; the next module proves this map injective.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 Table 5.3m, class 2D.
The retained GAP search supplies candidate tables and words only. Every asserted
identity, including membership in the exact carrier, is checked in Lean's kernel.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.SymmetricCentralizer
open Sporadic.LeechRelated.HS OrderCertificate Theory.GroupTheory
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

private def wordGen (i : Fin 3) : Equiv.Perm (Fin 100) :=
  match i.val with
  | 0 => p0
  | 1 => p1
  | _ => p1⁻¹

private theorem wordGen_mem (i : Fin 3) : wordGen i ∈ generated := by
  have ha : p0 ∈ generated := by
    rw [a_eq_generator]
    exact Subgroup.subset_closure (by simp)
  have hb : p1 ∈ generated := by
    rw [b_eq_generator]
    exact Subgroup.subset_closure (by simp)
  fin_cases i
  · exact ha
  · exact hb
  · exact generated.inv_mem hb

private theorem evalWord_mem (w : List (Fin 3)) : evalWord wordGen w ∈ generated := by
  induction w with
  | nil => exact generated.one_mem
  | cons i w ih => exact generated.mul_mem (wordGen_mem i) ih

private def generatorCodes : List ℕ :=
  [1567537458752845055784565388741109618389245422661489762506635364433890088665521936086314253589367524069163363649114897644137721089512690397873728463887863562688989701302519385859899531761364090951190659287407124,
   3741308519231724182102445775113065506420077169938550343353982493752360752852137038890682709277947478982391411514823811339630120046550343453292357107982769867283248031495208373461079624037097818915598109198667316,
   961710403894258893952835291160279996709901094782800185225693056520942847982696523961852691354952688528041480401687429351257881561966933630868491485131583839069202995699301073307904898551497825666520401208397323,
   3755480021752553605214827806833068583533648925962178808068511097218093901335747156516853446136171438270512897209422171593671534536735681663506413833566488196596398669013831555834640971029908646161468288985537986,
   3756079483845472820486596404959074031516771984732526486845479244992192472339486986034489392466980497334378804559343236759445060069084691763743488037309216428875307680691876445600901585022102051608571862837906440,
   1126009018659511979023145781700384747662926563954776031383194758971347601424308450904915310759831224518290707660765963367941895032098982830310214502350539655769318857390254590266865914105962858462819035017488137,
   3744843714637216420406561295780967048130608461687866435131996925628429030295818404574475578265273442376057136292800014167622180517503294871999994475312296981841618063841649272783518256750717997947844194518732308]

/-- The checked degree-100 realization of the seven adjacent transpositions. -/
private def generatorMap (i : Fin 7) (x : Fin 100) : Fin 100 :=
  ⟨(generatorCodes[i.val]! >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem generatorMap_involutive :
    ∀ i : Fin 7, ∀ x : Fin 100, generatorMap i (generatorMap i x) = x := by
  apply allFin
  decide +kernel

def generator (i : Fin 7) : Equiv.Perm (Fin 100) :=
  tablePerm (generatorMap i) (generatorMap i)
    (by exact generatorMap_involutive i) (by exact generatorMap_involutive i)

private def generatorWord0 : List (Fin 3) := [1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 2, 0, 1, 1, 0, 2, 0, 1, 1, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 1]

private theorem generatorWord0_eq : evalWord wordGen generatorWord0 = generator 0 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem generator0_mem : generator 0 ∈ generated :=
  generatorWord0_eq ▸ evalWord_mem generatorWord0

private def generatorWord1 : List (Fin 3) := [1, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 1]

private theorem generatorWord1_eq : evalWord wordGen generatorWord1 = generator 1 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem generator1_mem : generator 1 ∈ generated :=
  generatorWord1_eq ▸ evalWord_mem generatorWord1

private def generatorWord2 : List (Fin 3) := [1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 0, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 1]

private theorem generatorWord2_eq : evalWord wordGen generatorWord2 = generator 2 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem generator2_mem : generator 2 ∈ generated :=
  generatorWord2_eq ▸ evalWord_mem generatorWord2

private def generatorWord3 : List (Fin 3) := [0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 2, 0, 1, 1, 0, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2]

private theorem generatorWord3_eq : evalWord wordGen generatorWord3 = generator 3 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem generator3_mem : generator 3 ∈ generated :=
  generatorWord3_eq ▸ evalWord_mem generatorWord3

private def generatorWord4 : List (Fin 3) := [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2]

private theorem generatorWord4_eq : evalWord wordGen generatorWord4 = generator 4 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem generator4_mem : generator 4 ∈ generated :=
  generatorWord4_eq ▸ evalWord_mem generatorWord4

private def generatorWord5 : List (Fin 3) := [0, 1, 0, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2]

private theorem generatorWord5_eq : evalWord wordGen generatorWord5 = generator 5 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem generator5_mem : generator 5 ∈ generated :=
  generatorWord5_eq ▸ evalWord_mem generatorWord5

private def generatorWord6 : List (Fin 3) := [1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 1]

private theorem generatorWord6_eq : evalWord wordGen generatorWord6 = generator 6 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem generator6_mem : generator 6 ∈ generated :=
  generatorWord6_eq ▸ evalWord_mem generatorWord6

theorem generator_mem (i : Fin 7) : generator i ∈ generated := by
  fin_cases i
  · exact generator0_mem
  · exact generator1_mem
  · exact generator2_mem
  · exact generator3_mem
  · exact generator4_mem
  · exact generator5_mem
  · exact generator6_mem

/-- The seven generators centralize the specified representative. -/
theorem generator_commutes (i : Fin 7) :
    symmetricPermutation * generator i = generator i * symmetricPermutation := by
  have h : ∀ i : Fin 7, ∀ x : Fin 100,
      (symmetricPermutation * generator i) x = (generator i * symmetricPermutation) x := by
    apply allFin
    decide +kernel
  exact Equiv.ext (h i)

/-- All type-A₇ Coxeter relations, checked as permutation identities. -/
theorem generator_relations : CoxeterMatrix.IsLiftable (CoxeterMatrix.A 7) generator := by
  have h : ∀ i j : Fin 7, ∀ x : Fin 100,
      ((generator i * generator j) ^ (CoxeterMatrix.A 7 i j)) x = x := by
    apply allFin
    decide +kernel
  intro i j
  exact Equiv.ext (h i j)

theorem generator_product_ne_one : generator 0 * generator 1 ≠ 1 := by
  intro h
  have hval := congrArg (fun p : Equiv.Perm (Fin 100) => p 0) h
  have hn : (generator 0 * generator 1) 0 ≠ (1 : Equiv.Perm (Fin 100)) 0 := by
    decide +kernel
  exact hn hval

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.SymmetricCentralizer
