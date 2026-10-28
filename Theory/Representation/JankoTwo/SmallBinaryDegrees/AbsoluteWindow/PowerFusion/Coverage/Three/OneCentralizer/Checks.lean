module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Three.OneCentralizer.Data
import Mathlib.Tactic.FinCases

/-!
# Checked equations for the first cubic centralizer

Commutation and fusion for the 1080 candidate centralizer rows, and conjugation
for the 560 orbit rows, are checked on the certified four-point base. Decoding
identities give distinctness in linear many checks. Separate sequential blocks
of 27 centralizer rows or 28 orbit rows bound kernel reduction memory.

Source: retained ATLAS `J2G1-p100B0` normal forms and the witnesses in
`OneCentralizer/source/`. External computations supply witnesses only.
-/

namespace Sporadic.LeechRelated.J2.PowerFusionCertificate.OneCentralizerCertificates
open GeneratorPair.SecondOrbitCertificate

set_option Elab.async false

private def centralBlockIndex (b : Fin 40) (j : Fin 27) : Fin 1080 :=
  ⟨27 * b.val + j.val, by omega⟩

private def orbitBlockIndex (b : Fin 20) (j : Fin 28) : Fin 560 :=
  ⟨28 * b.val + j.val, by omega⟩

private def CommuteRow (i : Fin 1080) : Prop := ∀ k : Fin 4,
  normalForm (centralIndex i)
    (normalForm (representativeIndex 1) (k.castLE (by decide))) =
  normalForm (representativeIndex 1)
    (normalForm (centralIndex i) (k.castLE (by decide)))

private def FusionRow (i : Fin 1080) : Prop := ∀ k : Fin 4,
  normalForm (fusionConjugator i)
    (normalForm (representativeIndex (fusionClass i)) (k.castLE (by decide))) =
  normalForm (centralIndex i)
    (normalForm (fusionConjugator i) (k.castLE (by decide)))

private def OrbitRow (i : Fin 560) : Prop := ∀ k : Fin 4,
  normalForm (representativeIndex 1)
    (normalForm (rightRepresentative i) (k.castLE (by decide))) =
  normalForm (rightRepresentative i)
    (normalForm (orbitIndex i) (k.castLE (by decide)))

private theorem commuteBlock00 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 0 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock01 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 1 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock02 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 2 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock03 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 3 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock04 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 4 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock05 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 5 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock06 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 6 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock07 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 7 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock08 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 8 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock09 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 9 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock10 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 10 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock11 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 11 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock12 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 12 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock13 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 13 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock14 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 14 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock15 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 15 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock16 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 16 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock17 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 17 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock18 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 18 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock19 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 19 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock20 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 20 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock21 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 21 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock22 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 22 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock23 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 23 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock24 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 24 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock25 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 25 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock26 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 26 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock27 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 27 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock28 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 28 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock29 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 29 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock30 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 30 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock31 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 31 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock32 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 32 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock33 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 33 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock34 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 34 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock35 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 35 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock36 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 36 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock37 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 37 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock38 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 38 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commuteBlock39 : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex 39 j) := by
  unfold CommuteRow
  apply allFin
  decide +kernel

private theorem commute_block (b : Fin 40) : ∀ j : Fin 27,
    CommuteRow (centralBlockIndex b j) := by
  fin_cases b
  · exact commuteBlock00
  · exact commuteBlock01
  · exact commuteBlock02
  · exact commuteBlock03
  · exact commuteBlock04
  · exact commuteBlock05
  · exact commuteBlock06
  · exact commuteBlock07
  · exact commuteBlock08
  · exact commuteBlock09
  · exact commuteBlock10
  · exact commuteBlock11
  · exact commuteBlock12
  · exact commuteBlock13
  · exact commuteBlock14
  · exact commuteBlock15
  · exact commuteBlock16
  · exact commuteBlock17
  · exact commuteBlock18
  · exact commuteBlock19
  · exact commuteBlock20
  · exact commuteBlock21
  · exact commuteBlock22
  · exact commuteBlock23
  · exact commuteBlock24
  · exact commuteBlock25
  · exact commuteBlock26
  · exact commuteBlock27
  · exact commuteBlock28
  · exact commuteBlock29
  · exact commuteBlock30
  · exact commuteBlock31
  · exact commuteBlock32
  · exact commuteBlock33
  · exact commuteBlock34
  · exact commuteBlock35
  · exact commuteBlock36
  · exact commuteBlock37
  · exact commuteBlock38
  · exact commuteBlock39

private theorem commute_row (i : Fin 1080) : CommuteRow i := by
  let b : Fin 40 := ⟨i.val / 27, by omega⟩
  let j : Fin 27 := ⟨i.val % 27, Nat.mod_lt _ (by decide)⟩
  have he : centralBlockIndex b j = i := by
    apply Fin.ext
    simp only [centralBlockIndex, b, j]
    omega
  exact he ▸ commute_block b j

private theorem fusionBlock00 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 0 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock01 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 1 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock02 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 2 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock03 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 3 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock04 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 4 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock05 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 5 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock06 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 6 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock07 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 7 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock08 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 8 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock09 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 9 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock10 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 10 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock11 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 11 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock12 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 12 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock13 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 13 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock14 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 14 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock15 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 15 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock16 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 16 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock17 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 17 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock18 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 18 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock19 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 19 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock20 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 20 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock21 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 21 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock22 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 22 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock23 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 23 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock24 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 24 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock25 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 25 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock26 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 26 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock27 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 27 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock28 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 28 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock29 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 29 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock30 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 30 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock31 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 31 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock32 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 32 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock33 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 33 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock34 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 34 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock35 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 35 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock36 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 36 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock37 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 37 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock38 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 38 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusionBlock39 : ∀ j : Fin 27,
    FusionRow (centralBlockIndex 39 j) := by
  unfold FusionRow
  apply allFin
  decide +kernel

private theorem fusion_block (b : Fin 40) : ∀ j : Fin 27,
    FusionRow (centralBlockIndex b j) := by
  fin_cases b
  · exact fusionBlock00
  · exact fusionBlock01
  · exact fusionBlock02
  · exact fusionBlock03
  · exact fusionBlock04
  · exact fusionBlock05
  · exact fusionBlock06
  · exact fusionBlock07
  · exact fusionBlock08
  · exact fusionBlock09
  · exact fusionBlock10
  · exact fusionBlock11
  · exact fusionBlock12
  · exact fusionBlock13
  · exact fusionBlock14
  · exact fusionBlock15
  · exact fusionBlock16
  · exact fusionBlock17
  · exact fusionBlock18
  · exact fusionBlock19
  · exact fusionBlock20
  · exact fusionBlock21
  · exact fusionBlock22
  · exact fusionBlock23
  · exact fusionBlock24
  · exact fusionBlock25
  · exact fusionBlock26
  · exact fusionBlock27
  · exact fusionBlock28
  · exact fusionBlock29
  · exact fusionBlock30
  · exact fusionBlock31
  · exact fusionBlock32
  · exact fusionBlock33
  · exact fusionBlock34
  · exact fusionBlock35
  · exact fusionBlock36
  · exact fusionBlock37
  · exact fusionBlock38
  · exact fusionBlock39

private theorem fusion_row (i : Fin 1080) : FusionRow i := by
  let b : Fin 40 := ⟨i.val / 27, by omega⟩
  let j : Fin 27 := ⟨i.val % 27, Nat.mod_lt _ (by decide)⟩
  have he : centralBlockIndex b j = i := by
    apply Fin.ext
    simp only [centralBlockIndex, b, j]
    omega
  exact he ▸ fusion_block b j

private theorem orbitBlock00 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 0 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock01 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 1 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock02 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 2 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock03 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 3 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock04 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 4 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock05 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 5 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock06 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 6 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock07 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 7 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock08 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 8 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock09 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 9 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock10 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 10 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock11 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 11 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock12 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 12 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock13 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 13 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock14 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 14 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock15 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 15 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock16 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 16 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock17 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 17 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock18 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 18 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbitBlock19 : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex 19 j) := by
  unfold OrbitRow
  apply allFin
  decide +kernel

private theorem orbit_block (b : Fin 20) : ∀ j : Fin 28,
    OrbitRow (orbitBlockIndex b j) := by
  fin_cases b
  · exact orbitBlock00
  · exact orbitBlock01
  · exact orbitBlock02
  · exact orbitBlock03
  · exact orbitBlock04
  · exact orbitBlock05
  · exact orbitBlock06
  · exact orbitBlock07
  · exact orbitBlock08
  · exact orbitBlock09
  · exact orbitBlock10
  · exact orbitBlock11
  · exact orbitBlock12
  · exact orbitBlock13
  · exact orbitBlock14
  · exact orbitBlock15
  · exact orbitBlock16
  · exact orbitBlock17
  · exact orbitBlock18
  · exact orbitBlock19

private theorem orbit_row (i : Fin 560) : OrbitRow i := by
  let b : Fin 20 := ⟨i.val / 28, by omega⟩
  let j : Fin 28 := ⟨i.val % 28, Nat.mod_lt _ (by decide)⟩
  have he : orbitBlockIndex b j = i := by
    apply Fin.ext
    simp only [orbitBlockIndex, b, j]
    omega
  exact he ▸ orbit_block b j

/-- Checked commutation on the four-point carrier base. -/
public theorem commute_check (i : Fin 1080) (k : Fin 4) :
    normalForm (centralIndex i)
      (normalForm (representativeIndex 1) (k.castLE (by decide))) =
    normalForm (representativeIndex 1)
      (normalForm (centralIndex i) (k.castLE (by decide))) := commute_row i k

/-- Checked fusion inside the carrier, with the literal conjugator convention. -/
public theorem fusion_check (i : Fin 1080) (k : Fin 4) :
    normalForm (fusionConjugator i)
      (normalForm (representativeIndex (fusionClass i)) (k.castLE (by decide))) =
    normalForm (centralIndex i)
      (normalForm (fusionConjugator i) (k.castLE (by decide))) := fusion_row i k

/-- Checked conjugation equation for a right-coset representative. -/
public theorem orbit_check (i : Fin 560) (k : Fin 4) :
    normalForm (representativeIndex 1)
      (normalForm (rightRepresentative i) (k.castLE (by decide))) =
    normalForm (rightRepresentative i)
      (normalForm (orbitIndex i) (k.castLE (by decide))) := orbit_row i k

private theorem central_decode : ∀ i : Fin 1080, centralDecode (centralIndex i) = i.val := by
  apply allFin
  decide +kernel

private theorem orbit_decode : ∀ i : Fin 560, orbitDecode (orbitIndex i) = i.val := by
  apply allFin
  decide +kernel

/-- The 1080 commuting normal-form indices are distinct, by decoding. -/
public theorem centralIndex_injective : Function.Injective centralIndex := by
  intro i j h
  apply Fin.ext
  have hd := congrArg centralDecode h
  simpa only [central_decode] using hd

/-- The 560 conjugate normal-form indices are distinct, by decoding. -/
public theorem orbitIndex_injective : Function.Injective orbitIndex := by
  intro i j h
  apply Fin.ext
  have hd := congrArg orbitDecode h
  simpa only [orbit_decode] using hd

end Sporadic.LeechRelated.J2.PowerFusionCertificate.OneCentralizerCertificates
