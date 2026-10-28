module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Base
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.StabilizerWords
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.Words

/-!
# Transport of the exact first-four word subgroups

The polymorphic word lists agree with every literal `StabilizerWords` list
through stage four. Applying the ambient subgroup inclusion identifies their
images as subgroups of the full symmetric group. The corresponding base words
also agree. Consequently a concrete permutation model can supply the four
stabilizer reductions once its two generators are compared with the original
candidate words on all ambient letters.

This transport does not use restriction to the 31671-letter orbit or assume
that restriction is faithful. Source: GLS3 Table 5.3v; ATLAS F24G1-p306936B0.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel

/-- The generic word lists specialize to the literal, shared stage lists. -/
theorem generators_eq_actual (i : Fin 5) :
    Word.generators aLift bLift i = StabilizerWords.generators (i.castAdd 4) := by
  fin_cases i <;> rfl

/-- The four proposed base words have not changed in the finite model. -/
theorem baseWord_eq_actual (i : Fin 4) :
    Word.baseWord i = baseWord (i.castAdd 4) := by
  fin_cases i <;> rfl

/-- The generic stage inside the original ambient carrier is exactly `wordStage`. -/
theorem stage_eq_actual (i : Fin 5) :
    Word.stage candidateA candidateB i = wordStage (i.castAdd 4) := by
  unfold Word.stage wordStage
  have h := Word.map_generators liftedGroup.subtype aLift bLift i
  change (Word.generators aLift bLift i).map Subtype.val =
    Word.generators candidateA candidateB i at h
  rw [← h, generators_eq_actual]

/-- The inclusion in the full symmetric group preserves every marked stage. -/
theorem map_actual_stage (i : Fin 5) :
    (wordStage (i.castAdd 4)).map generated.subtype =
      Word.stage candidateA.val candidateB.val i := by
  rw [← stage_eq_actual, Word.map_stage]
  rfl

/-- Membership in a stage can be checked after the injective ambient inclusion. -/
theorem mem_actual_stage_iff (i : Fin 5) (g : Carrier) :
    g ∈ wordStage (i.castAdd 4) ↔ g.val ∈ Word.stage candidateA.val candidateB.val i := by
  rw [← map_actual_stage]
  exact (Subgroup.mem_map_iff_mem Subtype.val_injective).symm

/-- The marked points are the same evaluations in the full symmetric group. -/
theorem point_eq_actual (i : Fin 4) :
    Word.evaluate candidateA.val candidateB.val (Word.baseWord i) 508 =
      basePoint (i.castAdd 4) := by
  have h₁ := Word.map_evaluate liftedGroup.subtype aLift bLift (baseWord (i.castAdd 4))
  have h₂ := Word.map_evaluate generated.subtype candidateA candidateB (baseWord (i.castAdd 4))
  change (Word.evaluate aLift bLift _).val = Word.evaluate candidateA candidateB _ at h₁
  change (Word.evaluate candidateA candidateB _).val =
    Word.evaluate candidateA.val candidateB.val _ at h₂
  rw [baseWord_eq_actual, ← h₂, ← h₁]
  rfl

/-- Transport four actual point-stabilizer inclusions from a compared pair of
permutations. Both comparison premises must be proved on the full ambient set. -/
theorem actual_reductions_of_compared_permutations
    (a b : Equiv.Perm (Fin 306936))
    (ha : candidateA.val = a) (hb : candidateB.val = b)
    (step : ∀ i : Fin 4, ∀ g : Equiv.Perm (Fin 306936),
      g ∈ Word.stage a b i.castSucc →
      g (Word.evaluate a b (Word.baseWord i) 508) =
        Word.evaluate a b (Word.baseWord i) 508 →
      g ∈ Word.stage a b i.succ) :
    ∀ i : Fin 4, ∀ g : Carrier, g ∈ wordStage (i.castAdd 4).castSucc →
      g.val (basePoint (i.castAdd 4)) = basePoint (i.castAdd 4) →
      g ∈ wordStage (i.castAdd 4).succ := by
  intro i g hg hfix
  apply (mem_actual_stage_iff i.succ g).mpr
  rw [ha, hb]
  apply step i g.val
  · rw [← ha, ← hb]
    exact (mem_actual_stage_iff i.castSucc g).mp hg
  · rw [← ha, ← hb, point_eq_actual]
    exact hfix

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
