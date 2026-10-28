module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Representatives
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Check

/-!
# Packed evaluation for the Fi23 exhaustion words

The shared packed source maps evaluate the representative and candidate
words. Their agreement with the exact ATLAS permutations remains an explicit
premise, owned by the independent `Comparison.SourceActions` certificate.
This allows the numerical separation check to run independently of that proof.

Source: ATLAS F23G1-p31671B0; application: GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion
open Fi24Prime.Fi23Lift.Certificate

def packedLetter (b : Bool) (x : Fin 31671) : Fin 31671 :=
  if b then sourceB x else sourceA x

def representativeAction (x y : Fin 31671) : Fin 31671 :=
  ((wordCode x).bits.dropLast).foldr packedLetter y

def wordAction (x : Fin 31671) : Fin 31671 :=
  sourceA (sourceB (sourceB (sourceA (sourceB (sourceB
    (sourceA (sourceB (sourceA (sourceB (sourceA (sourceB x)))))))))))

def candidateAction (x : Fin 31671) : Fin 31671 := (wordAction^[7]) x

variable (hA : ∀ x, generatorA x = sourceA x) (hB : ∀ x, generatorB x = sourceB x)
include hA hB

theorem packedLetter_eq (b : Bool) (x : Fin 31671) :
    packedLetter b x = inclusion (letter b) x := by
  cases b
  · exact (hA x).symm
  · exact (hB x).symm

theorem representativeAction_eq (x y : Fin 31671) :
    representativeAction x y = inclusion (representative x) y := by
  have hf : ∀ bs : List Bool, bs.foldr packedLetter y =
      inclusion ((bs.map letter).prod) y := by
    intro bs
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simpa only [List.foldr_cons, List.map_cons, List.prod_cons, map_mul,
        Equiv.Perm.mul_apply, packedLetter_eq hA hB] using
          congrArg (inclusion (letter b)) ih
  exact hf _

theorem wordAction_eq (x : Fin 31671) : wordAction x = inclusion word x := by
  simp only [wordAction, ← hA, ← hB, word, map_mul, pow_succ,
    pow_zero, Equiv.Perm.mul_apply]
  rfl

theorem candidateAction_eq (x : Fin 31671) : candidateAction x = inclusion candidate x := by
  have hw : wordAction = inclusion word := funext (wordAction_eq hA hB)
  simp only [candidateAction, hw, candidate, map_pow, Equiv.Perm.coe_pow]

/-- One letter is sufficient to separate every nonbase representative. -/
def separationCheck (i : Nat) : Bool :=
  let x : Fin 31671 := ⟨i % 31671, Nat.mod_lt _ (by decide)⟩
  decide (representativeAction x (candidateAction 0) ≠
    candidateAction (representativeAction x 0) ∨ x = base)

-- Keep multiplication/application conversion abstract: specializing a raw
-- `congrArg` at the concrete candidate otherwise unfolds its large cycle data.
omit hA hB in
private theorem commute_apply {α : Type*} (p q : Equiv.Perm α)
    (h : p * q = q * p) (z : α) : p (q z) = q (p z) :=
  congrArg (fun r : Equiv.Perm α => r z) h

/-- Consume a finite kernel certificate at the literal commutator equation. -/
theorem representative_separated_of_check
    (hcheck : checkPow separationCheck 0 15 = true) (x : Fin 31671)
    (hx : representative x * candidate = candidate * representative x) : x = base := by
  have hc := checkPow_sound separationCheck 15 0 hcheck x.val (Nat.zero_le _)
    (Nat.lt_trans x.isLt (by decide))
  have hs : representativeAction x (candidateAction 0) ≠
      candidateAction (representativeAction x 0) ∨ x = base := by
    simpa only [separationCheck, Nat.mod_eq_of_lt x.isLt, decide_eq_true_eq] using hc
  refine hs.resolve_left (not_not.mpr ?_)
  simp only [representativeAction_eq hA hB, candidateAction_eq hA hB]
  have he := congrArg inclusion hx
  rw [map_mul, map_mul] at he
  exact commute_apply _ _ he 0

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion
