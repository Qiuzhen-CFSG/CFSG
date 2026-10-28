module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.CandidateTables.Reduction
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.InverseCheck

/-!
# Soundness of the full-ambient staged numerical tests

Each test contains only inverse laws or short compositions of packed maps.
Balanced checks can certify bounded intervals and then apply
`FirstFourModel.covered_checks`
to cover every ambient letter. The source words are separate obligations;
`Reduction` uses the records constructed here to assemble the exact candidates.
No exhaustive numerical test is asserted to have passed by this module.
Source: ATLAS F24G1-p306936B0 and the exact `WordSetup` candidates.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables
open Certificate

/-- Four proposed inverse laws; indices beyond the degree wrap harmlessly. -/
def inverseTest (i : Nat) : Bool :=
  let x := Fin.ofNat 306936 i
  decide (uMap (uInvMap x) = x ∧ vMap (vInvMap x) = x ∧
    wMap (wInvMap x) = x ∧ sMap (sInvMap x) = x)

/-- Short steps of the thirtieth-power chain, on the full ambient set. -/
def powerTestA (i : Nat) : Bool :=
  let x := Fin.ofNat 306936 i
  decide (a1Map x = wInvMap (rMap (vInvMap x)) ∧
    a2Map x = a1Map (a1Map x) ∧ a3Map x = a2Map (a1Map x) ∧
    a5Map x = a3Map (a2Map x) ∧ a10Map x = a5Map (a5Map x) ∧
    a15Map x = a10Map (a5Map x) ∧ FirstFourModel.imageA x = a15Map (a15Map x))

/-- Short steps of the sixth-power chain and the exact final conjugation. -/
def powerTestB (i : Nat) : Bool :=
  let x := Fin.ofNat 306936 i
  decide (b1Map x = uInvMap (vMap (vMap x)) ∧
    b2Map x = b1Map (b1Map x) ∧ b3Map x = b2Map (b1Map x) ∧
    b6Map x = b3Map (b3Map x) ∧ FirstFourModel.imageB x =
      uMap (sMap (wMap (b6Map (wInvMap (sInvMap (uInvMap x)))))))

theorem inverseChecks_of_test (h : ∀ i : Fin 306936, inverseTest i.val = true) :
    InverseChecks := by
  have hp (i : Fin 306936) := h i
  simp only [inverseTest, Fin.ofNat_eq_cast, Fin.cast_val_eq_self, decide_eq_true_eq] at hp
  exact ⟨fun i => (hp i).1, fun i => (hp i).2.1, fun i => (hp i).2.2.1,
    fun i => (hp i).2.2.2⟩

theorem powerChecksA_of_test (h : ∀ i : Fin 306936, powerTestA i.val = true) :
    PowerChecksA := by
  have hp (i : Fin 306936) := h i
  simp only [powerTestA, Fin.ofNat_eq_cast, Fin.cast_val_eq_self, decide_eq_true_eq] at hp
  exact ⟨fun i => (hp i).1, fun i => (hp i).2.1, fun i => (hp i).2.2.1,
    fun i => (hp i).2.2.2.1, fun i => (hp i).2.2.2.2.1,
    fun i => (hp i).2.2.2.2.2.1, fun i => (hp i).2.2.2.2.2.2⟩

theorem powerChecksB_of_test (h : ∀ i : Fin 306936, powerTestB i.val = true) :
    PowerChecksB := by
  have hp (i : Fin 306936) := h i
  simp only [powerTestB, Fin.ofNat_eq_cast, Fin.cast_val_eq_self, decide_eq_true_eq] at hp
  exact ⟨fun i => (hp i).1, fun i => (hp i).2.1, fun i => (hp i).2.2.1,
    fun i => (hp i).2.2.2.1, fun i => (hp i).2.2.2.2⟩

end Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables
