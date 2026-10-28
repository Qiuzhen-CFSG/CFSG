module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorData
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Check

/-!
# Coverage for the packed inverse certificates

Four balanced checks cover the intervals [0,262144), [262144,294912),
[294912,303104), and [303104,307200). Their union contains the whole
306936-point carrier. Soundness gives the literal left-inverse identity;
`Fin.ofNat` makes the final padding well-defined without changing any input
inside the carrier. The two concrete consumers are `InverseChecks.A` and `.B`.

Source: the packed `GeneratorData` maps for the retained ATLAS
F24G1-p306936B0 tables and the balanced checker in `Comparison.Check`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.InverseChecks

def inversePointTest (f g : Fin 306936 → Fin 306936) (n : Nat) : Bool :=
  let x := Fin.ofNat 306936 n
  decide (g (f x) = x)

theorem leftInverse_of_checks (f g : Fin 306936 → Fin 306936)
    (h₀ : checkPow (inversePointTest f g) 0 18 = true)
    (h₁ : checkPow (inversePointTest f g) 262144 15 = true)
    (h₂ : checkPow (inversePointTest f g) 294912 13 = true)
    (h₃ : checkPow (inversePointTest f g) 303104 12 = true) :
    Function.LeftInverse g f := by
  intro x
  have h : inversePointTest f g x.val = true := by
    by_cases hx₀ : x.val < 262144
    · exact checkPow_sound _ 18 0 h₀ x.val (Nat.zero_le _) hx₀
    by_cases hx₁ : x.val < 294912
    · exact checkPow_sound _ 15 262144 h₁ x.val (Nat.le_of_not_gt hx₀) hx₁
    by_cases hx₂ : x.val < 303104
    · exact checkPow_sound _ 13 294912 h₂ x.val (Nat.le_of_not_gt hx₁) hx₂
    · exact checkPow_sound _ 12 303104 h₃ x.val (Nat.le_of_not_gt hx₂)
        (Nat.lt_trans x.isLt (by decide))
  have hx : Fin.ofNat 306936 x.val = x := by simp
  simpa only [inversePointTest, hx, decide_eq_true_eq] using h

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.InverseChecks
