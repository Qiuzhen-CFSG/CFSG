module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Coset.Card

/-!
# A cubic element in the literal binary Co₁ carrier

The second published generator has cube one by its existing matrix certificate.
Its off-diagonal entry at `(0,1)` is one, so the generator has order three.
Lagrange's theorem supplies the factor three in the carrier cardinality.

Source: ATLAS `Co1G1-f2r24B0`, retained in the imported carrier; application to
Aschbacher–Smith 1.1.5(3) and the known-simple prime-to-15 argument.
-/

public section
namespace Sporadic.LeechRelated.Co1

/-- Three divides the order of the actual published Co₁ matrix carrier. -/
theorem three_dvd_card : 3 ∣ Nat.card Carrier := by
  let b : Carrier := ⟨generatorB, Subgroup.subset_closure (by simp)⟩
  have hc : b ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    change matrixB ^ 3 = 1
    simpa only [pow_succ, pow_zero, one_mul] using matrixB_cube
  have hn : b ≠ 1 := by
    intro h
    have he := congrArg (fun g : Carrier => g.val.val 0 1) h
    change (1 : ZMod 2) = 0 at he
    exact one_ne_zero he
  have ho : orderOf b = 3 := orderOf_eq_prime hc hn
  simpa only [ho] using orderOf_dvd_natCard b

end Sporadic.LeechRelated.Co1
