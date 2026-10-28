module
public import Theory.PGroupCore
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Prime-core quotient order under a prime-group kernel

A homomorphism with p-group kernel gives divisibility of the source
p-core quotient order by the target order. The argument passes through
the literal kernel and range; no core containment in the target is needed.
The consumer compares nested original components in source 14.7.50.
-/
public section
namespace MonoidHom
open Subgroup
variable {X Y : Type*} [Group X] [Group Y]
/-- The quotient by the source p-core has order dividing the target order. -/
theorem pCoreQuotient_card_dvd_of_isPGroup_ker (p : ℕ)
    (f : X →* Y) (hk : IsPGroup p f.ker) :
    Nat.card (X ⧸ pCore p X) ∣ Nat.card Y := by
  have hker : f.ker ≤ pCore p X := le_sSup ⟨inferInstance,hk⟩
  let r : (X ⧸ f.ker) →* (X ⧸ pCore p X) := QuotientGroup.lift f.ker
    (QuotientGroup.mk' (pCore p X)) (by simpa only [QuotientGroup.ker_mk'] using hker)
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore p X) x
    exact ⟨QuotientGroup.mk' f.ker x,rfl⟩
  have hd := card_dvd_of_surjective r hr
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hd
  exact hd.trans f.range.card_subgroup_dvd_card
end MonoidHom
