module

public import Theory.SpecificGroups.PSL2.OddCoverKernel
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# A two-core-free odd PSL₂ cover away from order nine

The perfect central kernel has order dividing two. With trivial two-core
it is therefore trivial. The exceptional field of order nine is retained
explicitly until the actual quintic Sylow geometry excludes it.

Source: Aschbacher--Smith I.1.3--4 and 6.1.4, printed pp.407--408 and666.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace Theory.PSL2

/-- The center of a two-core-free perfect central PSL₂ cover is trivial
for odd fields other than the separately retained order-nine field. -/
theorem odd_twoCore_free_center_eq_bot
    {Q : Type*} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (hcore : pCore 2 Q = ⊥)
    {F : Type*} [Field F] [Finite F] [Fact (3 < Nat.card F)]
    (hodd : Odd (Nat.card F)) (h9 : Nat.card F ≠ 9)
    (e : (Q ⧸ center Q) ≃* PSL(2,F)) : center Q = ⊥ := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hk : f.ker = center Q := by
    ext x
    change e (QuotientGroup.mk' (center Q) x) = 1 ↔ x ∈ center Q
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let c : Cover Q PSL(2,F) := {
    toMonoidHom := f
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := hk.le }
  have hc : Nat.card (center Q) ∣ 2 := by
    simpa only [show c.toMonoidHom.ker = center Q from hk] using
      odd_cover_kernel_card_dvd_two hodd h9 c
  have hp : IsPGroup 2 (center Q) := IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hc)
  exact bot_unique ((show center Q ≤ pCore 2 Q from le_sSup ⟨inferInstance,hp⟩).trans hcore.le)

end Theory.PSL2
