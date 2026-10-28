module
public import Theory.SpecificGroups.PSL3.BinaryOddCenterCover
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# Full special-linear recognition through a central cover

A finite quasisimple central cover of SL₃(F) with trivial two-core is an
isomorphism. Away from field orders two and four, the scalar-cover lift
bounds its order by that of SL₃(F). The exceptional order-four lift has
the same consequence because the covering center is odd. At order two,
the odd-center theorem kills the entire center. The resulting equivalence
is the supplied covering map, so it preserves every original marking.

Source: Aschbacher--Smith I.1.3, printed p.407, and the full core-quotient
recognition in C.2.7(g), printed pp.145--147; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace Matrix.SL3

/-- Trivial two-core removes every extra kernel over the full SL₃ model,
including the exceptional fields of orders two and four. -/
theorem centralCover_injective {F E : Type*} [Field F] [Finite F] [Group E] [Finite E] [IsQuasisimple E]
    (f : Cover E SL(3,F)) (hc : pCore 2 E = ⊥) : Function.Injective f.toMonoidHom := by
  let e : E ⧸ center E ≃* PSL(3,F) := f.quotientCenterEquiv
  have ho : Odd (Nat.card (center E)) := by
    exact Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using
        not_dvd_card_central_of_pCore_eq_bot hc (center E) le_rfl)
  by_cases h2 : Nat.card F = 2
  · apply f.toMonoidHom.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    exact f.ker_le_center.trans_eq (Matrix.PSL3.BinaryOddCenterCover.center_eq_bot_two h2 e ho)
  have hs : ∃ k : SL(3,F) →* E, Function.Surjective k := by
    by_cases h4 : Nat.card F = 4
    · obtain ⟨k,hk,_⟩ := Matrix.PSL3.BinaryOddCenterCover.exists_scalar_lift_four h4 e ho
      exact ⟨k,hk⟩
    · obtain ⟨k,hk,_⟩ := Matrix.PSL3.OrdinaryCenterRecognition.exists_scalar_lift h2 h4 e
      exact ⟨k,hk⟩
  obtain ⟨k,hk⟩ := hs
  exact (f.surjective.bijective_of_nat_card_le (Nat.card_le_card_of_surjective k hk)).1

/-- The original covering map, now known to be an isomorphism. -/
noncomputable def centralCoverEquiv
    {F E : Type*} [Field F] [Finite F] [Group E] [Finite E] [IsQuasisimple E]
    (f : Cover E SL(3,F)) (hc : pCore 2 E = ⊥) : E ≃* SL(3,F) :=
  MulEquiv.ofBijective f.toMonoidHom ⟨centralCover_injective f hc, f.surjective⟩

/-- Recognition retains the literal projection. -/
theorem centralCoverEquiv_apply
    {F E : Type*} [Field F] [Finite F] [Group E] [Finite E] [IsQuasisimple E]
    (f : Cover E SL(3,F)) (hc : pCore 2 E = ⊥) (x : E) :
    centralCoverEquiv f hc x = f.toMonoidHom x := by
  unfold centralCoverEquiv
  rfl

end Matrix.SL3
