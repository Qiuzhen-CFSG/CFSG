module

public import Theory.SpecificGroups.G2.MultiplierTwoGroup
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.GroupTheory.CoveringPGroupDescent
public import Theory.SpecificGroups.SU3.TernaryPerfectCover

/-!
# Recovering an even G₂ group from its marked central quotient

The universal kernel is a two-group, including at the four-element field.
Its image in a quasisimple cover with trivial two-core vanishes. Thus the
literal central projection is an isomorphism; its prescribed quotient
marking is retained.

Source: Aschbacher–Smith I.1.1–I.1.4 and the G₂ case of A.3.6.
-/

public section

namespace Atlas.G2.FiniteCover
open Subgroup Theory.GroupTheory PerfectCentralCovering

variable {F L : Type*} [Field F] [Finite F] [Group L] [Finite L] [IsQuasisimple L]

/-- A marked central quotient lifts to the original group when its two-core
is trivial. No further covering or multiplier premise remains. -/
theorem exists_marked_equiv {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hcore : pCore 2 L = ⊥) (e : L ⧸ center L ≃* Model F) :
    ∃ j : L ≃* Model F, ∀ x, j x = e (QuotientGroup.mk x) := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup (Model F) := e.symm.isSimpleGroup
  let c := centralQuotientCover e
  let : IsQuasisimple (Model F) := IsQuasisimple.of_surjective c.toMonoidHom c.surjective
  let g := c.toCovering
  have hi : Function.Injective g.toMonoidHom :=
    (universalQuasisimpleCover_isUniversal (Model F)).injective_of_pGroup_kernel
      (universalKernel_isPGroup_of_card_pow hF (by omega)) g hcore
  exact ⟨MulEquiv.ofBijective g.toMonoidHom ⟨hi, g.surjective⟩, fun _ => rfl⟩

end Atlas.G2.FiniteCover

namespace Atlas.G2.FiniteCover
open Subgroup Theory.GroupTheory PerfectCentralCovering
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]

/-- The binary derived endpoint has the same marked-cover conclusion, using
its separate ternary unitary kernel calculation. -/
theorem exists_binaryDerived_marked_equiv (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* commutator (Model (ZMod 2))) :
    ∃ j : L ≃* commutator (Model (ZMod 2)),
      ∀ x, j x = e (QuotientGroup.mk x) := by
  let f := centralQuotientCover e
  have hk := BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.binaryDerived_kernel_isTwoGroup f
  have hi : Function.Injective f.toMonoidHom := by
    apply f.toMonoidHom.ker_eq_bot_iff.mp
    apply bot_unique
    rw [← hcore]
    exact le_sSup ⟨inferInstance, hk⟩
  exact ⟨MulEquiv.ofBijective f.toMonoidHom ⟨hi,f.surjective⟩, fun _ => rfl⟩

end Atlas.G2.FiniteCover
