module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.JRestrictions.FixedPairQuartic.ModelRestriction
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions

/-!
# Central-layer recognition for the literal fixed-pair core

The transported pair core satisfies the intrinsic elementary-restriction
lemmas. Its sign layer is exactly Frattini, its central-four layer is cyclic,
and the two quotients are elementary of the required orders. These statements
apply to `coreImage`, which is the image of the literal pair core under the
marked hexad coordinates; the pair core is never replaced by the hexad radical.

The full isomorphism still requires the intrinsic center calculation and
cyclic-four recognition. The earlier hexad `Recognition` remains an explicit
source input, produced by the quartic-hexad development and discharged by the
local-cover assembly. Source: Aschbacher–Smith I.2.2(6a), printed pp.410 and 412.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open EvenCliffordSix.SplitExtension.ElementaryRestrictions
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
variable {K : Type*} [Group K] [Finite K] [IsCyclic (center K)]
variable (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
variable (rec : Recognition e m22Hexad234_mem)

/-- The original pair core has the literal sign layer as Frattini in model coordinates. -/
theorem coreImage_frattini :
    frattini (coreImage e hZ rec) = signIn (coreImage e hZ rec) :=
  frattini_eq_signIn _ (coreImage_contains_central e hZ rec)
    (coreImage_card e hZ rec) (coreImage_square e hZ rec)

/-- The distinguished C₄ inside the pair core, with an actual equivalence. -/
noncomputable def coreImage_centralFourEquiv :
    centralIn (coreImage e hZ rec) ≃* Multiplicative (ZMod 4) :=
  centralInFourEquiv _ (coreImage_contains_central e hZ rec)

theorem coreImage_signQuotient :
    IsElementaryAbelian 2 (coreImage e hZ rec ⧸ signIn (coreImage e hZ rec)) ∧
      Nat.card (coreImage e hZ rec ⧸ signIn (coreImage e hZ rec)) = 32 :=
  ⟨signQuotient_elementary _ (coreImage_square e hZ rec),
    signQuotient_card _ (coreImage_contains_central e hZ rec) (coreImage_card e hZ rec)⟩

theorem coreImage_centralQuotient :
    IsElementaryAbelian 2 (coreImage e hZ rec ⧸ centralIn (coreImage e hZ rec)) ∧
      Nat.card (coreImage e hZ rec ⧸ centralIn (coreImage e hZ rec)) = 16 :=
  ⟨centralQuotient_elementary _ (coreImage_square e hZ rec),
    centralQuotient_card _ (coreImage_contains_central e hZ rec) (coreImage_card e hZ rec)⟩

theorem coreImage_actorImage_elementary :
    IsElementaryAbelian 2 (actorImage (coreImage e hZ rec)) :=
  actorImage_elementary _ (coreImage_square e hZ rec)

/-- Every actual projected actor fixes the radical-intersection vector coordinates. -/
theorem coreImage_actor_fixes_radicalVectors
    (a : EvenCliffordSix.A) (ha : a ∈ actorImage (coreImage e hZ rec))
    (v : Multiplicative EvenCliffordSix.V)
    (hv : v ∈ radicalVectors (coreImage e hZ rec)) :
    EvenCliffordSix.permuteVector a.val v.toAdd = v.toAdd :=
  actorImage_fixes_radicalVectors _ (coreImage_square e hZ rec) a ha v hv

omit [IsCyclic (center K)] in
/-- The actual actor and fixed-vector groups satisfy the required order balance. -/
theorem coreImage_radical_count :
    2 * Nat.card (radicalVectors (coreImage e hZ rec)) *
      Nat.card (actorImage (coreImage e hZ rec)) = 64 := by
  rw [radicalVectors_card _ (coreImage_contains_central e hZ rec),
    radicalPart_card_mul_actorImage_card, coreImage_card e hZ rec]

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
