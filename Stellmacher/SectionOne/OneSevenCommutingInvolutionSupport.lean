module

public import Stellmacher.SectionOne.OneSevenFixedSupportLineControl
public import Stellmacher.SectionOne.OneSevenSylowOffender
public import Theory.GroupAction.NormalizingActor

/-!
# Actors commuting with a factor involution move its support within one line

In the exact Section One action, an involution in a canonical factor has
an order-two displacement subgroup. An ambient actor commuting with that
involution moves every point of the factor's four-element support only
inside this displacement line.

The existing factor theorem supplies the displacement order. The commuting
actor normalizes the involution's cyclic subgroup, hence preserves its
commutator subgroup. A two-element invariant subgroup is fixed pointwise.
The established canonical fixed-line support theorem gives the full support
bound. The actual action, factor, involution and commuting actor are retained.

This is the action calculation used for the predecessor support bound in
Stellmacher (9.10), printed p.57, after the selected-support assertion. It is
a reusable consequence of the canonical (1.7) factor theory, independent of
the graph construction and the later coatom argument.
-/

namespace Stellmacher.SectionOne

universe u

public theorem oneSevenFactor_commuting_involution_support_control
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hyp : Hypotheses G V) (D : Subgroup G) (hD : IsOneSevenFactor (V := V) D)
    (actor : G) (hactor : actor ∈ D) (hinvolution : IsInvolution actor)
    (mover : G) (hcommute : Commute mover actor) :
    Nat.card (commutatorAction (Subgroup.zpowers actor) V) = 2 ∧
      ∀ point ∈ commutatorAction D V,
        point⁻¹ * (mover • point) ∈ commutatorAction (Subgroup.zpowers actor) V := by
  let C := Subgroup.zpowers actor
  let R := commutatorAction C V
  have hCD : C ≤ D := Subgroup.zpowers_le.mpr hactor
  have hCcard : Nat.card C = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hinvolution.2 hinvolution.1]
  have hRcard : Nat.card R = 2 :=
    oneSevenFactor_involution_commutator_card_two hyp.action_faithful D C hD hCD hCcard
  have hRsupport : R ≤ commutatorAction D V := by
    change commutatorAction C V ≤ commutatorAction D V
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro value ⟨a, point, rfl⟩
    exact ⟨⟨a, hCD a.property⟩, point, rfl⟩
  have hmoverCentral : mover ∈ Subgroup.centralizer (C : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨power, rfl⟩ := ha
    exact (hcommute.zpow_right power).eq.symm
  have hnormalize : Subgroup.zpowers mover ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.zpowers_le.mpr hmoverCentral).trans (Subgroup.centralizer_le_normalizer _)
  have hinvariant : IsInvariant (Subgroup.zpowers mover) V R :=
    commutatorAction_isInvariant_of_normalizing_actor (Subgroup.zpowers mover) C hnormalize
  have hfixed : ∀ point ∈ R, mover • point = point := by
    obtain ⟨line, _, hline⟩ := (Nat.card_eq_two_iff' (1 : R)).mp hRcard
    intro point hpoint
    by_cases hone : point = 1
    · subst point
      exact smul_one mover
    have hmove : mover • point ∈ R :=
      (hinvariant.invariant ⟨mover, Subgroup.mem_zpowers mover⟩ point).mp hpoint
    have hpointEq : (⟨point, hpoint⟩ : R) = line :=
      hline ⟨point, hpoint⟩ (fun heq => hone (congrArg Subtype.val heq))
    have hmoveEq : (⟨mover • point, hmove⟩ : R) = line :=
      hline ⟨mover • point, hmove⟩ (fun heq => hone
        ((MulAction.injective mover) ((congrArg Subtype.val heq).trans (smul_one mover).symm)))
    exact congrArg Subtype.val (hmoveEq.trans hpointEq.symm)
  exact ⟨hRcard, oneSevenFactor_fixed_line_control hyp D hD R hRsupport hRcard mover hfixed⟩

end Stellmacher.SectionOne
