module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.Actor
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.NaturalSection
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
/-!
# The generalized Fitting subgroup of the terminal G₂ actor

The preimage of G₂(2)′ inside the actual offender actor is simple and
perfect, and its quotient embeds in the quotient of G₂(2) by G₂(2)′.
Since the offender actor has trivial two-core, this preimage is F*(N)
and lies in every nontrivial normal subgroup of N. The two-perfect first
local factor is contained in the same preimage.

Source: Aschbacher–Smith, final proof of 15.3.1, printed p.1155, and the
Fitting subgroup used in B.5.1 and B.5.6, printed pp.99 and 105.
The intrinsic G₂ results are reused from the attributed ATLAS port.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition
open OrdinaryExclusions.G2
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.Classification
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

noncomputable def component (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2)) : Subgroup d.offenderGroup :=
  (commutator (Atlas.G2.Model (ZMod 2))).comap
    (e.toMonoidHom.comp d.offenderGroup.subtype)

theorem component_map (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2)) :
    (component d e).map (e.toMonoidHom.comp d.offenderGroup.subtype) =
      commutator (Atlas.G2.Model (ZMod 2)) := by
  apply map_comap_eq_self
  simpa only [MonoidHom.range_comp, range_subtype] using derived_le_offenderImage d e

noncomputable def componentEquiv (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2)) :
    component d e ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
  ((component d e).equivMapOfInjective (e.toMonoidHom.comp d.offenderGroup.subtype)
    (e.injective.comp Subtype.val_injective)).trans (MulEquiv.subgroupCongr (component_map d e))

theorem component_structure (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2)) :
    generalizedFitting d.offenderGroup = component d e ∧
      ∀ N : Subgroup d.offenderGroup, N.Normal → N ≠ ⊥ → component d e ≤ N := by
  let L := commutator (Atlas.G2.Model (ZMod 2))
  let : IsSimpleGroup L := Atlas.G2.isSimple_commutator_binary
  let : Group.IsPerfect L := by
    let : Group.IsPerfect Atlas.G2.BinaryException.H := Atlas.G2.BinaryException.H_isPerfect
    let f := MulEquiv.subgroupCongr
      Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure.symm
    exact Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
  let : IsSimpleGroup (component d e) := (componentEquiv d e).isSimpleGroup
  let : Group.IsPerfect (component d e) :=
    Group.IsPerfect.ofSurjective (f := (componentEquiv d e).symm.toMonoidHom)
      (componentEquiv d e).symm.surjective
  let : (component d e).Normal := inferInstanceAs (L.comap _).Normal
  have hp : IsPGroup 2 (Atlas.G2.Model (ZMod 2) ⧸ L) := by
    apply IsPGroup.of_card (n := 1)
    rw [← index_eq_card]
    change (commutator (Atlas.G2.Model (ZMod 2))).index = 2 ^ 1
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
      Atlas.G2.BinaryException.index_H]
    rfl
  let q := (QuotientGroup.mk' L).comp (e.toMonoidHom.comp d.offenderGroup.subtype)
  have hker : q.ker = component d e := by
    ext x
    exact QuotientGroup.eq_one_iff _
  have hquot : IsPGroup 2 (d.offenderGroup ⧸ component d e) := by
    exact ((hp.to_subgroup q.range).of_equiv
      (QuotientGroup.quotientKerEquivRange q).symm).of_equiv
        (QuotientGroup.quotientMulEquivOfEq hker)
  have h := simple_two_quotient_structure (component d e)
    (Group.IsPerfect.not_isMulCommutative _) hquot d.offenderGroup_twoCore
  exact ⟨h.1, h.2.2⟩

/-- The actual component, with the first local factor restricted through its
original inclusion in the offender actor. -/
theorem first_le_fitting (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2)) :
    firstInOffender d ≤ generalizedFitting d.offenderGroup := by
  rw [(component_structure d e).1]
  intro x hx
  exact firstImage_le_derived d e (mem_map_of_mem e.toMonoidHom hx)

/-- The component's order is independent of which of the two offender actors
occurs; in both cases it is the actual derived group of order 6048. -/
theorem fitting_card (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2)) :
    Nat.card (generalizedFitting d.offenderGroup) = 6048 := by
  rw [(component_structure d e).1, Nat.card_congr (componentEquiv d e).toEquiv,
    Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
  exact Atlas.G2.BinaryException.card_H

/-- The bound is for the offender actor, without identifying it with the
whole quotient. -/
theorem actor_card_le (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2)) :
    Nat.card d.offenderGroup ≤ 12096 := by
  have h := d.offenderGroup.card_le_card_group
  rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model] at h
  norm_num at h ⊢
  exact h

/-- Every nontrivial normal subgroup of the actor contains its actual F*. -/
theorem fitting_le_normal (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2))
    (N : Subgroup d.offenderGroup) (hN : N.Normal) (hne : N ≠ ⊥) :
    generalizedFitting d.offenderGroup ≤ N := by
  rw [(component_structure d e).1]
  exact (component_structure d e).2 N hN hne

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.Classification
