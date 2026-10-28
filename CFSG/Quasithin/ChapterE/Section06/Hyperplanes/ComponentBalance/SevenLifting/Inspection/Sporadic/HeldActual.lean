module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.Held
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The actual Held obstruction to unrestricted seven inspection

The explicit Held outer involution has order two. Its checked fixed subgroup
contains a perfect normal subgroup of index two with center of order three
and actual central quotient A₇. Transport that subgroup through the fixed
subgroup inclusion and apply the established obstruction theorem. This
constructs a counterexample to the unrestricted SevenActionInspection
predicate from the actual permutation carrier, without any unproved table
premise. It does not refute the stronger ambient statement E.6.18.

Source: GLS3 Table 5.3p, printed p.277, and Aschbacher–Smith E.6.18, p.252.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
open Held.OuterInvolution Held.OuterInvolution.FixedStructure

theorem held_not_sevenActionInspection : ¬ SevenActionInspection Held.He := by
  let L := candidate.map action.fixedSubgroup.subtype
  let e : candidate ≃* L := candidate.equivMapOfInjective action.fixedSubgroup.subtype
    action.fixedSubgroup.subtype_injective
  have hLF : L ≤ action.fixedSubgroup := map_subtype_le _
  have hn : (L.subgroupOf action.fixedSubgroup).Normal := by
    have he : L.subgroupOf action.fixedSubgroup = candidate :=
      comap_map_eq_self (by rw [Subgroup.ker_subtype]; exact bot_le)
    rw [he]
    exact Subgroup.normal_of_index_eq_two candidate_index_exact
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hc : Nat.card (center candidate) = 3 := by
    rw [←orbitKernel_eq_center orbitImage_equiv_alternatingGroup
      (orbitKernel_le_centralZpowers.trans centralZpowers_le_center),
      orbitKernel_eq_centralZpowers_exact]
    exact centralZpowers_card
  let ez : center L ≃* Multiplicative (ZMod 3) :=
    (centerCongr e).symm.trans (mulEquivOfPrimeCardEq hc (by simp))
  have hz : (center candidate).map e.toMonoidHom = center L := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hx
      exact ⟨e.symm x,((centerCongr e).symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩
  let eq : (L ⧸ center L) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.congr (center candidate) (center L) e hz).symm.trans candidateQuotientCenterEquiv
  exact HeldInspection.not_inspection_of_fixed_normal_triple_cover action action_order L hLF hn ez eq

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
