module
public import Theory.SpecificGroups.SymmetricFourWreath.Core.OutsideInvolutions
public import Stellmacher.ElementaryAbelianMaxFamilyMap

/-!
# Intrinsic geometry of the Sylow central quotient

The coordinate fixed-point counts imply that Q/Z is self-centralizing and
that the centralizer of any hyperplane of Q/Z centralizes all of Q/Z. An
involution outside Q/Z cannot lie in an elementary subgroup of order sixteen,
since its centralizer has that order and is nonabelian. Thus Q/Z is the unique
maximum elementary subgroup and is the elementary Thompson subgroup.

Source: Aschbacher–Smith 13.9.6 and the no-transvection step of 13.9.8,
printed pp.971–972 (PDF pp.988–989).
-/

public section
namespace SymmetricFourWreath
open Subgroup

private theorem line_le_core : centralLine ≤ coreInP := zpowers_le.mpr centralInP_mem_coreInP

private theorem projection_ker : centralProjection.ker = centralLine  := QuotientGroup.ker_mk' centralLine

theorem quotientCore_comap : quotientCore.comap centralProjection = coreInP := by
  rw [quotientCore,comap_map_eq,projection_ker,sup_eq_left.mpr line_le_core]

private theorem card_preimage (E : Subgroup CentralQuotient) :
    Nat.card (E.comap centralProjection) = 2*Nat.card E := by
  let f : E.comap centralProjection →* E := centralProjection.restrict (fun _ hx=>hx)
  have hf : Function.Surjective f := by
    intro e
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective centralLine e
    exact ⟨⟨x,by change centralProjection x∈E; rw [show centralProjection x=e from hx];exact e.property⟩,
      Subtype.ext hx⟩
  have hle : centralLine ≤ E.comap centralProjection := by
    intro x hx
    change centralProjection x∈E
    rw [show centralProjection x=1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact E.one_mem
  have hk : f.ker = centralLine.subgroupOf (E.comap centralProjection) := by
    ext x
    change (⟨centralProjection x,x.property⟩ : E)=1 ↔ (x:P)∈centralLine
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  have hc : Nat.card f.ker=2 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,card_centralLine]
  have hi : f.ker.index=Nat.card E := by
    rw [index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  rw [←f.ker.card_mul_index,hc,hi]

theorem centralizer_large_subgroup_le_quotientCore (E : Subgroup CentralQuotient)
    (hE : E≤quotientCore) (hcard : 4<Nat.card E) : centralizer (E:Set CentralQuotient)≤quotientCore := by
  intro x hx
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective centralLine x
  by_cases ha : a∈coreInP
  · exact mem_map_of_mem centralProjection ha
  · have hle : E.comap centralProjection ≤ coreInP⊓centralFiber a := by
      intro y hy
      refine ⟨?_,?_⟩
      · rw [←quotientCore_comap]
        exact hE hy
      · change centralProjection y∈centralizer ({centralProjection a}:Set CentralQuotient)
        exact mem_centralizer_singleton_iff.mpr (hx _ hy)
    have hc := card_le_of_le hle
    rw [card_core_fixed a ha,card_preimage E] at hc
    omega

private theorem quotientCore_le_centralizer : quotientCore ≤ centralizer (quotientCore:Set CentralQuotient) := by
  intro x hx y hy
  exact congrArg Subtype.val (quotientCore_elementary.is_comm.comm (⟨y,hy⟩:quotientCore) ⟨x,hx⟩)

theorem centralizer_quotientCore : centralizer (quotientCore:Set CentralQuotient)=quotientCore :=
  le_antisymm (centralizer_large_subgroup_le_quotientCore quotientCore le_rfl (by rw [card_quotientCore];decide))
    quotientCore_le_centralizer

theorem hyperplane_fixers (E : Subgroup CentralQuotient) (hE : E≤quotientCore)
    (hcard : Nat.card E=8) : centralizer (E:Set CentralQuotient)≤centralizer (quotientCore:Set CentralQuotient) :=
  (centralizer_large_subgroup_le_quotientCore E hE (by omega)).trans quotientCore_le_centralizer

private theorem elementary_large_le (E : Subgroup CentralQuotient)
    (hE : IsElementaryAbelian 2 E) (hcard : 16≤Nat.card E) : E≤quotientCore := by
  intro x hx
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective centralLine x
  by_cases ha : a∈coreInP
  · exact mem_map_of_mem centralProjection ha
  · have hs : centralProjection a*centralProjection a=1 := by
      simpa only [pow_two] using (elemPow_eq_one_of_isElementaryAbelian (p:=2) (centralProjection a) hx)
    have hle : E.comap centralProjection ≤ centralFiber a := by
      intro y hy
      change centralProjection y∈centralizer ({centralProjection a}:Set CentralQuotient)
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hE.is_comm.comm (⟨centralProjection y,hy⟩:E) ⟨centralProjection a,hx⟩))
    have heq : E.comap centralProjection=centralFiber a := eq_of_le_of_card_ge hle (by
      rw [card_preimage,card_centralFiber_of_involution a ha hs]
      omega)
    obtain ⟨b,hb,c,hc,hbc⟩ := centralFiber_noncommuting a ha hs
    have hbE : centralProjection b∈E := by change b∈E.comap centralProjection;rw [heq];exact hb
    have hcE : centralProjection c∈E := by change c∈E.comap centralProjection;rw [heq];exact hc
    exact (hbc (congrArg Subtype.val (hE.is_comm.comm (⟨centralProjection b,hbE⟩:E) ⟨centralProjection c,hcE⟩))).elim

theorem maximum_elementary_centralQuotient (E : Subgroup CentralQuotient) :
    E∈Stellmacher.elementaryAbelianMaxSubgroups (⊤:Subgroup CentralQuotient) ↔ E=quotientCore := by
  constructor
  · rintro ⟨_,hE,hmax⟩
    have hc : 16≤Nat.card E := by simpa only [card_quotientCore] using hmax quotientCore le_top inferInstance
    exact eq_of_le_of_card_ge (elementary_large_le E hE hc) (card_quotientCore ▸ hc)
  · rintro rfl
    refine ⟨le_top,inferInstance,fun E _ hE=>?_⟩
    by_cases hc : 16≤Nat.card E
    · exact card_le_of_le (elementary_large_le E hE hc)
    · rw [card_quotientCore];omega

theorem thompson_centralQuotient :
    Stellmacher.elementaryAbelianMaxJ (⊤:Subgroup CentralQuotient)=quotientCore := by
  apply le_antisymm
  · apply sSup_le
    intro E hE
    rw [(maximum_elementary_centralQuotient E).mp hE]
  · exact le_sSup ((maximum_elementary_centralQuotient _).mpr rfl)
end SymmetricFourWreath
