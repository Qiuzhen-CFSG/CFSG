module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.Comparison
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow

/-!
# The Sylow marking on a projected inner actor

The two-central mark in L* is exactly the mark of the corresponding element
of L/Z(L). Membership in L* means innerness of the action, not membership of
the original actor in L. These equivalences provide the precise input for
the marked rows of 16.1.5 in the proof of 16.5.6(4), printed p.1197 of
Aschbacher–Smith's combined manuscript of 1 March 2004.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
variable {G : Type*} [Group G]

/-- Restricting to the component preserves the literal Sylow-center witness. -/
theorem twoCentralIn_coe_iff {L : Subgroup G} (v : L) :
    IsTwoCentralIn L (v : G) ↔ orderOf (v : G) = 2 ∧ TwoCentral v := by
  constructor
  · rintro ⟨hv2, S, ⟨P, rfl⟩, hvS, hSC⟩
    have hvP : v ∈ P := by
      obtain ⟨w, hw, he⟩ := hvS
      have he' : w = v := Subtype.ext he
      exact he' ▸ hw
    refine ⟨hv2, P, hvP, mem_center_iff.mpr ?_⟩
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp
      (hSC (mem_map_of_mem L.subtype x.property))
  · rintro ⟨hv2, P, hvP, hvC⟩
    refine ⟨hv2, (P : Subgroup L).map L.subtype, ⟨P, rfl⟩,
      mem_map_of_mem L.subtype hvP, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg (fun z : P => (z.val.val : G))
      (mem_center_iff.mp hvC ⟨y, hy⟩)

variable [Finite G] {L : Subgroup G}

/-- A marked element of the central quotient is a marked element of L*. -/
theorem twoCentral_componentImage_iff (x : L ⧸ center L) :
    IsTwoCentralIn (componentImage L)
      (componentImageEquiv L x : ActionQuotient L) ↔
      orderOf x = 2 ∧ TwoCentral x := by
  rw [twoCentralIn_coe_iff]
  have ho : orderOf (componentImageEquiv L x : ActionQuotient L) = orderOf x :=
    (orderOf_submonoid (componentImageEquiv L x)).trans
      ((componentImageEquiv L).orderOf_eq x)
  rw [ho]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, ?_⟩
    simpa only [MulEquiv.symm_apply_apply] using
      (TwoCentral.map (componentImageEquiv L).symm hc)
  · rintro ⟨hx, hc⟩
    exact ⟨hx, hc.map (componentImageEquiv L)⟩

/-- The projected actor is two-central precisely when its action is inner
and the representing central coset has the two-central Sylow marking. -/
theorem action_twoCentral_iff (u : normalizer (L : Set G)) :
    IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u) ↔
      orderOf (actionMap (L := L) le_rfl u) = 2 ∧
      ∃ k : L, L.normalizerMonoidHom u = MulAut.conj k ∧
        TwoCentral (QuotientGroup.mk' (center L) k) := by
  have represented (k : L) (hk : L.normalizerMonoidHom u = MulAut.conj k) :
      (componentImageEquiv L (QuotientGroup.mk' (center L) k) : ActionQuotient L) =
        actionMap (L := L) le_rfl u := by
    rw [componentImageEquiv_mk]
    apply actionHom_injective
    rw [actionHom_component, actionHom_actionMap, hk]
  constructor
  · intro hu
    obtain ⟨k, hk⟩ := (action_inner_iff u).mpr
      (twoCentral_iff_odd_index.mp hu).2.1
    refine ⟨hu.1, k, hk, ?_⟩
    rw [← represented k hk] at hu
    exact (twoCentral_componentImage_iff _).mp hu |>.2
  · rintro ⟨hu2, k, hk, hc⟩
    rw [← represented k hk] at hu2 ⊢
    apply (twoCentral_componentImage_iff _).mpr
    refine ⟨?_, hc⟩
    rwa [orderOf_submonoid (componentImageEquiv L (QuotientGroup.mk' (center L) k)),
      (componentImageEquiv L).orderOf_eq] at hu2

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows
