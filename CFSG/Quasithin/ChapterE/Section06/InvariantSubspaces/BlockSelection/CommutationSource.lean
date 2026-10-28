module
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.FixedNine
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.Contracts
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.Source
/-!
# Relative block commutation for E.6.14

Apply C.1.9 inside the actual characteristic-two overgroup H. Conjugation
by N_G(H) acts on H, so the conjugate remains a block subnormal in H.
Mapping the commutator back through H's inclusion supplies the exact
commutation contracts used by the fixed-nine and residual arguments.

Source: Aschbacher–Smith C.1.9, printed p.123, and E.6.14, printed p.251.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
open Subgroup Theory.GroupTheory CFSG.Quasithin
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
universe u
variable {G : Type u} [Group G] [Finite G]

/-- C.1.9 on a chi-zero block and a distinct conjugate in its relative ambient group. -/
theorem conjugateChiZeroCommutationInput : ConjugateChiZeroCommutationInput G := by
  intro H L hc hLH hL hs x hx hne
  let B := L.subgroupOf H
  let a := H.normalizerMonoidHom ⟨x,hx⟩
  have hb : ChapterC.IsBlock B :=
    ⟨inferInstance, hL.chi.short.of_mulEquiv (subgroupOfEquivOfLe hLH).symm, hs⟩
  have hm : (B.map a.toMonoidHom).map H.subtype = L.map (MulAut.conj x) := by
    rw [map_map]
    have he : H.subtype.comp a.toMonoidHom = (MulAut.conj x).toMonoidHom.comp H.subtype := by
      ext l
      rfl
    rw [he, ← map_map, map_subgroupOf_eq_of_le hLH]
    rfl
  have hn : B.map a.toMonoidHom ≠ B := by
    intro he
    apply hne
    have he := congrArg (Subgroup.map H.subtype) he
    rwa [hm, map_subgroupOf_eq_of_le hLH] at he
  have hg : ChapterC.BlockCommutationHypothesis H := by
    intro _
    exact twoThreeCore_generalizedFitting hc
  have hcomm := ChapterC.blocks_commute hg (hb.map_equiv a) hb hn
  have he := congrArg (Subgroup.map H.subtype) hcomm
  rw [map_commutator, hm, map_subgroupOf_eq_of_le hLH, Subgroup.map_bot] at he
  exact commutator_eq_bot_iff_le_centralizer.mp he

/-- The cubic-actor specialization constructs the fixed elementary nine of E.6.14. -/
theorem fixedNineInput : FixedNineInput G :=
  fixedNineInput_of_conjugate_commutation (fun H L hc hLH hL hs x hx _ hne =>
    conjugateChiZeroCommutationInput H L hc hLH hL hs x hx hne)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
