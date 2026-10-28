module
public import Stellmacher.SectionEight.LocalQuotientSylowActionSetup
public import Stellmacher.SectionEight.LemmaEightOneResidualJoin
public import Stellmacher.UniqueMaximalContainingTransport
public import Stellmacher.UniqueMaximalContainingMap
public import Stellmacher.SectionOne.OneSevenIdentification
public import Stellmacher.SectionOne.SL2ProductElementaryThreeSupplement
public import Theory.GroupTheory.ElementaryOddSylowUniqueMaximal


/-!
# Maximality of the Sylow image in the initial faithful quotient

For a local Section Eight context and its supplied faithful quotient
witness on the initial center, the projected edge Sylow subgroup is maximal.
No center, critical-length, or additional irreducibility hypothesis is needed.

The canonical product from (1.7) joins the projected Sylow to the whole quotient:
this follows from the residual join in (8.1) and residual--Sylow generation in
the initial stabilizer. Its derived subgroup is a normal elementary abelian
three-group supplement. The initial stabilizer's unique-maximal property
passes through the witness's surjection; the image Sylow is proper because
the faithful quotient has even order and trivial two-core. The elementary-odd
supplement theorem then identifies the image Sylow with that unique maximal
subgroup.

This supplies the maximality used for simultaneous opposite Sylow generation
in Stellmacher (8.4)(1),(2),(8); see `refs/latex/stellmacher-n-group.tex`.
All quotient and action constructions use the original witness instances.
The existing canonical theorem keeps its public statement and applies this
local result through `ctx.toLocalContext`. Generated-group contexts can use
the same proof without introducing an ambient Sylow-two parameter.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_four_faithful_sylow_isCoatom_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    IsCoatom ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) := by
  classical
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  have hlocal := (local_quotient_sylow_action_setup h Γ cp w).1
  have hP := (SevenSix.edge_local_data h Γ cp).1
  obtain ⟨hSP, U, hU⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hUS : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  let Ub := U.mapSurjective w.surjective
  let Sb := (S.subgroupOf P).map w.projection
  let E := SectionOne.oneSevenGenerated (G := w.X) (V := Za)
  have hUb : (Ub : Subgroup w.X) = Sb := by
    change (U : Subgroup P).map w.projection = _
    rw [hUS]
  have hEgen : E ⊔ (Ub : Subgroup w.X) = ⊤ := by
    have hres := lemma_eight_one_residual_join_local ctx w
    change SectionOne.oneE (V := Za) Sb =
      ((EAt Γ cp.a).subgroupOf P).map w.projection ⊔
        SectionOne.oneJ (V := Za) Sb at hres
    have hident := (SectionOne.oneSeven_global_identification hlocal Ub).2
    rw [hUb] at hident
    rw [hident] at hres
    have hEres : ((EAt Γ cp.a).subgroupOf P).map w.projection ≤ E :=
      le_sup_left.trans hres.ge
    have hRS : (EAt Γ cp.a).subgroupOf P ⊔ S.subgroupOf P = ⊤ := by
      apply Subgroup.map_injective P.subtype_injective
      have hEaP : EAt Γ cp.a ≤ P := by
        rw [show EAt Γ cp.a = twoResidualAmbient P from Γ.twoResidualAt_def cp.a]
        exact Subgroup.map_subtype_le _
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hEaP,
        Subgroup.map_subgroupOf_eq_of_le hSP, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
      rw [show EAt Γ cp.a = twoResidualAmbient P from Γ.twoResidualAt_def cp.a]
      exact SectionThree.twoResidual_sup_sylowImage ⟨U, hU⟩
    have hRSmap := congrArg (Subgroup.map w.projection) hRS
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ w.surjective] at hRSmap
    apply top_unique
    rw [← hRSmap, hUb]
    exact sup_le_sup hEres le_rfl
  have hUne : (Ub : Subgroup w.X) ≠ ⊤ := by
    intro htop
    have hp : IsPGroup 2 w.X := by
      have hp := Ub.isPGroup'
      rw [htop] at hp
      exact hp.of_surjective (⊤ : Subgroup w.X).subtype (fun x => ⟨⟨x, trivial⟩, rfl⟩)
    have hcore : pCore 2 w.X = ⊤ := by
      apply top_unique
      exact le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩
    have hbad : (⊤ : Subgroup w.X) = ⊥ := hcore.symm.trans hlocal.twoCore_eq_bot
    have hcard : Nat.card w.X = 1 := by
      simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using Subgroup.card_eq_one.mpr hbad
    have heven := hlocal.G_even
    rw [hcard] at heven
    norm_num at heven
  have hPset := (pFamily_iff_pSet _ _ _).mp hP.1
  have huniqP : IsUniqueMaximalContaining (U : Subgroup P) (⊤ : Subgroup P) :=
    native_uniqueMaximalContaining P (U : Subgroup P) (by rw [hU]; exact hPset.2)
  have huniqUb := uniqueMaximalContaining_map_of_ne_top
    w.projection w.surjective (U : Subgroup P) huniqP hUne
  have huniq : ∃! M : Subgroup w.X, IsCoatom M ∧ (Ub : Subgroup w.X) ≤ M := by
    obtain ⟨M, hM, hUM, huniq⟩ := (uniqueMaximalContaining_top_iff _).mp huniqUb
    exact ⟨M, ⟨hM, hUM⟩, fun N hN => huniq N hN.1 hN.2⟩
  obtain ⟨hEn, hprod, _⟩ := SectionOne.oneSeven_global_product hlocal Ub
  obtain ⟨R, hRn, hRe, hRgen⟩ := SectionOne.sl2_product_elementary_three_supplement Ub E hEn
    (SectionOne.oneSevenFactors (G := w.X) (V := Za)) hprod
    (fun D hD => ((SectionOne.mem_oneSevenFactors_iff D).mp hD).1) hEgen
  let _ := hRn
  let _ := hRe
  change IsCoatom Sb
  rw [← hUb]
  exact Theory.GroupTheory.sylow_isCoatom_of_elementary_odd_supplement_unique_maximal
    R Ub hRgen huniq

public theorem eight_four_faithful_sylow_isCoatom
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    IsCoatom ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) := by
  exact eight_four_faithful_sylow_isCoatom_local ctx.toLocalContext w

end Stellmacher.SectionEight
