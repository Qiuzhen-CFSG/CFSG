module

public import Stellmacher.Recognition.LargeTerminalSmallFive
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# The first residual is normal in the full small terminal centralizer

If the omega-central involution has the first residual as its full
centralizer two-core, the literal mapped first residual group is normal
in that centralizer. The original order 2048 interface follows as a wrapper;
the general form also applies when excluding that core size at order 4096. The image of that residual
in the full centralizer quotient by its two-core is exactly the five-core
of the quotient, and this five-core has order five.

The first residual image in the vertex quotient has order five, so the
residual group itself has order 2560. The established full centralizer
core has order 512 and is contained in that residual, giving quotient image
order five. P-star subnormality persists under the quotient map, so the
image lies in the quotient's five-core. The actual Sylow five-subgroup of
the full centralizer has order five and intersects the two-core trivially;
its quotient image is a Sylow five-subgroup of order five. Equality with
the five-core follows, and normality pulls back because the residual
contains the quotient kernel.

All groups and maps are the original join inclusion and the canonical
full-centralizer quotient. No bound on the odd centralizer of this normal
five-subgroup is assumed; excluding its possible extra three-part remains
a separate step. Source: the P-star subnormality in Stellmacher (5.2), the
large residual structure in (10.1)(18)--(20), and the standard finite
subnormal p-subgroup theorem.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
universe u

/-- The mapped first-step two-residual has order 2560. -/
public theorem LargeTerminalContext.first_residual_group_card
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) :
    Nat.card ((EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
      (ctx.first ⊔ ctx.second).subtype) = 2560 := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset Γ cp 2 middle := ⟨⟨2, by omega⟩, rfl, rfl⟩
  let P := GAt Γ cp.firstStep
  let E := EAt Γ cp.firstStep
  let R := twoCoreIn E
  have hE : E = twoResidualIn P := Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  obtain ⟨e⟩ := ten_one_large_first_residual_five tenCtx middle hpath ctx.noTransvections
  have hquot : Nat.card ((E.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P))) = 5 :=
    (Nat.card_congr e.toEquiv).trans (by simp [C5])
  rw [← relIndex_ker, QuotientGroup.ker_mk'] at hquot
  have hmap := relIndex_map_map_of_injective (pCore 2 P) (E.subgroupOf P) P.subtype_injective
  rw [map_subgroupOf_eq_of_le hEP] at hmap
  have hindex : R.relIndex E = 5 := by
    change (twoCoreIn E).relIndex E = 5
    rw [hE, residual_core_eq_inter_core, inf_relIndex_left, ← hE]
    exact hmap.trans hquot
  have hRcard : Nat.card R = 512 :=
    (card_map_of_injective (K := R) K.subtype_injective).symm.trans ctx.first_residual_structure.1
  have hRE : R ≤ E := twoCoreIn_le E
  have hcard := (R.subgroupOf E).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hRE).toEquiv] at hcard
  change R.relIndex E * Nat.card R = Nat.card E at hcard
  rw [hindex, hRcard] at hcard
  exact (card_map_of_injective K.subtype_injective).trans hcard.symm

/-- The actual first residual is normal in the full centralizer, and its
quotient image is the normal cyclic five-core. -/
public theorem LargeTerminalContext.first_residual_normal_of_core_eq
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0)
    (hcore : ∃ z : G, orderOf z = 2 ∧ zpowers z = omegaOneCenter (S0 : Subgroup G) ∧
      twoCoreIn (centralizer ({z} : Set G)) = ctx.firstResidual) :
    ∃ z : G, orderOf z = 2 ∧ zpowers z = omegaOneCenter (S0 : Subgroup G) ∧
      let C := centralizer ({z} : Set G)
      let E := (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
        (ctx.first ⊔ ctx.second).subtype
      NormalIn E C ∧
        (E.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)) = pCore 5 (C ⧸ pCore 2 C) ∧
        Nat.card (pCore 5 (C ⧸ pCore 2 C)) = 5 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨z, hz, hgen, hcore, hJcard, _, _, P, hPcard, _⟩ :=
    ctx.exists_sylow_five_fixed_center_of_core_eq hcore
  let C := centralizer ({z} : Set G)
  let E := (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
    (ctx.first ⊔ ctx.second).subtype
  let EC := E.subgroupOf C
  let J := pCore 2 C
  let Q := C ⧸ J
  let q : C →* Q := QuotientGroup.mk' J
  let I := EC.map q
  have hC : C = centralizer (omegaOneCenter (S0 : Subgroup G) : Set G) := by
    change centralizer ({z} : Set G) = _
    rw [← centralizer_closure, ← zpowers_eq_closure, hgen]
  have hEsub : SubnormalIn E C := by
    rw [hC]
    exact (nine_two_ambient_setup
      (ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three).toAmbientSectionNineContext).2.2.2
  have hJE : J ≤ EC := by
    intro j hj
    have hm : (j : G) ∈ twoCoreIn C := mem_map_of_mem C.subtype hj
    rw [hcore] at hm
    obtain ⟨r, hr, hrj⟩ := hm
    exact mem_map.mpr ⟨r, twoCoreIn_le _ hr, hrj⟩
  have hECcard : Nat.card EC = 2560 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEsub.1).toEquiv).trans ctx.first_residual_group_card
  have hIcard : Nat.card I = 5 := by
    have hh := (J.subgroupOf EC).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hJE).toEquiv, hJcard, hECcard] at hh
    have hindex : J.relIndex EC = Nat.card I := by
      have h := relIndex_ker EC q
      rwa [QuotientGroup.ker_mk'] at h
    change J.relIndex EC * 512 = 2560 at hh
    rw [hindex] at hh
    omega
  have hIsub : I.IsSubnormal := hEsub.2.quotient
  have hIfive : IsPGroup 5 I := IsPGroup.of_card (n := 1) (by simpa using hIcard)
  have hIcore : I ≤ pCore 5 Q := by
    have h := isPGroup_le_pCoreAmbient_of_isSubnormalIn (⊤ : Subgroup Q) I 5 le_top
      (hIsub.comap (⊤ : Subgroup Q).subtype) hIfive
    have htop : (pCore 5 (⊤ : Subgroup Q)).map (⊤ : Subgroup Q).subtype = pCore 5 Q :=
      pCore_map_iso 5 Subgroup.topEquiv
    rwa [htop] at h
  let PB : Sylow 5 Q := P.mapSurjective (QuotientGroup.mk'_surjective J)
  have hPBcard : Nat.card PB = 5 := by
    have hdis : Disjoint J (P : Subgroup C) :=
      IsPGroup.disjoint_of_ne 2 5 (by decide) _ _ pCore_isPGroup P.isPGroup'
    have hbot : J.subgroupOf (P : Subgroup C) = ⊥ := subgroupOf_eq_bot.mpr hdis
    have h := relIndex_ker (P : Subgroup C) q
    rw [QuotientGroup.ker_mk'] at h
    change (J.subgroupOf (P : Subgroup C)).index = Nat.card PB at h
    rw [hbot, index_bot, hPcard] at h
    exact h.symm
  have hcorePB : pCore 5 Q ≤ PB := pCore_isPGroup.le_sylow_of_normal PB
  have hcorecard : Nat.card (pCore 5 Q) = 5 := by
    have hlo := card_le_of_le hIcore
    have hhi := card_le_of_le hcorePB
    rw [hIcard] at hlo
    rw [hPBcard] at hhi
    omega
  have hI : I = pCore 5 Q := eq_of_le_of_card_ge hIcore (by rw [hIcard, hcorecard])
  have hInormal : I.Normal := hI ▸ inferInstance
  have hECnormal : EC.Normal := by
    have h := hInormal.comap q
    have heq : I.comap q = EC := comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])
    rwa [heq] at h
  exact ⟨z, hz, hgen, ⟨hEsub.1, hECnormal⟩, hI, hcorecard⟩

/-- The order-2048 specialization retains the original public interface. -/
public theorem LargeTerminalContext.first_residual_normal_of_card
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) (hS : Nat.card S0 = 2048) :
    ∃ z : G, orderOf z = 2 ∧ zpowers z = omegaOneCenter (S0 : Subgroup G) ∧
      let C := centralizer ({z} : Set G)
      let E := (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
        (ctx.first ⊔ ctx.second).subtype
      NormalIn E C ∧
        (E.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)) = pCore 5 (C ⧸ pCore 2 C) ∧
        Nat.card (pCore 5 (C ⧸ pCore 2 C)) = 5 := by
  exact ctx.first_residual_normal_of_core_eq (ctx.involution_centralizer_core_eq_of_card hS)

end Stellmacher.Recognition
