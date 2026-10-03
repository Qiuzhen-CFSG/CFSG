module

public import Stellmacher.Recognition.LargeTerminalFourFixedLocalData
public import Theory.GroupTheory.ClassThreeResidualTwentyBound
public import Theory.GroupTheory.CharacteristicTwoFrattiniFive
public import Stellmacher.SectionFiveToSeven.ResidualTwoExtension

/-!
# The upper terminal involution-centralizer quotient

At Sylow order 4096 the distinguished involution centralizer has two-core
of order 1024. Its Frattini quotient has order at most 32, so the faithful
Frattini action shows that its Sylow five-subgroups have order five. The
subnormal first-step residual maps onto the quotient's normal five-core.
Adjoining the two-core and taking the two-residual shows that the first-step
residual, and its order-512 two-core, are normal in the full centralizer.

The action on the order-512 residual's Frattini quotient has two-group
kernel. Its class-three structure excludes order-fifteen automorphisms;
the normal-five bound therefore bounds the full quotient by twenty.
The known second local subgroup has order 20480, so a cardinal squeeze
identifies it with the full centralizer. No ambient Sylow-five or odd-local
solvability hypothesis is used.

Source: Stellmacher (10.1)(18)--(20) and Thompson VI, printed pp.629--630.
The cardinal squeeze is reused from the saved five-centralizer confinement
development. The intrinsic residual action uses Parrott's class-three
calculation, independently of a recognition theorem.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup

universe u

private theorem frattini_card_congr {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) :
    Nat.card (H ⧸ frattini H) = Nat.card (K ⧸ frattini K) := by
  have hmap : (frattini H).map e.toMonoidHom = frattini K := by
    apply le_antisymm
    · exact map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective e.surjective)
    · intro k hk
      refine mem_map.mpr ⟨e.symm k, ?_, e.apply_symm_apply k⟩
      exact frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective hk
  exact Nat.card_congr (QuotientGroup.congr _ _ e hmap).toEquiv

/-- Transport of the intrinsic bound to the actual full-centralizer core. -/
public theorem LargeTerminalContext.involution_centralizer_frattini_quotient_card_le
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    Nat.card (pCore 2 (centralizer ({z} : Set G)) ⧸
      frattini (pCore 2 (centralizer ({z} : Set G)))) ≤ 32 := by
  let C := centralizer ({z} : Set G)
  let J := pCore 2 C
  have hcore := (ctx.involution_centralizer_core_eq_at_generator hS z hgen).1
  let e : J ≃* twoCoreIn ctx.second :=
    (J.equivMapOfInjective C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr hcore)
  exact (frattini_card_congr e).le.trans (ctx.second_core_frattini_quotient_card_le hS)

/-- Every Sylow five-subgroup of the full involution centralizer has order
five. This is internal Sylow status, not ambient Sylow status in G. -/
public theorem LargeTerminalContext.involution_centralizer_sylow_five_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (P : Sylow 5 (centralizer ({z} : Set G))) : Nat.card P = 5 := by
  let C := centralizer ({z} : Set G)
  have hchar : centralizer (pCore 2 C : Set C) ≤ pCore 2 C :=
    (ctx.localStructure C (Theory.GroupTheory.isTwoLocal_involution_centralizer hz)).2
  have hPC : ctx.second ≤ C := ctx.second_le_residual_normalizer.trans
    (ctx.residual_normalizer_le_involution_centralizer z hz hgen)
  have hdiv : 5 ∣ Nat.card C :=
    (by norm_num : 5 ∣ 20480).trans
      (ctx.second_card_of_large_card hS ▸ card_dvd_of_le hPC)
  exact five_sylow_card_of_characteristic_two_frattini_card_le hchar
    (ctx.involution_centralizer_frattini_quotient_card_le hS z hgen) hdiv P

/-- The subnormal first-step residual maps onto the order-five core of the
full involution-centralizer quotient. -/
public theorem LargeTerminalContext.involution_centralizer_quotient_five_core
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    let C := centralizer ({z} : Set G)
    let E := (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
      (ctx.first ⊔ ctx.second).subtype
    (E.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)) =
      pCore 5 (C ⧸ pCore 2 C) ∧
      Nat.card (pCore 5 (C ⧸ pCore 2 C)) = 5 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let C := centralizer ({z} : Set G)
  let E := (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
    (ctx.first ⊔ ctx.second).subtype
  let EC := E.subgroupOf C
  let R := ctx.firstResidual
  let J := pCore 2 C
  let Q := C ⧸ J
  let q : C →* Q := QuotientGroup.mk' J
  let I := EC.map q
  have hC : C = centralizer (omegaOneCenter (S : Subgroup G) : Set G) := by
    change centralizer ({z} : Set G) = _
    rw [← centralizer_closure, ← zpowers_eq_closure, hgen]
  have hEsub : SubnormalIn E C := by
    rw [hC]
    exact (nine_two_ambient_setup
      (ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three).toAmbientSectionNineContext).2.2.2
  have hRE : R ≤ E := map_mono (twoCoreIn_le _)
  have hRJ : R ≤ twoCoreIn C := by
    obtain ⟨w, _, hw, hlo, _, _⟩ := ctx.involution_centralizer_core
    rwa [← centralizer_closure, ← zpowers_eq_closure, hw, ← hC] at hlo
  have hRJC (r : R) : (⟨r, hEsub.1 (hRE r.property)⟩ : C) ∈ J := by
    obtain ⟨j, hj, he⟩ := hRJ r.property
    have heq : j = (⟨r, hEsub.1 (hRE r.property)⟩ : C) := Subtype.ext he
    exact heq ▸ hj
  have hECcard : Nat.card EC = 2560 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEsub.1).toEquiv).trans ctx.first_residual_group_card
  let T := J.subgroupOf EC
  have hTle : Nat.card T ≤ 512 := by
    have hdC : Nat.card T ∣ 1024 := by
      let f : T →* J := {
        toFun := fun t => ⟨t.1.1, t.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
      have hinj : Function.Injective f := by
        intro a b h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun j : J => (j : C)) h
      have hh := card_dvd_of_injective f hinj
      rwa [(ctx.involution_centralizer_core_eq_at_generator hS z hgen).2] at hh
    have hdE : Nat.card T ∣ 2560 := hECcard ▸ T.card_subgroup_dvd_card
    have hd := Nat.dvd_gcd hdC hdE
    norm_num at hd
    exact Nat.le_of_dvd (by decide) hd
  have hTge : 512 ≤ Nat.card T := by
    let f : R →* T := {
      toFun := fun r => ⟨⟨⟨r, hEsub.1 (hRE r.property)⟩, hRE r.property⟩, hRJC r⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun t : T => (t.1.1 : G)) h
    have hh := Nat.card_le_card_of_injective f hinj
    rwa [ctx.first_residual_structure.1] at hh
  have hTcard : Nat.card T = 512 := Nat.le_antisymm hTle hTge
  have hIcard : Nat.card I = 5 := by
    have hh := T.index_mul_card
    rw [hTcard, hECcard] at hh
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
  let P : Sylow 5 C := default
  have hPcard : Nat.card P = 5 := ctx.involution_centralizer_sylow_five_card hS z hz hgen P
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
  exact ⟨eq_of_le_of_card_ge hIcore (by rw [hIcard, hcorecard]), hcorecard⟩

/-- At the upper endpoint the full involution centralizer normalizes both
the first-step residual group and its two-core. -/
public theorem LargeTerminalContext.first_residual_normal_of_large_card {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    NormalIn ((EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
      (ctx.first ⊔ ctx.second).subtype) (centralizer ({z} : Set G)) ∧
    NormalIn ctx.firstResidual (centralizer ({z} : Set G)) := by
  let C := centralizer ({z} : Set G)
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let P := GAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep
  let E := (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map K.subtype
  let J := twoCoreIn C
  have hP : P.map K.subtype = ctx.second :=
    (nine_two_ambient_setup
      (ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three).toAmbientSectionNineContext).2.2.1
  have hE : E = twoResidualIn ctx.second := by
    change (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map K.subtype = _
    have hh : EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep = twoResidualIn P :=
      ctx.terminal.Γ.twoResidualAt_def _
    rw [hh]
    exact map_twoResidualAmbient_of_subgroup_image P K.subtype ctx.second hP
  have hEC : E ≤ C := (hE ▸ twoResidualIn_le ctx.second).trans
    (ctx.second_le_residual_normalizer.trans
      (ctx.residual_normalizer_le_involution_centralizer z hz hgen))
  have hJ : J = twoCoreIn ctx.second :=
    (ctx.involution_centralizer_core_eq_at_generator hS z hgen).1
  have hJN : J ≤ normalizer (E : Set G) := by
    rw [hJ, hE]
    exact (twoCoreIn_le ctx.second).trans
      ((normal_subgroupOf_iff_le_normalizer (twoResidualIn_le ctx.second)).mp
        (twoResidualIn_normal ctx.second))
  have hJtwo : IsPGroup 2 J := pCore_isPGroup.map C.subtype
  have hres : twoResidualIn (E ⊔ J) = E := by
    rw [hE] at hJN ⊢
    exact twoResidualIn_sup_twoGroup_eq ctx.second J hJtwo hJN
  have hLnormal : ((E ⊔ J).subgroupOf C).Normal := by
    have hnormal : (((E.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C))).comap
        (QuotientGroup.mk' (pCore 2 C))).Normal := by
      rw [(ctx.involution_centralizer_quotient_five_core hS z hz hgen).1]
      infer_instance
    rw [comap_map_eq, QuotientGroup.ker_mk'] at hnormal
    have hJC : J ≤ C := twoCoreIn_le C
    rw [subgroupOf_sup hEC hJC]
    have hJCeq : J.subgroupOf C = pCore 2 C := subgroupOf_map_subtype_eq _
    rwa [hJCeq]
  have hLC : E ⊔ J ≤ C := sup_le hEC (twoCoreIn_le C)
  have hEnormal : (E.subgroupOf C).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hEC).mpr
    intro c hc
    rw [mem_normalizer_iff_map_conj_eq, ← hres]
    change (twoResidualIn (E ⊔ J)).map (MulAut.conj c).toMonoidHom = _
    rw [← twoResidualIn_map_equiv]
    exact congrArg twoResidualIn (mem_normalizer_iff_map_conj_eq.mp
      ((normal_subgroupOf_iff_le_normalizer hLC).mp hLnormal hc))
  have hRE : ctx.firstResidual = twoCoreIn E := by
    let E0 := EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep
    let e := E0.equivMapOfInjective K.subtype K.subtype_injective
    have hp := pCore_map_iso 2 e
    change ((pCore 2 E0).map E0.subtype).map K.subtype = (pCore 2 E).map E.subtype
    rw [← hp, map_map, map_map]
    rfl
  refine ⟨⟨hEC, hEnormal⟩, ?_⟩
  rw [hRE]
  exact ⟨(twoCoreIn_le E).trans hEC,
    twoCoreIn_normal_of_normal E C hEC hEnormal⟩

/-- A bound on the full quotient upgrades core equality to equality of the
full involution centralizer with the second local group. -/
public theorem LargeTerminalContext.involution_centralizer_eq_second_of_quotient_card_le
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (hquot : Nat.card (centralizer ({z} : Set G) ⧸
      pCore 2 (centralizer ({z} : Set G))) ≤ 20) :
    centralizer ({z} : Set G) = ctx.second := by
  have hPC : ctx.second ≤ centralizer ({z} : Set G) :=
    ctx.second_le_residual_normalizer.trans
      (ctx.residual_normalizer_le_involution_centralizer z hz hgen)
  have hcore := (ctx.involution_centralizer_core_eq_at_generator hS z hgen).2
  have hcount := (pCore 2 (centralizer ({z} : Set G))).card_mul_index
  rw [hcore, index_eq_card] at hcount
  apply (eq_of_le_of_card_ge hPC ?_).symm
  rw [ctx.second_card_of_large_card hS]
  omega

/-- The full distinguished involution-centralizer quotient has order at most
twenty at the upper terminal endpoint. -/
public theorem LargeTerminalContext.involution_centralizer_quotient_card_le
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    Nat.card (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))) ≤ 20 := by
  let C := centralizer ({z} : Set G)
  let E0 := (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
    (ctx.first ⊔ ctx.second).subtype
  let E := E0.subgroupOf C
  let R := ctx.firstResidual.subgroupOf C
  obtain ⟨hEn, hRn⟩ := ctx.first_residual_normal_of_large_card hS z hz hgen
  let _ : E.Normal := hEn.2
  let _ : R.Normal := hRn.2
  let e : R ≃* ctx.firstResidual := subgroupOfEquivOfLe hRn.1
  have hRQ : R ≤ pCore 2 C := by
    have hRC : ctx.firstResidual ≤ twoCoreIn C := by
      obtain ⟨w, _, hw, hlo, _, _⟩ := ctx.involution_centralizer_core
      have hc : C = centralizer (omegaOneCenter (S : Subgroup G) : Set G) := by
        change centralizer ({z} : Set G) = _
        rw [← centralizer_closure, ← zpowers_eq_closure, hgen]
      rwa [← centralizer_closure, ← zpowers_eq_closure, hw, ← hc] at hlo
    intro r hr
    obtain ⟨j, hj, hjr⟩ := hRC hr
    have heq : j = r := Subtype.ext hjr
    exact heq ▸ hj
  have hRE : R ≤ E := fun _ hr => map_mono (twoCoreIn_le _) hr
  have hRcard : Nat.card R = 512 :=
    (Nat.card_congr e.toEquiv).trans ctx.first_residual_structure.1
  have hEcard : Nat.card E = 2560 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEn.1).toEquiv).trans ctx.first_residual_group_card
  have hRtwo : IsPGroup 2 R := pCore_isPGroup.to_le hRQ
  let _ : Fact (IsPGroup 2 R) := ⟨hRtwo⟩
  let _ : Group.IsNilpotent R := hRtwo.isNilpotent
  have hR0two : IsPGroup 2 ctx.firstResidual := hRtwo.of_equiv e
  let _ : Group.IsNilpotent ctx.firstResidual := hR0two.isNilpotent
  have hclass : Group.nilpotencyClass R = 3 := by
    have hlo := Group.nilpotencyClass_le_of_surjective e.toMonoidHom e.surjective
    have hhi := Group.nilpotencyClass_le_of_surjective e.symm.toMonoidHom e.symm.surjective
    rw [ctx.first_residual_structure.2.2.2.2.2] at hlo hhi
    omega
  have hZ : Nat.card (center R) = 2 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans ctx.first_residual_structure.2.2.2.1
  have hDmap : (commutator R).map e.toMonoidHom = commutator ctx.firstResidual := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  have hD : Nat.card (commutator R) = 32 := by
    rw [← card_map_of_injective (f := e.toMonoidHom) (K := commutator R) e.injective, hDmap]
    exact ctx.first_residual_structure.2.2.2.2.1
  have hV : Nat.card (R ⧸ frattini R) = 16 :=
    (frattini_card_congr e).trans ctx.first_residual_frattini_structure.2
  have hPhiCard : Nat.card (frattini R) = 32 := by
    have hh := (frattini R).card_mul_index
    rw [index_eq_card, hV, hRcard] at hh
    omega
  have hPhi : commutator R = frattini R :=
    eq_of_le_of_card_ge (commutator_le_frattini_of_isPGroup (p := 2)) (by rw [hD, hPhiCard])
  exact quotient_card_le_twenty_of_normal_class_three_residual
    (ctx.localStructure C (Theory.GroupTheory.isTwoLocal_involution_centralizer hz)).2
    (ctx.involution_centralizer_core_eq_at_generator hS z hgen).2 R E hRQ hRE
    hRcard hEcard hclass hZ hPhi hD

/-- The distinguished involution has exactly the second local group as its
full centralizer. -/
public theorem LargeTerminalContext.involution_centralizer_eq_second
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    centralizer ({z} : Set G) = ctx.second :=
  ctx.involution_centralizer_eq_second_of_quotient_card_le hS z hz hgen
    (ctx.involution_centralizer_quotient_card_le hS z hz hgen)

end Stellmacher.Recognition
