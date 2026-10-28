module

public import Stellmacher.Recognition.LargeTerminalReeSquaringFourthPower
public import Stellmacher.Recognition.LargeTerminalReeCoreTable
public import Stellmacher.Recognition.LargeTerminalInvertingSylowData
public import Stellmacher.Recognition.LargeTerminalReeCoreModelOrientation
public import Stellmacher.Recognition.LargeTerminalFirstCoreSecondCenter
public import Theory.SpecificGroups.ReeTwo.CoreFiveActionNormalization
public import Theory.SpecificGroups.ReeTwo.FixingNonsplitFirstCore

/-!
# Excluding the nonsplit terminal squaring extension

A root-fixing squaring lift with nontrivial fourth power generates a local
Sylow subgroup together with the second core. The marked Ree coordinates
identify this as a nonsplit fixing extension. Its intrinsic first core has
a distinguished involution fixed by every automorphism, by the model's
fourth-root counts. Marked Sylow conjugacy and the intrinsic description of
the actual first core contradict the neighboring parabolic's automorphism
moving that involution. Consequently every two-power squaring lift has
fourth power one.

The transport follows the inverting-extension argument in
`LargeTerminalInvertingSylowIdentification`, with the separate root-fixing,
nonsplit certificate. No splitting is deduced from the quotient order.
Source: Thompson VI, pp.629–630, and Shinoda (1975), pp.81–83.
-/

namespace Stellmacher.Recognition
universe u
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup

private theorem normalized_five_action
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAP : A ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (t z : twoCoreIn ctx.second)
    (hgen : zpowers (t : G) = twoCoreIn ctx.second ⊓ centralizer (A : Set G))
    (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core)
    (het : eQ t = ReeTwo.Core.root 2) (hez : eQ z = ReeTwo.Core.root 9) :
    ∃ (e : twoCoreIn ctx.second ≃* ReeTwo.Core) (a : A),
      e t = ReeTwo.Core.root 2 ∧ e z = ReeTwo.Core.root 9 ∧
      ctx.reeCoreAction e (inclusion hAP a) = ReeTwo.Core.c := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := A)
  let f := ctx.reeCoreAction eQ
  let rho := f (inclusion hAP a)
  have hrho : orderOf rho = 5 := by
    apply orderOf_eq_prime
    · change f (inclusion hAP a) ^ 5 = 1
      rw [← map_pow, ← map_pow]
      have hp : a ^ 5 = 1 := hA ▸ pow_card_eq_one' (x := a)
      rw [hp, map_one, map_one]
    · intro he
      have htriv : ∀ b : A, f (inclusion hAP b) = 1 := by
        intro b
        obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (ha b)
        rw [← hn, map_zpow, map_zpow]
        change rho ^ n = 1
        rw [he, one_zpow]
      have htop : (centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second) = ⊤ := by
        apply eq_top_iff.mpr
        intro q _
        apply mem_centralizer_iff.mpr
        intro b hb
        have hh := ctx.reeCoreAction_apply eQ (inclusion hAP ⟨b, hb⟩) q
        rw [htriv] at hh
        simp only [MulAut.one_apply, eQ.symm_apply_apply] at hh
        exact mul_inv_eq_iff_eq_mul.mp hh.symm
      rw [htop, card_top, Nat.card_congr eQ.toEquiv, ReeTwo.Core.card] at hcard
      norm_num at hcard
  have htfix : rho (ReeTwo.Core.root 2) = ReeTwo.Core.root 2 := by
    rw [← het]
    apply eQ.symm.injective
    apply Subtype.ext
    rw [ctx.reeCoreAction_apply, eQ.symm_apply_apply]
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp (hgen.le (mem_zpowers (t : G))).2 a a.property)
  obtain ⟨d, hdt, hdz, hd⟩ := ReeTwo.Core.exists_marked_conjugator_of_orderOf_eq_five rho hrho htfix
  refine ⟨eQ.trans d, a, ?_, ?_, ?_⟩
  · exact (congrArg d het).trans hdt
  · exact (congrArg d hez).trans hdz
  · change d * rho * d⁻¹ = ReeTwo.Core.c
    exact hd

private theorem no_nonsplit_fixing_lift
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (t z : twoCoreIn ctx.second) (hz2 : orderOf (z : G) = 2)
    (hzgen : zpowers (z : G) = omegaOneCenter (S : Subgroup G))
    (htgen : zpowers (t : G) = twoCoreIn ctx.second ⊓ centralizer (A : Set G))
    (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core)
    (het : eQ t = ReeTwo.Core.root 2) (hez : eQ z = ReeTwo.Core.root 9)
    (s : G) (hsP : s ∈ ctx.second) (hsA : s ∈ normalizer (A : Set G))
    (hs16 : s ^ 16 = 1) (hsa : ∀ c ∈ A, s * c * s⁻¹ = c ^ 2)
    (hst : s * (t : G) * s⁻¹ = t) (hs4 : s ^ 4 = (z : G)) : False := by
  obtain ⟨e, a, het, hez, ha⟩ := normalized_five_action ctx A hA hAP hcard t z htgen eQ het hez
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let sP : ctx.second := ⟨s, hsP⟩
  have hsP16 : sP ^ 16 = 1 := Subtype.ext hs16
  have hp : IsPGroup 2 (zpowers sP) := by
    apply (isPGroup_iff_card_dvd_pow).mpr
    exact ⟨4, by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hsP16⟩
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  have hsT : sP ∈ T := hT (mem_zpowers sP)
  have hQT : ∀ q : twoCoreIn ctx.second,
      (⟨(q : G), twoCoreIn_le ctx.second q.property⟩ : ctx.second) ∈ T := by
    intro q
    obtain ⟨qP, hqP, he⟩ := q.property
    have hqT := (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal T hqP
    have heq : (⟨(q : G), twoCoreIn_le ctx.second q.property⟩ : ctx.second) = qP :=
      Subtype.ext he.symm
    rw [heq]
    exact hqT
  let f := ctx.reeCoreAction e
  let beta := f sP
  have hconj : ∀ q, (e.symm (beta q) : G) = s * (e.symm q : G) * s⁻¹ := by
    intro q
    simpa only [e.apply_symm_apply] using ctx.reeCoreAction_apply e sP (e.symm q)
  have hbc : beta * ReeTwo.Core.c * beta⁻¹ = ReeTwo.Core.c ^ 2 := by
    rw [← ha]
    change f sP * f (inclusion hAP a) * (f sP)⁻¹ = f (inclusion hAP a) ^ 2
    rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
    apply congrArg f
    exact Subtype.ext (hsa a a.property)
  have hbfix : beta (ReeTwo.Core.root 2) = ReeTwo.Core.root 2 := by
    rw [← het]
    apply e.symm.injective
    apply Subtype.ext
    rw [ctx.reeCoreAction_apply, e.symm_apply_apply]
    exact hst
  have hb4 : beta ^ 4 = 1 := by
    change (f sP) ^ 4 = 1
    rw [← map_pow]
    apply MulEquiv.ext
    intro q
    apply e.symm.injective
    apply Subtype.ext
    have hhq := ctx.reeCoreAction_apply e (sP ^ 4) (e.symm q)
    simp only [e.apply_symm_apply] at hhq
    rw [hhq]
    change s ^ 4 * (e.symm q : G) * (s ^ 4)⁻¹ = (e.symm q : G)
    rw [hs4]
    have hzc : z ∈ center (twoCoreIn ctx.second) := by
      apply mem_center_iff.mpr
      intro x
      apply e.injective
      simpa only [map_mul, hez] using
        mem_center_iff.mp ReeTwo.Core.root_nine_mem_center (e x)
    exact mul_inv_eq_iff_eq_mul.mpr
      (congrArg Subtype.val (mem_center_iff.mp hzc (e.symm q))).symm
  let i : T →* G := ctx.second.subtype.comp T.toSubgroup.subtype
  have hi : Function.Injective i := ctx.second.subtype_injective.comp T.toSubgroup.subtype_injective
  let j : ReeTwo.Core →* T :=
    { toFun := fun q => ⟨⟨(e.symm q : G), twoCoreIn_le ctx.second (e.symm q).property⟩, hQT (e.symm q)⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; exact congrArg (fun q : twoCoreIn ctx.second => (q : G)) e.symm.map_one
      map_mul' := fun x y => by apply Subtype.ext; apply Subtype.ext; exact congrArg (fun q : twoCoreIn ctx.second => (q : G)) (e.symm.map_mul x y) }
  let sT : T := ⟨sP, hsT⟩
  have hj : ∀ q, i (j q) = (e.symm q : G) := fun _ => rfl
  have hjz : i (j (ReeTwo.Core.root 9)) = (z : G) := by
    rw [hj, ← hez, e.symm_apply_apply]
  have hgen : j.range ⊔ zpowers sT = ⊤ := by
    apply Subgroup.map_injective hi
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    have hrange : j.range.map i = twoCoreIn ctx.second := by
      rw [← MonoidHom.range_comp]
      ext x
      constructor
      · rintro ⟨q, rfl⟩
        exact (e.symm q).property
      · intro hx
        refine ⟨e ⟨x, hx⟩, ?_⟩
        exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
    rw [hrange]
    have hs4Q : s ^ 4 ∈ twoCoreIn ctx.second := by
      rw [hs4]
      exact z.property
    have hG := ctx.local_sylow_generated_by_squaring_lift hS A hA hAP s hsP hsA hsa hs4Q T hsT
    change twoCoreIn ctx.second ⊔ zpowers s = (⊤ : Subgroup T).map i
    rw [hG, ← MonoidHom.range_eq_map, MonoidHom.range_comp, range_subtype]
  have hcardT : Nat.card T = 4096 := by
    have hSP : (S : Subgroup G) ≤ ctx.second :=
      ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
    exact (Nat.card_congr ((T.equiv (S.subtype hSP)).trans
      (subgroupOfEquivOfLe hSP)).toEquiv).trans hS
  have hjconj : ∀ q, sT * j q * sT⁻¹ = j (beta q) := by
    intro q
    apply hi
    exact (hconj q).symm
  have hjfour : sT ^ 4 = j (ReeTwo.Core.root 9) := by
    apply hi
    rw [map_pow, hjz]
    exact hs4
  obtain ⟨hzK, hfixed⟩ := ReeTwo.FixingExtension.root_nine_firstCore_obstruction
    hcardT j sT beta hgen hb4 hbc hbfix hjconj hjfour
  obtain ⟨hzS, eS, heS⟩ := ctx.marked_equiv_local_sylow T z hz2 hzgen
    ⟨twoCoreIn_le ctx.second z.property, hQT z⟩
  have hfirst := ctx.first_core_eq_second_center_centralizer hS eQ
  have hcoreS : twoCoreIn ctx.first ≤ (S : Subgroup G) := by
    have hSP : (S : Subgroup G) ≤ ctx.first :=
      ctx.terminal.hypothesisTwo.fiveOne.P1_mem.1.2.1.1
    rintro x ⟨p, hp, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.first)).le_sylow_of_normal (S.subtype hSP) hp
  let eK : twoCoreIn ctx.first ≃* ReeTwo.FixingExtension.firstCore T :=
    (subgroupOfEquivOfLe hcoreS).symm.trans
      ((MulEquiv.subgroupCongr hfirst).trans (centralizerUpperCentralSeriesEquiv eS 2))
  let zK : ReeTwo.FixingExtension.firstCore T := ⟨j (ReeTwo.Core.root 9), hzK⟩
  apply ctx.first_core_not_equiv_fixed_involution
    ⟨z, ctx.central_involution_mem_first_core z hzgen⟩ hz2 hzgen zK hfixed
  refine ⟨eK, ?_⟩
  apply Subtype.ext
  apply hi
  exact heS.trans hjz.symm

/-- Every actual two-power squaring lift has fourth power one. The nonsplit
alternative contradicts the neighboring first-core geometry. -/
public theorem LargeTerminalContext.five_squaring_fourth_power_eq_one
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (b : G) (hbP : b ∈ ctx.second) (hbN : b ∈ normalizer (A : Set G))
    (hb16 : b ^ 16 = 1) (hb : ∀ c ∈ A, b * c * b⁻¹ = c ^ 2) : b ^ 4 = 1 := by
  rcases ctx.five_squaring_fourth_power_eq_one_or_central_involution
    hS z hz hgen A hA hfixed b hbP hb16 hb with hh | hh
  · exact hh
  exfalso
  let Q := twoCoreIn ctx.second
  have hzR : z ∈ ctx.firstResidual := by
    apply (show CenterAmbient ctx.firstResidual ≤ ctx.firstResidual from map_subtype_le _)
    rw [ctx.first_residual_center_eq_omegaOneCenter, ← hgen]
    exact mem_zpowers z
  have hRQ : ctx.firstResidual ≤ Q := by
    change ctx.firstResidual ≤ twoCoreIn ctx.second
    rw [ctx.derived_centralizer_supplement.1]
    exact le_sup_right
  let zQ : Q := ⟨z, hRQ hzR⟩
  obtain ⟨v, a, hvA, hvsq, hvgen, hframe⟩ :=
    ctx.exists_ree_frame_of_cyclic hS A hA hAP hAN hcard hcyc hfixed zQ hz hgen
  have hFcard : Nat.card (Q ⊓ centralizer (A : Set G) : Subgroup G) = 4 := by
    rw [← inf_comm (centralizer (A : Set G)) Q, ← subgroupOf_map_subtype,
      card_map_of_injective Q.subtype_injective]
    exact hcard
  have hv4 : orderOf (v : G) = 4 := by
    rw [← Nat.card_zpowers, hvgen]
    exact hFcard
  have hx := ctx.ree_core_relations_of_frame A hA hAN hfixed
    v zQ hz hgen hvA hvsq a hframe
  let f : ReeTwo.Core →* Q := ReeTwo.Core.lift hx
  have hfroot (i : ReeTwo.CoreRoot) :
      f (ReeTwo.Core.root i) = ReeTwo.frameRoots a v zQ i :=
    ReeTwo.Core.lift_root hx i
  have hfinj : Function.Injective f := ReeTwo.Core.hom_injective_of_last_root f (by
    rw [hfroot]
    change zQ ≠ 1
    intro he
    have heG : z = 1 := congrArg (fun q : Q => (q : G)) he
    rw [heG, orderOf_one] at hz
    contradiction)
  have hQS : Q ≤ (S : Subgroup G) := by
    have hSP : (S : Subgroup G) ≤ ctx.second :=
      ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
    rintro x ⟨q, hq, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
      (S.subtype hSP) hq
  have hQcard : Nat.card Q = 1024 := by
    have h := ctx.local_character_core_card hS
    rwa [Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv] at h
  let e : ReeTwo.Core ≃* Q := MulEquiv.ofBijective f
    ((Nat.bijective_iff_injective_and_card f).mpr
      ⟨hfinj, ReeTwo.Core.card.trans hQcard.symm⟩)
  have hev : e.symm v = ReeTwo.Core.root 2 := by
    apply e.injective
    exact (e.apply_symm_apply v).trans (hfroot 2).symm
  have hez : e.symm zQ = ReeTwo.Core.root 9 := by
    apply e.injective
    exact (e.apply_symm_apply zQ).trans (hfroot 9).symm
  have hbv := ctx.five_squaring_commutes_fixed_root hS z hz hgen A hA hAP hAN
    hcard hcyc hfixed b v hbP hb v.property hvA hv4
  exact no_nonsplit_fixing_lift ctx hS A hA hAP hcard v zQ hz hgen hvgen
    e.symm hev hez b hbP hbN hb16 hb (mul_inv_eq_iff_eq_mul.mpr hbv.eq) hh

end Stellmacher.Recognition
