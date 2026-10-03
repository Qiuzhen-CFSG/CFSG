module

public import Stellmacher.SectionNine.DistanceOneVstarContainments
public import Theory.GroupTheory.QuaternionCentralProductFactors
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.IndexTwoCoprimeAutomorphism
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs

/-!
# Preliminary geometry of the residual Vstar action

The terminal local quotient in the explicit distance-one local conclusion is
SL₂(2), of order six. Surjectivity makes three divide the terminal stabilizer
order, so Cauchy's theorem produces an element of order three. Such an element
belongs to every normal subgroup of two-power index: its image in the quotient
has order dividing three and coprime to three, hence is trivial. Intersecting
these normal subgroups puts the element in the actual terminal two-residual.

At critical distance one the actual Vstar is normal in the terminal stabilizer.
The local conclusion describes it as a product of commuting quaternion factors.
The intrinsic-factor theorem shows that every cube-one automorphism preserving
the product preserves each factor. Thus every actual order-three actor in the
terminal residual normalizes both factors. This is an invariant-factor result;
nontriviality of both factor actions and the full fixed-centralizer bound
remain separate geometric obligations.

The entire Vstar action is nontrivial. The quaternion product has order32,
and the Sylow image in the terminal SL2(2) quotient has order2, so the core has
order64. An actor fixing Vstar would fix the full core by the index-two
coprime automorphism theorem. Characteristic two then puts it in that core,
contradicting its order three. This excludes total triviality, while the case
of an actor trivial on just one quaternion factor remains to be ruled out.

Finally the terminal stabilizer has order384. Its normal centralizer of Vstar
contains no element of order3 by the preceding nontriviality result. Its order
therefore divides2^7, so it is a normal two-subgroup and lies in the terminal
core. This controls the full local kernel needed by the subsequent factor-swap
argument.

These are preliminary parts of the residual-action calculation used in
Stellmacher (9.1), Journal of Algebra 190 (1997), p.48 / PDF p.38 of
`refs/files/stellmacher-n-group.pdf`. The local conclusion is an explicit input;
no classification producer or downstream normalizer construction is imported.
-/

open Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven

universe u

private theorem order_three_mem_residual
    {G : Type u} [Group G] [Finite G] (P : Subgroup G)
    (actor : P) (horder : orderOf actor = 3) :
    actor ∈ twoResidualSubgroup P := by
  rw [twoResidualSubgroup, Subgroup.mem_sInf]
  intro normal hnormal
  let _ : normal.Normal := hnormal.1
  have hgroup : IsPGroup 2 (P ⧸ normal) := by
    rw [IsPGroup.iff_card]
    obtain ⟨power, hpower⟩ := hnormal.2
    exact ⟨power, by simpa only [Subgroup.index_eq_card] using hpower⟩
  have hdvd : orderOf (QuotientGroup.mk' normal actor) ∣ 3 := by
    rw [← horder]
    exact orderOf_map_dvd (QuotientGroup.mk' normal) actor
  have hcoprime := hgroup.orderOf_coprime (n := 3) (by decide)
    (QuotientGroup.mk' normal actor)
  have hone : orderOf (QuotientGroup.mk' normal actor) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcoprime (dvd_refl _) hdvd
  exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hone)

namespace Stellmacher.SectionNine

public theorem distance_one_terminal_residual_order_three
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlocal : DistanceOneLocalConclusion ctx) :
    ∃ actor : G, actor ∈ EAt ctx.Γ ctx.criticalPath.a' ∧ orderOf actor = 3 := by
  obtain ⟨projection, hsurjective, _⟩ := hlocal.2.1
  have hcard : Nat.card SL2Two = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  have hdiv : 3 ∣ Nat.card (GAt ctx.Γ ctx.criticalPath.a') := by
    have hmodeldiv := Subgroup.card_dvd_of_surjective projection hsurjective
    rw [hcard] at hmodeldiv
    exact dvd_trans (by decide : 3 ∣ 6) hmodeldiv
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨actor, horder⟩ := exists_prime_orderOf_dvd_card' 3 hdiv
  refine ⟨actor, ?_, ?_⟩
  · change actor.val ∈ ctx.Γ.twoResidualAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def]
    exact Subgroup.mem_map_of_mem _ (order_three_mem_residual _ actor horder)
  · simpa only [Subgroup.orderOf_coe] using horder


public theorem distance_one_vstar_factor_invariance
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hlocal : DistanceOneLocalConclusion ctx) :
    let Vstar := conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    ∃ left right : Subgroup G,
      IsModel left Q8 ∧ IsModel right Q8 ∧ Vstar = left ⊔ right ∧
      Nat.card (left ⊓ right : Subgroup G) = 2 ∧
      (∀ x ∈ left, ∀ y ∈ right, x * y = y * x) ∧
      ∀ actor : G, actor ∈ EAt ctx.Γ ctx.criticalPath.a' → orderOf actor = 3 →
        actor ∈ Subgroup.normalizer (left : Set G) ∧
          actor ∈ Subgroup.normalizer (right : Set G) := by
  obtain ⟨left, right, hleft, hright, hjoin, hinter, hcomm, _⟩ := hlocal.2.2.2.2
  refine ⟨left, right, hleft, hright, hjoin, hinter, hcomm, ?_⟩
  intro actor hactor horder
  have hn := (distance_one_vstar_containments ctx hlength).1
  have hactorB : actor ∈ GAt ctx.Γ ctx.criticalPath.a' := by
    apply SevenSix.twoResidualIn_le (GAt ctx.Γ ctx.criticalPath.a')
    simpa only [EAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def,
      GAt, CosetGraphContext.stabilizer] using hactor
  have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hn.1).mp hn.2 hactorB
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm
  rw [hjoin] at hmap
  have hpow : actor ^ 3 = 1 := by rw [← horder]; exact pow_orderOf_eq_one actor
  have hcube : ∀ x : G, (MulAut.conj actor) ((MulAut.conj actor) ((MulAut.conj actor) x)) = x := by
    intro x
    have hc : (MulAut.conj actor) ^ 3 = 1 := by rw [← map_pow, hpow, map_one]
    have hx := congrArg (fun e : MulAut G => e x) hc
    simpa [pow_succ] using hx
  have hfactors := Subgroup.quaternion_factors_invariant_of_cube_eq_one
    left right hleft hright hinter hcomm (MulAut.conj actor) hmap hcube
  exact ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfactors.1,
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfactors.2⟩

private theorem vstar_card {G : Type*} [Group G] [Finite G]
    (V : Subgroup G) (hV : IsCentralProductQ8Q8 V) : Nat.card V = 32 := by
  obtain ⟨B, C, ⟨eB⟩, ⟨eC⟩, rfl, hinter, hcomm, _⟩ := hV
  have hB : Nat.card B = 8 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hC : Nat.card C = 8 := by
    rw [Nat.card_congr eC.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hn : C ≤ Subgroup.normalizer (B : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro c hc b hb
    exact hcomm b hb c hc
  have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes B C hn
  rw [hB, hC, hinter] at hcard
  omega

public theorem distance_one_vstar_card
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlocal : DistanceOneLocalConclusion ctx) :
    Nat.card (conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')) = 32 :=
  vstar_card _ hlocal.2.2.2.2

public theorem distance_one_terminal_core_index_in_sylow {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hlocal : DistanceOneLocalConclusion ctx) :
    (QAt ctx.Γ ctx.criticalPath.a').relIndex T = 2 := by
  have hend : ctx.criticalPath.a' = ctx.criticalPath.firstStep := by
    rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
    congr 1
    exact Fin.ext hlength
  have hs := (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  rw [← hend] at hs
  obtain ⟨_, sylow, hT⟩ := hs
  obtain ⟨projection, hsurj, hker⟩ := hlocal.2.1
  have hcore : QAt ctx.Γ ctx.criticalPath.a' ≤ GAt ctx.Γ ctx.criticalPath.a' := by
    change ctx.Γ.twoCoreAt _ ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hQmap : QAt ctx.Γ ctx.criticalPath.a' =
      projection.ker.map (GAt ctx.Γ ctx.criticalPath.a').subtype := by
    rw [hker, Subgroup.map_subgroupOf_eq_of_le hcore]
  rw [hQmap]
  conv_lhs => arg 2; rw [← hT]
  rw [Subgroup.relIndex_map_map_of_injective _ _
    (GAt ctx.Γ ctx.criticalPath.a').subtype_injective, Subgroup.relIndex_ker]
  let image := sylow.mapSurjective hsurj
  change Nat.card image = 2
  rw [Sylow.card_eq_multiplicity,
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
      (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)]
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.factorization_mul (by decide) (by decide)]
  norm_num [Nat.prime_two, Nat.prime_three]


public theorem distance_one_terminal_order_three_moves_vstar
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hlocal : DistanceOneLocalConclusion ctx)
    (actor : G) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.a')
    (horder : orderOf actor = 3) :
    ∃ x : G, x ∈ conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a') ∧ ¬ Commute actor x := by
  classical
  let V := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let terminal := GAt ctx.Γ ctx.criticalPath.a'
  have hcont := distance_one_vstar_containments ctx hlength
  have hVQ : V ≤ Q := hcont.2.1
  have hQT : Q ≤ T := by
    have hend : ctx.criticalPath.a' = ctx.criticalPath.firstStep := by
      rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
      congr 1
      exact Fin.ext hlength
    change QAt ctx.Γ ctx.criticalPath.a' ≤ T
    rw [hend]
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  have hQp : IsPGroup 2 Q := by
    change IsPGroup 2 (ctx.Γ.twoCoreAt ctx.criticalPath.a')
    rw [ctx.Γ.twoCoreAt_def]
    exact pCore_isPGroup.map _
  have hVcard : Nat.card V = 32 := vstar_card V hlocal.2.2.2.2
  have hQcard : Nat.card Q = 64 := by
    have hc := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) Q T bot_le hQT
    simp only [Subgroup.relIndex_bot_left] at hc
    have hi : Q.relIndex T = 2 := distance_one_terminal_core_index_in_sylow ctx hlength hlocal
    rw [hi, hlocal.2.2.1] at hc
    omega
  have hindex : (V.subgroupOf Q).index = 2 := by
    have hc := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) V Q bot_le hVQ
    simp only [Subgroup.relIndex_bot_left] at hc
    rw [hVcard, hQcard] at hc
    change V.relIndex Q = 2
    omega
  by_contra hnot
  push Not at hnot
  have hfixV : ∀ x ∈ V, Commute actor x := hnot
  have hnorm : actor ∈ Subgroup.normalizer (Q : Set G) :=
    SevenSix.stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a' hactor
  let actorN : Subgroup.normalizer (Q : Set G) := ⟨actor, hnorm⟩
  let e : MulAut Q := Q.normalizerMonoidHom actorN
  have hpow : actor ^ 3 = 1 := by rw [← horder]; exact pow_orderOf_eq_one actor
  have hethree : e ^ 3 = 1 := by
    have hh : actorN ^ 3 = 1 := Subtype.ext hpow
    change (Q.normalizerMonoidHom actorN) ^ 3 = 1
    rw [← map_pow, hh, map_one]
  have hefix : ∀ x ∈ V.subgroupOf Q, e x = x := by
    intro x hx
    apply Subtype.ext
    change actor * (x : G) * actor⁻¹ = (x : G)
    rw [(hfixV x hx).eq, mul_inv_cancel_right]
  have he := Subgroup.eq_one_of_cube_eq_one_of_fixed_index_two (V.subgroupOf Q)
    hindex (hQp.to_subgroup _) e hethree hefix
  have hcentral : actor ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hh := congrArg (fun f : MulAut Q => (f ⟨x, hx⟩ : G)) he
    change actor * x * actor⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hchar : IsCharacteristicTwoType terminal := by
    have hend : ctx.criticalPath.a' = ctx.criticalPath.firstStep := by
      rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
      congr 1
      exact Fin.ext hlength
    change IsCharacteristicTwoType (GAt ctx.Γ ctx.criticalPath.a')
    rw [hend]
    exact (SevenSix.edge_characteristic_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  have hactorQ : actor ∈ Q := by
    have hc : (⟨actor, hactor⟩ : terminal) ∈
        Subgroup.centralizer (pCore 2 terminal : Set terminal) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hcentral x (by
        change (x : G) ∈ ctx.Γ.twoCoreAt ctx.criticalPath.a'
        rw [ctx.Γ.twoCoreAt_def]
        exact Subgroup.mem_map_of_mem _ hx)
    change actor ∈ ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoCoreAt_def]
    exact Subgroup.mem_map_of_mem _ (hchar hc)
  have hcop := hQp.orderOf_coprime (n := 3) (by decide) (⟨actor, hactorQ⟩ : Q)
  change orderOf ((⟨actor, hactorQ⟩ : Q) : G) = 3 at horder
  rw [Subgroup.orderOf_coe] at horder
  rw [horder] at hcop
  norm_num at hcop

public theorem distance_one_terminal_card
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hlocal : DistanceOneLocalConclusion ctx) :
    Nat.card (GAt ctx.Γ ctx.criticalPath.a') = 384 := by
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let terminal := GAt ctx.Γ ctx.criticalPath.a'
  have hend : ctx.criticalPath.a' = ctx.criticalPath.firstStep := by
    rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
    congr 1
    exact Fin.ext hlength
  have hs := (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  rw [← hend] at hs
  obtain ⟨hTB, sylow, hT⟩ := hs
  have hQT : Q ≤ T := by
    intro x hx
    change x ∈ ctx.Γ.twoCoreAt ctx.criticalPath.a' at hx
    rw [ctx.Γ.twoCoreAt_def] at hx
    obtain ⟨xx, hxx, rfl⟩ := hx
    exact (congrArg (fun D : Subgroup G => (xx : G) ∈ D) hT).mp
      (Subgroup.mem_map_of_mem _ (pCore_isPGroup.le_sylow_of_normal sylow hxx))
  obtain ⟨projection, hsurj, hker⟩ := hlocal.2.1
  have hQB : Q.relIndex terminal = 6 := by
    change (Q.subgroupOf terminal).index = 6
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    exact SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  have hidx := Subgroup.relIndex_mul_relIndex Q T terminal hQT hTB
  rw [distance_one_terminal_core_index_in_sylow ctx hlength hlocal, hQB] at hidx
  have hTidx : T.relIndex terminal = 3 := by omega
  have hc := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) T terminal bot_le hTB
  simp only [Subgroup.relIndex_bot_left] at hc
  rw [hlocal.2.2.1, hTidx] at hc
  exact hc.symm

public theorem distance_one_vstar_centralizer_le_core
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hlocal : DistanceOneLocalConclusion ctx) :
    let V := conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.centralizer (V : Set G) ≤
      QAt ctx.Γ ctx.criticalPath.a' := by
  let V := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  let terminal := GAt ctx.Γ ctx.criticalPath.a'
  change terminal ⊓ Subgroup.centralizer (V : Set G) ≤ QAt ctx.Γ ctx.criticalPath.a'
  have hn := (distance_one_vstar_containments ctx hlength).1
  let _ : (V.subgroupOf terminal).Normal := hn.2
  let K := Subgroup.centralizer (V.subgroupOf terminal : Set terminal)
  have hKnot : ¬ 3 ∣ Nat.card K := by
    intro hdvd
    let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
    obtain ⟨actor, horder⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
    have ho : orderOf (actor : G) = 3 := by
      simpa only [Subgroup.orderOf_coe] using horder
    obtain ⟨x, hx, hnc⟩ := distance_one_terminal_order_three_moves_vstar ctx hlength hlocal
      actor actor.val.property ho
    apply hnc
    have hh := Subgroup.mem_centralizer_iff.mp actor.property (⟨x, hn.1 hx⟩ : terminal) hx
    exact (congrArg (fun y : terminal => (y : G)) hh).symm
  have hKd : Nat.card K ∣ 2 ^ 7 * 3 := by
    have hd := K.card_subgroup_dvd_card
    rw [distance_one_terminal_card ctx hlength hlocal] at hd
    exact hd
  have hcop : (Nat.card K).Coprime 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hKnot).symm
  have hdiv : Nat.card K ∣ 2 ^ 7 := hcop.dvd_of_dvd_mul_right hKd
  have hKp : IsPGroup 2 K := by
    rw [IsPGroup.iff_card]
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    exact ⟨k, hk⟩
  have hKcore : K ≤ pCore 2 terminal := le_sSup ⟨inferInstance, hKp⟩
  intro actor hactor
  have hmem : (⟨actor, hactor.1⟩ : terminal) ∈ K := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hactor.2 x hx)
  change actor ∈ ctx.Γ.twoCoreAt ctx.criticalPath.a'
  rw [ctx.Γ.twoCoreAt_def]
  exact Subgroup.mem_map_of_mem _ (hKcore hmem)


end Stellmacher.SectionNine
