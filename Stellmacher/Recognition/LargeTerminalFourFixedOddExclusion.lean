module

public import Stellmacher.Recognition.LargeTerminalInvolutionCentralizerQuotient
public import Stellmacher.Recognition.LargeTerminalFiveLocalAutomorphisms
public import Theory.GroupTheory.ThreeFiveHallComplement
public import Theory.GroupTheory.CharacteristicTwoOddAction
public import Theory.GroupAction.ThreeFiveFixedLowerBound

/-!
# The actual odd action for the terminal four-fixed exclusion

Confinement places the five-normalizer in the second local group. The full
local automizer and the fixed four-group give a five-centralizer of order
20. Consequently the five-fixed subgroup of the two-core of C_G(y) has
order at most four: its elements lie in that five-centralizer by confinement.
No containment of the full core in the second local core is used.

If three divides the involution-centralizer order, its solvability supplies
a Hall {3,5}-subgroup and Burnside transfer supplies a normal five-complement.
Its elementary central layer and the original five-subgroup give an actual
embedded semidirect product acting faithfully on the full centralizer core.
The involution y gives a common fixed involution. The coprime fixed-point
lower bound then forces at least eight five-fixed elements in the core,
contradicting the upper bound of four. Thus neither three nor fifteen divides
the involution centralizer order.

Source: Thompson VI, printed p.630. The full distinguished centralizer
identification is re-exported from LargeTerminalInvolutionCentralizerQuotient.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped IsMulCommutative

/-- Under confinement the ambient five-centralizer has order twenty. -/
public theorem LargeTerminalContext.five_centralizer_card_twenty_of_confinement
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (hfixed : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4) :
    Nat.card (centralizer (A : Set G)) = 20 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let M := ctx.second
  let Q := twoCoreIn M
  let N := normalizer (A : Set G)
  let C := centralizer (A : Set G)
  have hAM : A ≤ M := A.le_normalizer.trans hN
  have hQp : IsPGroup 2 Q := pCore_isPGroup.map M.subtype
  have hAp : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hd : Disjoint Q A := IsPGroup.disjoint_of_ne 2 5 (by decide) _ _ hQp hAp
  have hAQ : A ≤ normalizer (Q : Set G) := hAM.trans
    ((normal_subgroupOf_iff_le_normalizer (twoCoreIn_le M)).mp (twoCoreIn_normal M))
  have hQN : Q ⊓ N = Q ⊓ C := by
    apply le_antisymm _ (inf_le_inf_left Q (Subgroup.centralizer_le_normalizer _))
    refine le_inf inf_le_left ?_
    rw [← commutator_eq_bot_iff_le_centralizer]
    apply bot_unique
    apply le_trans _ hd.le_bot
    exact le_inf ((commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hAQ))
      (le_normalizer_iff_commutator_le_right.mp inf_le_right)
  have hQNcard : Nat.card (Q.subgroupOf N) = 4 := by
    rw [← card_map_of_injective N.subtype_injective, subgroupOf_map_subtype, hQN, inf_comm]
    rw [← card_map_of_injective Q.subtype_injective, subgroupOf_map_subtype] at hfixed
    exact hfixed
  have hQcard : Nat.card Q = 1024 := by
    obtain ⟨z, _, _, hcore, hc⟩ := ctx.involution_centralizer_core_eq_of_large_card hS
    change Nat.card (twoCoreIn ctx.second) = 1024
    rw [← hcore]
    exact (card_map_of_injective (centralizer ({z} : Set G)).subtype_injective).trans hc
  have hQindex : Q.relIndex M = 20 := by
    have hc := (Q.subgroupOf M).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (twoCoreIn_le M)).toEquiv, hQcard,
      ctx.second_card_of_large_card hS] at hc
    change Q.relIndex M = 20
    change 1024 * Q.relIndex M = 20480 at hc
    omega
  have hindex : Q.relIndex N ∣ 20 := by
    let _ : (Q.subgroupOf M).Normal := twoCoreIn_normal M
    have hd := relIndex_dvd_index_of_normal (Q.subgroupOf M) (N.subgroupOf M)
    rw [relIndex_subgroupOf hN] at hd
    exact hQindex ▸ hd
  have hNbound : Nat.card N ≤ 80 := by
    have hi := Nat.le_of_dvd (by decide : 0 < 20) hindex
    have hc := (Q.subgroupOf N).card_mul_index
    rw [hQNcard] at hc
    change 4 * Q.relIndex N = Nat.card N at hc
    omega
  have hsurj : Function.Surjective A.normalizerMonoidHom := by
    intro a
    obtain ⟨n, hn⟩ := ctx.five_local_automorphisms_surjective hS A hA hAM a
    exact ⟨n.1, hn⟩
  have hCindex : C.relIndex N = 4 := by
    have hi := index_ker A.normalizerMonoidHom
    rw [normalizerMonoidHom_ker, MonoidHom.range_eq_top.mpr hsurj, card_top] at hi
    let _ : IsCyclic A := isCyclic_of_prime_card hA
    rw [IsCyclic.card_mulAut, hA] at hi
    exact hi
  have hCbound : Nat.card C ≤ 20 := by
    have hc := (C.subgroupOf N).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer _)).toEquiv] at hc
    change Nat.card C * C.relIndex N = Nat.card N at hc
    rw [hCindex] at hc
    omega
  have h4 : 4 ∣ Nat.card C := by
    have hd := card_dvd_of_le (show C ⊓ Q ≤ C from inf_le_left)
    rw [← subgroupOf_map_subtype, card_map_of_injective Q.subtype_injective, hfixed] at hd
    exact hd
  have h5 : 5 ∣ Nat.card C := by
    let _ : IsCyclic A := isCyclic_of_prime_card hA
    have hAC : A ≤ C := by
      intro a ha b hb
      exact congrArg Subtype.val (mul_comm (⟨b, hb⟩ : A) ⟨a, ha⟩)
    exact hA ▸ card_dvd_of_le hAC
  have h20 : 20 ∣ Nat.card C := (show Nat.Coprime 4 5 by decide).mul_dvd_of_dvd_of_dvd h4 h5
  exact Nat.le_antisymm hCbound (Nat.le_of_dvd (Nat.card_pos) h20)
/-- Confinement applies to fixed core elements without containing the whole core. -/
public theorem LargeTerminalContext.fixed_core_le_second_centralizer_of_confinement
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (hN : normalizer (A : Set G) ≤ ctx.second) (y : G) :
    twoCoreIn (centralizer ({y} : Set G)) ⊓ centralizer (A : Set G) ≤
      ctx.second ⊓ centralizer (A : Set G) :=
  le_inf (inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans hN)) inf_le_right

/-- The actual centralizer core has at most four five-fixed elements. -/
public theorem LargeTerminalContext.fixed_centralizer_core_card_le_four
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (hfixed : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (y : G) (hy : y ∈ centralizer (A : Set G)) :
    let C := centralizer ({y} : Set G)
    Nat.card ((centralizer (A.subgroupOf C : Set C)).subgroupOf (pCore 2 C)) ≤ 4 := by
  let C := centralizer ({y} : Set G)
  let K := pCore 2 C
  let D := (centralizer (A.subgroupOf C : Set C)).subgroupOf K
  have hAC : A ≤ C := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hy a ha)
  let f : D →* centralizer (A : Set G) := {
    toFun := fun d => ⟨d.1.1.1, by
      intro a ha
      exact congrArg C.subtype (mem_centralizer_iff.mp d.property
        (⟨a, hAC ha⟩ : C) ha)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : centralizer (A : Set G) => (t : G)) hab
  have hd : Nat.card D ∣ 20 :=
    ctx.five_centralizer_card_twenty_of_confinement hS A hA hN hfixed ▸
      card_dvd_of_injective f hinj
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := C)).to_subgroup D |>.exists_card_eq
  have hnle : n ≤ 2 := by
    by_contra h
    have h8 : 8 ∣ 20 := (show 2 ^ 3 ∣ Nat.card D by
      rw [hn]
      exact pow_dvd_pow 2 (by omega)).trans hd
    norm_num at h8
  change Nat.card D ≤ 4
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hnle


/-- The putative factor of three supplies actual faithful semidirect automorphisms
of the full centralizer core, with a common fixed involution and at most four
five-fixed points. -/
public theorem LargeTerminalContext.exists_three_five_core_action_of_three_dvd
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (hfixed : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (y : G) (hy : y ∈ centralizer (A : Set G)) (hy2 : orderOf y = 2)
    (h3 : 3 ∣ Nat.card (centralizer ({y} : Set G))) :
    let C := centralizer ({y} : Set G)
    let K := pCore 2 C
    ∃ (H : Subgroup C) (_hAH : A.subgroupOf C ≤ H) (B : Subgroup H),
      IsElementaryAbelian 3 B ∧ B ≠ ⊥ ∧
      ∃ (φ : (A.subgroupOf C).subgroupOf H →* MulAut B)
        (ρ : SemidirectProduct B ((A.subgroupOf C).subgroupOf H) φ →* MulAut K)
        (k : K),
        Nat.card ((A.subgroupOf C).subgroupOf H) = 5 ∧
        Function.Injective ρ ∧
        (∀ b : B, (∀ a, φ a b = b) → b = 1) ∧
        orderOf k = 2 ∧ (∀ h, ρ h k = k) ∧
        Nat.card {x : K | ∀ a, ρ (SemidirectProduct.inr a) x = x} ≤ 4 := by
  let C := centralizer ({y} : Set G)
  let K := pCore 2 C
  have hAC : A ≤ C := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hy a ha)
  obtain ⟨PS, hPS⟩ := ctx.exists_sylow_five_of_normalizer_le_second hS A hA hN
  have hPC : (PS : Subgroup G) ≤ C := by rwa [hPS]
  let PC := PS.subtype hPC
  have hPCeq : (PC : Subgroup C) = A.subgroupOf C := by
    change (PS : Subgroup G).subgroupOf C = A.subgroupOf C
    rw [hPS]
  have hPCcard : Nat.card PC = 5 := by
    rw [hPCeq]
    exact (Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv).trans hA
  have hNmap : (normalizer (PC : Set C)).map C.subtype ≤ normalizer (A : Set G) := by
    change (normalizer ((PC : Subgroup C) : Set C)).map C.subtype ≤ _
    rw [hPCeq]
    have hh := le_normalizer_map (H := A.subgroupOf C) C.subtype
    rwa [map_subgroupOf_eq_of_le hAC] at hh
  have hno3 : ¬ 3 ∣ Nat.card (normalizer (PC : Set C)) := by
    intro h
    have hd := card_dvd_of_le (hNmap.trans hN)
    rw [card_map_of_injective C.subtype_injective, ctx.second_card_of_large_card hS] at hd
    have := h.trans hd
    norm_num at this
  obtain ⟨hsolv, hchar⟩ := ctx.localStructure C
    (Theory.GroupTheory.isTwoLocal_involution_centralizer hy2)
  have hall := exists_three_five_hall_normal_complement hsolv PC hPCcard hno3 h3
  rw [hPCeq] at hall
  obtain ⟨H, hAH, hHall, P, hPN, hP3, hPne, hcomp, hPA⟩ := hall
  let _ : P.Normal := hPN
  let AH := (A.subgroupOf C).subgroupOf H
  obtain ⟨B, hB3, hBne, φ, ι, hι, hιB, hιA, hfree⟩ :=
    exists_elementary_three_semidirect_embedding P AH hP3 hPne hcomp.disjoint hPA
  have hodd : Nat.Coprime 2 (Nat.card H) := Nat.prime_two.coprime_iff_not_dvd.mpr (by
    intro h2
    have hh := hHall.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ h2
    change (2 : ℕ) = 3 ∨ 2 = 5 at hh
    norm_num at hh)
  let ρH : H →* MulAut K := (MulAut.conjNormal : C →* MulAut K).comp H.subtype
  have hρH : Function.Injective ρH := odd_subgroup_conj_twoCore_injective hchar H hodd
  let ρ := ρH.comp ι
  have hyC : y ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hycent : (⟨y, hyC⟩ : C) ∈ center C := by
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (mem_centralizer_singleton_iff.mp c.property)
  obtain ⟨k, _, hk2, hk⟩ := exists_twoCore_central_involution hchar
    (⟨y, hyC⟩ : C) hycent (by simpa only [← orderOf_coe] using hy2)
  refine ⟨H, hAH, B, hB3, hBne, φ, ρ, k, ?_, hρH.comp hι, hfree, hk2,
    (fun h => hk (ι h)), ?_⟩
  · exact (Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv).trans
      ((Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv).trans hA)
  · let D := (centralizer (A.subgroupOf C : Set C)).subgroupOf K
    let F := {x : K | ∀ a, ρ (SemidirectProduct.inr a) x = x}
    let f : F → D := fun x => ⟨x.1, by
      intro a ha
      have he := x.property (⟨⟨a, hAH ha⟩, ha⟩ : AH)
      change ρH (ι (SemidirectProduct.inr _)) x.1 = x.1 at he
      rw [hιA] at he
      have he' := congrArg (fun q : K => (q : C)) he
      change a * (x.1 : C) * a⁻¹ = (x.1 : C) at he'
      exact mul_inv_eq_iff_eq_mul.mp he'⟩
    have hfinj : Function.Injective f := by
      intro a b hab
      exact Subtype.ext (congrArg (fun d : D => (d : K)) hab)
    exact (Nat.card_le_card_of_injective f hfinj).trans
      (ctx.fixed_centralizer_core_card_le_four hS A hA hN hfixed y hy)

/-- The actual core action excludes three from the centralizer order.
Only confinement and the four-element fixed subgroup are needed. -/
public theorem LargeTerminalContext.not_three_dvd_fixed_involution_centralizer_of_core_action
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (hfixed : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (y : G) (hy : y ∈ centralizer (A : Set G)) (hy2 : orderOf y = 2) :
    ¬ 3 ∣ Nat.card (centralizer ({y} : Set G)) := by
  intro h3
  obtain ⟨H, _, B, hB3, hBne, φ, ρ, k, hA5, hρ, hfree, hk2, hk, hsmall⟩ :=
    ctx.exists_three_five_core_action_of_three_dvd hS A hA hN hfixed y hy hy2 h3
  let C := centralizer ({y} : Set G)
  let K := pCore 2 C
  let AH := (A.subgroupOf C).subgroupOf H
  let J := SemidirectProduct B AH φ
  let _ : Finite J := Finite.of_equiv (B × AH) SemidirectProduct.equivProd.symm
  let _ : IsElementaryAbelian 3 B := hB3
  let _ : Nontrivial B := B.nontrivial_iff_ne_bot.mpr hBne
  let _ : MulDistribMulAction J K := MulDistribMulAction.compHom K ρ
  let _ : FaithfulSMul J K := ⟨by
    intro a b hab
    apply hρ
    exact DFunLike.ext _ _ hab⟩
  let L := (SemidirectProduct.inl : B →* J).range
  let T := (SemidirectProduct.inr : AH →* J).range
  obtain ⟨hLN, hL3, hLne, hT5, hLT, hLC⟩ :=
    three_five_semidirect_subgroup_data hA5 φ hfree
  let _ : L.Normal := hLN
  let _ : IsElementaryAbelian 3 L := hL3
  have hlarge : 8 ≤ Nat.card (FixedPoints.subgroup T K) :=
    ThreeFiveAction.eight_le_card_fixed pCore_isPGroup L T hLne hT5 hLT hLC k hk2 hk
  let F := {x : K | ∀ a, ρ (SemidirectProduct.inr a) x = x}
  let f : FixedPoints.subgroup T K → F := fun x =>
    ⟨x.1, fun a => x.property ⟨SemidirectProduct.inr a, ⟨a, rfl⟩⟩⟩
  have hinj : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x : F => (x : K)) hab)
  have hupper : Nat.card (FixedPoints.subgroup T K) ≤ 4 :=
    (Nat.card_le_card_of_injective f hinj).trans hsmall
  exact (by decide : ¬ (8 : ℕ) ≤ 4) (hlarge.trans hupper)


/-- The core-action exclusion of three also excludes fifteen. -/
public theorem LargeTerminalContext.not_fifteen_dvd_fixed_involution_centralizer_of_core_action
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (y : G) (hy : y ∈ centralizer (A : Set G)) (hy2 : orderOf y = 2) :
    ¬ 15 ∣ Nat.card (centralizer ({y} : Set G)) := by
  intro h15
  exact ctx.not_three_dvd_fixed_involution_centralizer_of_core_action
    hS A hA hN hcard y hy hy2 ((by decide : 3 ∣ 15).trans h15)

/-- The exact noncyclic four-fixed alternative has neither three nor fifteen
in its involution-centralizer order. The residual, noncyclicity and location
hypotheses are retained for the terminal application; the stronger core-action
exclusion above only needs confinement, the fixed cardinality and the involution. -/
public theorem LargeTerminalContext.noncyclic_four_fixed_odd_exclusion
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (_hAP : A ≤ ctx.second)
    (_hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (_hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (_hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (_hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (_hyR : y ∉ ctx.firstResidual)
    (hy2 : orderOf y = 2) :
    (¬ 3 ∣ Nat.card (centralizer ({y} : Set G))) ∧
      ¬ 15 ∣ Nat.card (centralizer ({y} : Set G)) :=
  ⟨ctx.not_three_dvd_fixed_involution_centralizer_of_core_action
      hS A hA hN hcard y hyA hy2,
    ctx.not_fifteen_dvd_fixed_involution_centralizer_of_core_action
      hS A hA hN hcard y hyA hy2⟩

end Stellmacher.Recognition
