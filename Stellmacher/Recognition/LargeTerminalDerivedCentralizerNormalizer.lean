module

public import Stellmacher.Recognition.LargeTerminalDerivedCentralizer
public import Stellmacher.Recognition.LargeTerminalInvolutionCentralizerQuotient
public import Stellmacher.Recognition.LargeTerminalFourFixedCoreFrattini
public import Theory.GroupTheory.ElementarySixtyFourSolvableCore
public import Theory.GroupTheory.PCoreSurjective

/-!
# Confinement of the derived-centralizer normalizer

Write Q for the second local core and W = C_Q(R') for the order-64
centralizer of the first residual's derived subgroup. The normalizer N of
W contains the prescribed Sylow subgroup, so its two-core T lies in Q,
and W ≤ T. The original order-five subgroup has exactly four fixed points
on Q. Orbit counting on W and T forces |T| to be 64 or 1024; hence T is
W or Q.

The center of Q is the distinguished order-two subgroup. Thus N_G(Q) is
exactly the second local group, and the T = Q branch gives confinement.
In the other branch the faithful Frattini action of N/T is a solvable
binary automorphism group on at most 64 elements, with trivial two-core
and order divisible by 320. The solvable binary automorphism bound excludes
this obstruction, so N_G(W) lies in the second local group.

No maximal-two-local assumption or fixed-four centralizer-core identification
is used. Source: Thompson VI, printed p.630, together with the native
Stellmacher (10.1) core and residual structure.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

private theorem fixed_card_mod_five
    {G : Type*} [Group G] [Finite G] (A U : Subgroup G)
    (hA : Nat.card A = 5) (hAU : A ≤ normalizer (U : Set G)) :
    Nat.card U % 5 = Nat.card ((centralizer (A : Set G)).subgroupOf U) % 5 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : MulDistribMulAction A U := conjMulDistribMulActionOfLeNormalizer A U hAU
  have heq : FixedPoints.subgroup A U = (centralizer (A : Set G)).subgroupOf U := by
    ext x
    constructor
    · intro hx
      apply mem_centralizer_iff.mpr
      intro a ha
      have hh := congrArg (fun y : U => (y : G)) (hx ⟨a, ha⟩)
      change a * (x : G) * a⁻¹ = (x : G) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hx a
      apply Subtype.ext
      change (a : G) * (x : G) * (a : G)⁻¹ = (x : G)
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hx a a.property)
  have hh := (IsPGroup.of_card (p := 5) (n := 1) (by simpa using hA)).card_modEq_card_fixedPoints U
  change Nat.card U % 5 = Nat.card (FixedPoints.subgroup A U) % 5 at hh
  rwa [heq] at hh

private theorem fixed_card_mono
    {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    {U V : Subgroup G} (hUV : U ≤ V) :
    Nat.card ((centralizer (A : Set G)).subgroupOf U) ≤
      Nat.card ((centralizer (A : Set G)).subgroupOf V) := by
  let f : ((centralizer (A : Set G)).subgroupOf U) →
      ((centralizer (A : Set G)).subgroupOf V) := fun x => ⟨⟨x.1, hUV x.1.2⟩, x.2⟩
  exact Nat.card_le_card_of_injective f (by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun x => ((x.1 : V) : G)) h)))

/-- The local core and the prescribed Sylow have the same central involution line. -/
public theorem LargeTerminalContext.second_core_center
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    CenterAmbient (twoCoreIn ctx.second) = omegaOneCenter (S : Subgroup G) := by
  let Q := twoCoreIn ctx.second
  let R := ctx.firstResidual
  have hRQ : R ≤ Q := by
    change ctx.firstResidual ≤ twoCoreIn ctx.second
    rw [ctx.derived_centralizer_supplement.1]
    exact le_sup_right
  have hSP : (S : Subgroup G) ≤ ctx.second :=
    ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
  have hQS : Q ≤ (S : Subgroup G) := by
    rintro x ⟨q, hq, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
      (S.subtype hSP) hq
  have hZQ : omegaOneCenter (S : Subgroup G) ≤ Q := by
    rw [← ctx.first_residual_center_eq_omegaOneCenter]
    exact (map_subtype_le _).trans hRQ
  rw [SectionEight.eight_six_centerAmbient_eq_inf_centralizer]
  apply le_antisymm
  · calc
      Q ⊓ centralizer (Q : Set G) ≤ Q ⊓ centralizer (R : Set G) :=
        inf_le_inf_left _ (centralizer_le hRQ)
      _ = CenterAmbient R := ctx.core_inf_residual_centralizer
      _ = omegaOneCenter (S : Subgroup G) := ctx.first_residual_center_eq_omegaOneCenter
  · exact le_inf hZQ ((omegaOneCenter_le_centerAmbient _).trans
      ((centerAmbient_le_centralizer _).trans (centralizer_le hQS)))

/-- The full normalizer of the local core is its known local group. -/
public theorem LargeTerminalContext.second_core_normalizer_eq_second
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    normalizer (twoCoreIn ctx.second : Set G) = ctx.second := by
  obtain ⟨z, hz, hgen, _, _, _⟩ := ctx.involution_centralizer_core
  apply le_antisymm
  · have h := normalizer_le_centralizer_of_characteristic_involution
      (twoCoreIn ctx.second) (center (twoCoreIn ctx.second)) z hz
      (ctx.second_core_center.trans hgen.symm)
    exact h.trans_eq (ctx.involution_centralizer_eq_second hS z hz hgen)
  · exact ctx.second.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image ctx.second (pCore 2 ctx.second))

/-- The normalizer two-core lies between the derived centralizer and the local core. -/
public theorem LargeTerminalContext.derived_centralizer_normalizer_core_bounds
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    let Q := twoCoreIn ctx.second
    let W := Q ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G)
    W ≤ twoCoreIn (normalizer (W : Set G)) ∧
      twoCoreIn (normalizer (W : Set G)) ≤ Q := by
  let Q := twoCoreIn ctx.second
  let W := Q ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G)
  let N := normalizer (W : Set G)
  let T := twoCoreIn N
  have hMN : ctx.second ≤ N := (ctx.derived_centralizer_normalizer_local_data hS).2.1
  have hSP : (S : Subgroup G) ≤ ctx.second :=
    ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
  have hSN : (S : Subgroup G) ≤ N := hSP.trans hMN
  have hTS : T ≤ (S : Subgroup G) := by
    rintro x ⟨t, ht, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := N)).le_sylow_of_normal (S.subtype hSN) ht
  have hTM : T ≤ ctx.second := hTS.trans hSP
  have hTnormal : (T.subgroupOf ctx.second).Normal :=
    normal_subgroupOf_of_le_normalizer (hMN.trans
      ((normal_subgroupOf_iff_le_normalizer (twoCoreIn_le N)).mp (twoCoreIn_normal N)))
  have hTtwo : IsPGroup 2 T := pCore_isPGroup.map N.subtype
  have hTQ : T ≤ Q := by
    rw [← map_subgroupOf_eq_of_le hTM]
    apply map_mono
    exact le_sSup ⟨hTnormal, hTtwo.comap_subtype⟩
  refine ⟨?_, hTQ⟩
  have hWtwo : IsPGroup 2 W := (pCore_isPGroup.map ctx.second.subtype).to_le inf_le_left
  have hWN : W ≤ N := W.le_normalizer
  have hWnormal : (W.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  change W ≤ (pCore 2 N).map N.subtype
  rw [← map_subgroupOf_eq_of_le hWN]
  exact map_mono (show W.subgroupOf N ≤ pCore 2 N from
    le_sSup ⟨hWnormal, hWtwo.comap_subtype⟩)

/-- Five-orbit counting excludes every intermediate normalizer two-core. -/
public theorem LargeTerminalContext.derived_centralizer_normalizer_core_dichotomy
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAM : A ≤ ctx.second)
    (hfixed : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4) :
    let Q := twoCoreIn ctx.second
    let W := Q ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G)
    twoCoreIn (normalizer (W : Set G)) = W ∨
      twoCoreIn (normalizer (W : Set G)) = Q := by
  let Q := twoCoreIn ctx.second
  let W := Q ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G)
  let N := normalizer (W : Set G)
  let T := twoCoreIn N
  obtain ⟨hWT, hTQ⟩ := ctx.derived_centralizer_normalizer_core_bounds hS
  change W ≤ T at hWT
  change T ≤ Q at hTQ
  obtain ⟨hWcard, hMN, _⟩ := ctx.derived_centralizer_normalizer_local_data hS
  change Nat.card W = 64 at hWcard
  have hAW : A ≤ normalizer (W : Set G) := hAM.trans hMN
  have hAT : A ≤ normalizer (T : Set G) := hAW.trans
    ((normal_subgroupOf_iff_le_normalizer (twoCoreIn_le N)).mp (twoCoreIn_normal N))
  have hFQ : Nat.card ((centralizer (A : Set G)).subgroupOf Q) = 4 := hfixed
  have hFWle := fixed_card_mono A (hWT.trans hTQ)
  have hFWmod := fixed_card_mod_five A W hA hAW
  rw [hWcard] at hFWmod
  rw [hFQ] at hFWle
  have hFW : Nat.card ((centralizer (A : Set G)).subgroupOf W) = 4 := by omega
  have hFTge := fixed_card_mono A hWT
  have hFTle := fixed_card_mono A hTQ
  rw [hFW] at hFTge
  rw [hFQ] at hFTle
  have hFT : Nat.card ((centralizer (A : Set G)).subgroupOf T) = 4 := by omega
  have hTmod := fixed_card_mod_five A T hA hAT
  rw [hFT] at hTmod
  have hQcard : Nat.card Q = 1024 := by
    obtain ⟨z, _, _, heq, hc⟩ := ctx.involution_centralizer_core_eq_of_large_card hS
    change Nat.card (twoCoreIn ctx.second) = 1024
    rw [← heq]
    exact (card_map_of_injective (centralizer ({z} : Set G)).subtype_injective).trans hc
  have hdiv : Nat.card T ∣ 2 ^ 10 := by
    have hd := card_dvd_of_le hTQ
    rw [hQcard] at hd
    exact hd
  have hTge := card_le_of_le hWT
  rw [hWcard] at hTge
  obtain ⟨n, hn, hTcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hcases : Nat.card T = 64 ∨ Nat.card T = 1024 := by
    interval_cases n <;> norm_num only [Nat.reducePow] at hTcard <;> omega
  rcases hcases with h64 | h1024
  · exact Or.inl (eq_of_le_of_card_ge hWT (by rw [hWcard, h64])).symm
  · exact Or.inr (eq_of_le_of_card_ge hTQ (by rw [hQcard, h1024]))

/-- Excluding two-core order 64 suffices for the requested confinement. -/
public theorem LargeTerminalContext.derived_centralizer_normalizer_le_second_of_core_card_ne
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (hcore : Nat.card (pCore 2 (normalizer
      (twoCoreIn ctx.second ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G) : Set G))) ≠ 64) :
    normalizer (twoCoreIn ctx.second ⊓
      centralizer (DerivedAmbient ctx.firstResidual : Set G) : Set G) ≤ ctx.second := by
  obtain ⟨A, hA, hAM, _, hfixed, _⟩ := ctx.exists_five_fixed_four_of_large_card hS
  let W := twoCoreIn ctx.second ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G)
  let N := normalizer (W : Set G)
  rcases ctx.derived_centralizer_normalizer_core_dichotomy hS A hA hAM hfixed with hW | hQ
  · have hc : Nat.card (twoCoreIn N) = 64 :=
      congrArg (fun U : Subgroup G => Nat.card U) hW |>.trans (ctx.derived_centralizer_card_and_index hS).1
    rw [show twoCoreIn N = (pCore 2 N).map N.subtype from rfl,
      card_map_of_injective N.subtype_injective] at hc
    exact (hcore hc).elim
  · have hN : N ≤ normalizer (twoCoreIn N : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (twoCoreIn_le N)).mp (twoCoreIn_normal N)
    rw [hQ, ctx.second_core_normalizer_eq_second hS] at hN
    exact hN

/-- The only remaining input is a small solvable binary automorphism bound.
This statement is a conditional assembly, not an unconditional confinement. -/
public theorem LargeTerminalContext.derived_centralizer_normalizer_le_second_of_binary_bound
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (hbound : ∀ (E : Type u) [Group E] [Finite E] [IsElementaryAbelian 2 E],
      Nat.card E ≤ 64 → ∀ B : Subgroup (MulAut E),
      Group.IsSolvable B → 320 ∣ Nat.card B → pCore 2 B ≠ ⊥) :
    normalizer (twoCoreIn ctx.second ⊓
      centralizer (DerivedAmbient ctx.firstResidual : Set G) : Set G) ≤ ctx.second := by
  apply ctx.derived_centralizer_normalizer_le_second_of_core_card_ne hS
  intro h64
  let W := twoCoreIn ctx.second ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G)
  let N := normalizer (W : Set G)
  obtain ⟨_, hMN, _, hsolv, hchar⟩ := ctx.derived_centralizer_normalizer_local_data hS
  let _ : Group.IsSolvable N := hsolv
  let T := pCore 2 N
  have hT : IsPGroup 2 T := pCore_isPGroup
  let _ : Fact (IsPGroup 2 T) := ⟨hT⟩
  let E := T ⧸ frattini T
  let _ : IsElementaryAbelian 2 E := isElementaryAbelian_quotient_frattini (p := 2)
  let action : N →* MulAut E := (quotientAut (frattini T)).comp MulAut.conjNormal
  have hker : action.ker = T := pCore_frattini_action_kernel 2 hchar
  have hcount : Nat.card T * Nat.card action.range = Nat.card N := by
    rw [← index_ker, hker]
    exact T.card_mul_index
  have hcore : pCore 2 action.range = ⊥ := by
    have hh := action.rangeRestrict.card_pCore_of_ker_isPGroup
      action.rangeRestrict_surjective (by
        rw [MonoidHom.ker_rangeRestrict, hker]
        exact hT)
    rw [MonoidHom.ker_rangeRestrict, hker] at hh
    change Nat.card T = Nat.card T * Nat.card (pCore 2 action.range) at hh
    have hTcard : Nat.card T = 64 := h64
    rw [hTcard] at hh
    exact Subgroup.card_eq_one.mp (by omega)
  have hE : Nat.card E ≤ 64 := by
    have hh := Nat.le_of_dvd (Nat.card_pos (α := T))
      (Subgroup.card_quotient_dvd_card (frattini T))
    exact hh.trans_eq h64
  have hdivN : 20480 ∣ Nat.card N :=
    ctx.second_card_of_large_card hS ▸ card_dvd_of_le hMN
  have hdiv : 320 ∣ Nat.card action.range := by
    obtain ⟨k, hk⟩ := hdivN
    have hTcard : Nat.card T = 64 := h64
    rw [hTcard, hk] at hcount
    exact ⟨k, by omega⟩
  exact hbound E hE action.range
    (Group.isSolvable_of_surjective action.rangeRestrict_surjective) hdiv hcore

/-- The order-64 centralizer of the first residual's derived subgroup has its
full normalizer in the second local group. -/
public theorem LargeTerminalContext.derived_centralizer_normalizer_le_second
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    normalizer (twoCoreIn ctx.second ⊓
      centralizer (DerivedAmbient ctx.firstResidual : Set G) : Set G) ≤ ctx.second := by
  apply ctx.derived_centralizer_normalizer_le_second_of_binary_bound hS
  intro E _ _ _ hE B hsolv hB
  let _ : Group.IsSolvable B := hsolv
  exact two_core_ne_bot_of_solvable_elementary_le_sixtyfour hE B hB

end Stellmacher.Recognition
