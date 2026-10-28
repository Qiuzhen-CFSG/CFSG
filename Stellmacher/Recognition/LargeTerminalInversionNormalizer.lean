module

public import Stellmacher.Recognition.LargeTerminalFiveNormalizerData
public import Stellmacher.Recognition.LargeTerminalReeFrameConstruction
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SpecificGroups.FiveFour

/-!
# Normalizing hypothetical local inversion

Keep the original terminal context. Sylow fusion moves a hypothetical inverter
into the five-normalizer. The order-twenty five-centralizer fixes the root, so
the root action depends only on the automorphism induced on the five-subgroup.
Its squaring generator must therefore invert the root. Taking the fifth power
produces an actual two-element while preserving both actions and normalization
of the residual subgroup. Its order divides sixteen; splitting remains open.

Source: the local automizer APIs of Thompson VI, pp.629–630, developed in
`LargeTerminalFiveNormalizerData` and `LargeTerminalReeFrameConstruction`.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u


/-- An inverter can be chosen in the actual local five-normalizer. This is
Sylow fusion applied to the five-subgroup inside the second parabolic. -/
public theorem LargeTerminalContext.exists_five_normalizing_inverter
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (t b : G) (htQ : t ∈ twoCoreIn ctx.second)
    (htA : t ∈ centralizer (A : Set G))
    (hbP : b ∈ ctx.second) (hinv : b * t * b⁻¹ = t⁻¹) :
    ∃ n : G, n ∈ ctx.second ∧ n ∈ normalizer (A : Set G) ∧
      n * t * n⁻¹ = t⁻¹ := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P := ctx.second
  let AP := A.subgroupOf P
  have hAPcard : Nat.card AP = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv).trans hA
  have hindex : AP.index = 4096 := by
    have h := AP.card_mul_index
    rw [hAPcard, ctx.second_card_of_large_card hS] at h
    omega
  let T : Sylow 5 P :=
    (IsPGroup.of_card (n := 1) (by simpa using hAPcard)).toSylow
      (by rw [hindex]; decide)
  let tP : P := ⟨t, twoCoreIn_le P htQ⟩
  let bP : P := ⟨b, hbP⟩
  have htC : tP ∈ centralizer (T : Set P) := by
    apply mem_centralizer_iff.mpr
    intro a ha
    apply Subtype.ext
    exact mem_centralizer_iff.mp htA a ha
  have hi : bP * tP * bP⁻¹ = tP⁻¹ := Subtype.ext hinv
  obtain ⟨n, hn, he⟩ := T.conj_eq_normalizer_conj_of_mem_centralizer
    tP bP⁻¹ htC (by simpa only [inv_inv, hi] using (centralizer (T : Set P)).inv_mem htC)
  have hnA : (n : G) ∈ normalizer (A : Set G) := by
    have h : n ∈ normalizer (A.subgroupOf P : Set P) := hn
    rw [← subgroupOf_normalizer_eq hAP] at h
    exact h
  refine ⟨(n : G)⁻¹, P.inv_mem n.property, (normalizer (A : Set G)).inv_mem hnA, ?_⟩
  have hh := congrArg (fun x : P => (x : G)) he
  simpa only [coe_mul, coe_inv, inv_inv, tP, bP, hinv] using hh.symm

private theorem local_centralizer_fixes_root
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (t : G) (htQ : t ∈ twoCoreIn ctx.second)
    (htA : t ∈ centralizer (A : Set G)) (ht4 : orderOf t = 4) :
    ctx.second ⊓ centralizer (A : Set G) ≤ centralizer ({t} : Set G) := by
  have hbound := ctx.five_local_centralizer_card_le_twenty hS A hA hAP hcard
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : IsCyclic A := isCyclic_of_prime_card hA
  have hTA : zpowers t ≤ centralizer (A : Set G) := zpowers_le.mpr htA
  have hAC : A ≤ ctx.second ⊓ centralizer (A : Set G) := le_inf hAP (le_centralizer A)
  have hTC : zpowers t ≤ ctx.second ⊓ centralizer (A : Set G) :=
    le_inf (zpowers_le.mpr (twoCoreIn_le ctx.second htQ)) hTA
  have hT : Nat.card (zpowers t) = 4 := (Nat.card_zpowers t).trans ht4
  have hd : Disjoint A (zpowers t) := disjoint_of_coprime_natCard (by rw [hA, hT]; decide)
  have hprod : Nat.card (A ⊔ zpowers t : Subgroup G) = 20 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A (zpowers t)
      (hTA.trans (Subgroup.centralizer_le_normalizer _)) hd, hA, hT]
  have heq : ctx.second ⊓ centralizer (A : Set G) = A ⊔ zpowers t :=
    (eq_of_le_of_card_ge (sup_le hAC hTC) (by omega)).symm
  rw [heq]
  exact (sup_le (le_centralizer_iff.mpr hTA) (le_centralizer _)).trans
    (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers t)))

private theorem root_action_eq_of_same_five_action
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (t : G) (htQ : t ∈ twoCoreIn ctx.second)
    (htA : t ∈ centralizer (A : Set G)) (ht4 : orderOf t = 4)
    (a b : G) (haP : a ∈ ctx.second) (hbP : b ∈ ctx.second)
    (hab : ∀ c ∈ A, a * c * a⁻¹ = b * c * b⁻¹) :
    a * t * a⁻¹ = b * t * b⁻¹ := by
  have hdA : b⁻¹ * a ∈ centralizer (A : Set G) := by
    apply mem_centralizer_iff.mpr
    intro c hc
    apply (mul_inv_eq_iff_eq_mul.mp ?_).symm
    calc
      (b⁻¹ * a) * c * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * c * a⁻¹) * b := by group
      _ = b⁻¹ * (b * c * b⁻¹) * b := by rw [hab c hc]
      _ = c := by group
  have hd := mem_centralizer_singleton_iff.mp
    (local_centralizer_fixes_root ctx hS A hA hAP hcard t htQ htA ht4
      ⟨ctx.second.mul_mem (ctx.second.inv_mem hbP) haP, hdA⟩)
  calc
    a * t * a⁻¹ = b * ((b⁻¹ * a) * t * (b⁻¹ * a)⁻¹) * b⁻¹ := by group
    _ = b * t * b⁻¹ := by rw [mul_inv_eq_iff_eq_mul.mpr hd]

private theorem five_action_is_power_of_squaring
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (hA : Nat.card A = 5)
    (s n : G) (hsN : s ∈ normalizer (A : Set G))
    (hnN : n ∈ normalizer (A : Set G))
    (hs : ∀ c ∈ A, s * c * s⁻¹ = c ^ 2) :
    ∃ k : ℕ, k < 4 ∧ ∀ c ∈ A,
      n * c * n⁻¹ = s ^ k * c * (s ^ k)⁻¹ := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : IsCyclic A := isCyclic_of_prime_card hA
  let eA : A ≃* FiveFour.Cyclic 5 := mulEquivOfPrimeCardEq hA (by simp [FiveFour.Cyclic])
  let α := A.normalizerMonoidHom ⟨s, hsN⟩
  have he : MulAut.congr eA α = FiveFour.doubling := by
    apply MulEquiv.ext
    intro c
    change eA (α (eA.symm c)) = FiveFour.doubling c
    have hh : α (eA.symm c) = (eA.symm c) ^ 2 :=
      Subtype.ext (hs (eA.symm c) (eA.symm c).property)
    rw [hh, map_pow, eA.apply_symm_apply]
    exact (by decide +kernel : ∀ c : FiveFour.Cyclic 5, c ^ 2 = FiveFour.doubling c) c
  have ho : orderOf α = 4 := by
    rw [← (MulAut.congr eA).orderOf_eq α, he]
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime_pow (p := 2) (n := 1)
      (by decide +kernel : FiveFour.doubling ^ 2 ≠ 1) FiveFour.doubling_four
  have htop : zpowers α = ⊤ := by
    apply eq_top_of_card_eq
    rw [Nat.card_zpowers, ho, IsCyclic.card_mulAut, hA]
    decide
  have hn : A.normalizerMonoidHom ⟨n, hnN⟩ ∈ zpowers α := htop ▸ mem_top _
  rw [mem_zpowers_iff_mem_range_orderOf, ho] at hn
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hn
  refine ⟨k, Finset.mem_range.mp hk, ?_⟩
  intro c hc
  have hh := congrArg (fun f : MulAut A => (f ⟨c, hc⟩ : G)) heq
  have hp : A.normalizerMonoidHom (⟨s, hsN⟩ ^ k) = α ^ k := map_pow _ _ _
  rw [← hp] at hh
  exact hh.symm

private theorem fifth_power_inverts
    {G : Type*} [Group G] (b t : G) (h : b * t * b⁻¹ = t⁻¹) :
    b ^ 5 * t * (b ^ 5)⁻¹ = t⁻¹ := by
  have hi : b * t⁻¹ * b⁻¹ = t := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv h
  have htwo : Commute (b ^ 2) t := by
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      b ^ 2 * t * (b ^ 2)⁻¹ = b * (b * t * b⁻¹) * b⁻¹ := by simp only [pow_two]; group
      _ = t := by rw [h, hi]
  have hfour : Commute (b ^ 4) t := by simpa only [← pow_mul] using htwo.pow_left 2
  calc
    b ^ 5 * t * (b ^ 5)⁻¹ = b * (b ^ 4 * t * (b ^ 4)⁻¹) * b⁻¹ := by
      rw [show (5 : ℕ) = 1 + 4 from rfl, pow_add, pow_one]; group
    _ = t⁻¹ := by rw [mul_inv_eq_iff_eq_mul.mpr hfour.eq, h]


/-- If local inversion occurs, an actual two-element squaring the five-subgroup
also inverts the root. Its order divides sixteen; no splitting is asserted. -/
public theorem LargeTerminalContext.exists_two_power_five_squaring_inverter
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (t b : G) (htQ : t ∈ twoCoreIn ctx.second) (ht4 : orderOf t = 4)
    (hgen : zpowers t = twoCoreIn ctx.second ⊓ centralizer (A : Set G))
    (hbP : b ∈ ctx.second) (hinv : b * t * b⁻¹ = t⁻¹) :
    ∃ s : G, s ∈ ctx.second ∧ s ∈ normalizer (A : Set G) ∧
      s ∈ normalizer (ctx.firstResidual : Set G) ∧
      s ∈ normalizer (twoCoreIn ctx.second : Set G) ∧
      s ^ 16 = 1 ∧ (∀ c ∈ A, s * c * s⁻¹ = c ^ 2) ∧
      s * t * s⁻¹ = t⁻¹ := by
  have htA : t ∈ centralizer (A : Set G) := (hgen.le (mem_zpowers t)).2
  obtain ⟨n, hnP, hnN, hnt⟩ := LargeTerminalContext.exists_five_normalizing_inverter ctx hS A hA hAP t b htQ htA hbP hinv
  obtain ⟨a, haP, haR, haQ, haN, ha, hat⟩ :=
    ctx.exists_five_squaring_root_symmetry hS A hA hAP t ht4 hgen
  have haInv : a * t * a⁻¹ = t⁻¹ := by
    rcases hat with hat | hat
    · obtain ⟨k, _, hk⟩ := five_action_is_power_of_squaring A hA a n haN hnN ha
      have hfix : Commute (a ^ k) t :=
        (show Commute a t from mul_inv_eq_iff_eq_mul.mp hat).pow_left k
      have heq := root_action_eq_of_same_five_action ctx hS A hA hAP hcard t htQ htA ht4
        n (a ^ k) hnP (pow_mem haP k) hk
      have hinv_eq : t⁻¹ = t := hnt.symm.trans (heq.trans (mul_inv_eq_iff_eq_mul.mpr hfix.eq))
      have ht2 : t ^ 2 = 1 := by
        rw [pow_two]
        nth_rw 1 [← hinv_eq]
        exact inv_mul_cancel t
      have hd := orderOf_dvd_of_pow_eq_one ht2
      rw [ht4] at hd
      norm_num at hd
    · exact hat
  let s := a ^ 5
  have hsP : s ∈ ctx.second := pow_mem haP 5
  have hsN : s ∈ normalizer (A : Set G) := pow_mem haN 5
  have h16 : s ^ 16 = 1 := by
    have h4096 : s ^ 4096 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨a, haP⟩ : ctx.second))
      rw [ctx.second_card_of_large_card hS] at hh
      change (a ^ 5) ^ 4096 = 1
      rw [← pow_mul]
      exact congrArg Subtype.val hh
    have h80 : orderOf s ∣ 80 := by
      have hh := orderOf_dvd_natCard
        (⟨s, hsP, hsN⟩ : (ctx.second ⊓ normalizer (A : Set G) : Subgroup G))
      rw [← Subgroup.orderOf_coe] at hh
      exact hh.trans (ctx.five_local_normalizer_card_dvd_eighty hS A hA hAP hcard)
    exact orderOf_dvd_iff_pow_eq_one.mp (show orderOf s ∣ 16 from
      Nat.dvd_gcd h80 (orderOf_dvd_of_pow_eq_one h4096))
  exact ⟨s, hsP, hsN, pow_mem haR 5, pow_mem haQ 5, h16, fifth_power_squares_five A hA a ha,
    fifth_power_inverts a t haInv⟩

end Stellmacher.Recognition
