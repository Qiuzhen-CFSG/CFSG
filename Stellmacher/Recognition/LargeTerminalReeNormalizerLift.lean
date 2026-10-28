module

public import Stellmacher.Recognition.LargeTerminalFiveNormalizerData
public import Stellmacher.Recognition.LargeTerminalReeRootSeed
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Stellmacher.Recognition.LargeTerminalReeSquaringFourthPower
public import Stellmacher.Recognition.LargeTerminalReeNonsplitExclusion

/-!
# The compatible Ree normalizer lift

The full local automizer supplies a squaring element. Taking its fifth
power removes its odd part; the local normalizer calculation bounds its
order by sixteen. The residual center improves this to order four or eight.
The fixed-root calculation proves compatibility, and the nonsplit first-core
obstruction excludes order eight using the neighboring parabolic geometry.
Thus there is an actual order-four lift centralizing the fixed subgroup.

The earlier conditional and order-alternative interfaces are preserved.
The final theorem discharges both local calculations without inferring
splitting from the quotient type.

Source: Thompson VI, pp.629–630, and Shinoda (1975), pp.81–83.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

/-- A local normalizer of A preserves its fixed subgroup in the second core.
Pointwise fixation is a stronger assertion supplied by the fixed-root calculation. -/
public theorem LargeTerminalContext.five_local_normalizer_preserves_fixed
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) :
    ctx.second ⊓ normalizer (A : Set G) ≤
      normalizer ((twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  have hQ : ctx.second ≤ normalizer (twoCoreIn ctx.second : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (twoCoreIn_le ctx.second)).mp
      (twoCoreIn_normal ctx.second)
  exact (inf_le_inf hQ (normalizer_le_normalizer_centralizer A)).trans
    inf_normalizer_le_normalizer_inf

/-- The remaining fourth-power and fixed-root calculations suffice for the
compatible order-four lift. This is conditional assembly, not the unconditional
normalizer-lifting theorem. -/
public theorem LargeTerminalContext.exists_compatible_squaring_element_of_calculations
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
    (hpower : ∀ b : G, b ∈ ctx.second → b ∈ normalizer (A : Set G) →
      b ^ 16 = 1 → (∀ c ∈ A, b * c * b⁻¹ = c ^ 2) → b ^ 4 = 1)
    (hroot : ∀ b t : G, b ∈ ctx.second → b ∈ normalizer (A : Set G) →
      b ^ 16 = 1 → (∀ c ∈ A, b * c * b⁻¹ = c ^ 2) →
      t ∈ twoCoreIn ctx.second → t ∈ centralizer (A : Set G) →
      t ∉ ctx.firstResidual → orderOf t = 4 → t ^ 2 = z →
      Commute b t) :
    ∃ a : centralizer ({z} : Set G), orderOf a = 4 ∧
      (∀ c ∈ A, (a : G) * c * (a : G)⁻¹ = c ^ 2) ∧
      (a : G) ∈ centralizer
        ((twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  obtain ⟨b, hbP, hbN, horder, hb⟩ :=
    ctx.exists_two_power_five_squaring_element hS A hA hAP hcard
  have hb16 : b ^ 16 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rcases horder with h | h | h <;> rw [h] <;> decide
  have hb4 : orderOf b = 4 :=
    orderOf_eq_four_of_squares_five A hA b hb (hpower b hbP hbN hb16 hb)
  obtain ⟨t, htQ, htA, htR, ht4, htsq, htgen⟩ :=
    ctx.exists_five_fixed_root_of_cyclic A hAN hcard hcyc hfixed z hz hgen
  have hbt := hroot b t hbP hbN hb16 hb htQ htA htR ht4 htsq
  have hbC : b ∈ centralizer ({z} : Set G) := by
    rw [ctx.involution_centralizer_eq_second hS z hz hgen]
    exact hbP
  refine ⟨⟨b, hbC⟩, ?_, hb, ?_⟩
  · rwa [← Subgroup.orderOf_coe]
  · change b ∈ centralizer
      ((twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Subgroup G) : Set G)
    rw [← htgen, zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr hbt.eq

/-- Fixed-root compatibility is automatic. Only the fourth-power calculation
remains as an input to this assembly theorem. -/
public theorem LargeTerminalContext.exists_compatible_squaring_element_of_fourth_power
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
    (hpower : ∀ b : G, b ∈ ctx.second → b ∈ normalizer (A : Set G) →
      b ^ 16 = 1 → (∀ c ∈ A, b * c * b⁻¹ = c ^ 2) → b ^ 4 = 1) :
    ∃ a : centralizer ({z} : Set G), orderOf a = 4 ∧
      (∀ c ∈ A, (a : G) * c * (a : G)⁻¹ = c ^ 2) ∧
      (a : G) ∈ centralizer
        ((twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  apply ctx.exists_compatible_squaring_element_of_calculations
    hS z hz hgen A hA hAP hAN hcard hcyc hfixed hpower
  intro b t hbP _ _ hb htQ htA _ ht4 _
  exact ctx.five_squaring_commutes_fixed_root hS z hz hgen A hA hAP hAN
    hcard hcyc hfixed b t hbP hb htQ htA ht4

/-- The earlier order-four-or-eight interface, retained for existing consumers.
The final theorem below strengthens it to order exactly four. -/
public theorem LargeTerminalContext.exists_compatible_squaring_element_four_or_eight
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
      center ctx.firstResidual) :
    ∃ a : centralizer ({z} : Set G), (orderOf a = 4 ∨ orderOf a = 8) ∧
      (∀ c ∈ A, (a : G) * c * (a : G)⁻¹ = c ^ 2) ∧
      (a : G) ∈ centralizer
        ((twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  obtain ⟨b, hbP, hbN, horder, hb⟩ :=
    ctx.exists_two_power_five_squaring_element hS A hA hAP hcard
  have hb16 : b ^ 16 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rcases horder with h | h | h <;> rw [h] <;> decide
  have hb48 := ctx.five_squaring_order_four_or_eight hS A hA hfixed b hbP hb16 hb
  obtain ⟨t, htQ, htA, _, ht4, _, htgen⟩ :=
    ctx.exists_five_fixed_root_of_cyclic A hAN hcard hcyc hfixed z hz hgen
  have hbt := ctx.five_squaring_commutes_fixed_root hS z hz hgen A hA hAP hAN
    hcard hcyc hfixed b t hbP hb htQ htA ht4
  have hbC : b ∈ centralizer ({z} : Set G) := by
    rw [ctx.involution_centralizer_eq_second hS z hz hgen]
    exact hbP
  refine ⟨⟨b, hbC⟩, ?_, hb, ?_⟩
  · simpa only [← Subgroup.orderOf_coe] using hb48
  · rw [← htgen, zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr hbt.eq

/-- The actual involution centralizer contains an order-four element inducing
squaring on the specified five-subgroup and centralizing its fixed subgroup
in the two-core. Both the fourth-power and fixed-root calculations are discharged. -/
public theorem LargeTerminalContext.exists_compatible_squaring_element
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
    : ∃ a : centralizer ({z} : Set G), orderOf a = 4 ∧
      (∀ c ∈ A, (a : G) * c * (a : G)⁻¹ = c ^ 2) ∧
      (a : G) ∈ centralizer
        ((twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  exact ctx.exists_compatible_squaring_element_of_fourth_power hS z hz hgen
    A hA hAP hAN hcard hcyc hfixed
    (ctx.five_squaring_fourth_power_eq_one hS z hz hgen A hA hAP hAN hcard hcyc hfixed)

end Stellmacher.Recognition
