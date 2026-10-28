module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Level1.Data
import Mathlib.Tactic.FinCases

/-!
# HS stabilizer level 1: kernel-checked transitions and index

Part of the order-divisibility certificate for the exact ATLAS HS carrier.
Source: GLS volume 3, Table 5.3m, printed p.274; ATLAS HSG1-p100B0.
The generator in `OrderBound/source/` supplies witnesses only. Every finite
identity is checked by Lean's kernel.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.OrderCertificate
open Theory.GroupTheory
set_option maxRecDepth 100000
set_option Elab.async false

theorem step1_0 : ∀ r, gen1 0 * rep1 r =
    rep1 (act1 0 r) * evalWord gen2 (factor1 0 r) :=
  step1_of_check 0 (by decide +kernel)

theorem step1_1 : ∀ r, gen1 1 * rep1 r =
    rep1 (act1 1 r) * evalWord gen2 (factor1 1 r) :=
  step1_of_check 1 (by decide +kernel)

theorem step1_2 : ∀ r, gen1 2 * rep1 r =
    rep1 (act1 2 r) * evalWord gen2 (factor1 2 r) :=
  step1_of_check 2 (by decide +kernel)

theorem step1_3 : ∀ r, gen1 3 * rep1 r =
    rep1 (act1 3 r) * evalWord gen2 (factor1 3 r) :=
  step1_of_check 3 (by decide +kernel)

theorem step1_4 : ∀ r, gen1 4 * rep1 r =
    rep1 (act1 4 r) * evalWord gen2 (factor1 4 r) :=
  step1_of_check 4 (by decide +kernel)

theorem step1_5 : ∀ r, gen1 5 * rep1 r =
    rep1 (act1 5 r) * evalWord gen2 (factor1 5 r) :=
  step1_of_check 5 (by decide +kernel)

theorem step1_6 : ∀ r, gen1 6 * rep1 r =
    rep1 (act1 6 r) * evalWord gen2 (factor1 6 r) :=
  step1_of_check 6 (by decide +kernel)

theorem step1_7 : ∀ r, gen1 7 * rep1 r =
    rep1 (act1 7 r) * evalWord gen2 (factor1 7 r) :=
  step1_of_check 7 (by decide +kernel)

theorem step1_8 : ∀ r, gen1 8 * rep1 r =
    rep1 (act1 8 r) * evalWord gen2 (factor1 8 r) :=
  step1_of_check 8 (by decide +kernel)

theorem step1_9 : ∀ r, gen1 9 * rep1 r =
    rep1 (act1 9 r) * evalWord gen2 (factor1 9 r) :=
  step1_of_check 9 (by decide +kernel)

theorem step1_10 : ∀ r, gen1 10 * rep1 r =
    rep1 (act1 10 r) * evalWord gen2 (factor1 10 r) :=
  step1_of_check 10 (by decide +kernel)

theorem step1_11 : ∀ r, gen1 11 * rep1 r =
    rep1 (act1 11 r) * evalWord gen2 (factor1 11 r) :=
  step1_of_check 11 (by decide +kernel)

theorem step1_12 : ∀ r, gen1 12 * rep1 r =
    rep1 (act1 12 r) * evalWord gen2 (factor1 12 r) :=
  step1_of_check 12 (by decide +kernel)

theorem step1_13 : ∀ r, gen1 13 * rep1 r =
    rep1 (act1 13 r) * evalWord gen2 (factor1 13 r) :=
  step1_of_check 13 (by decide +kernel)

theorem step1_14 : ∀ r, gen1 14 * rep1 r =
    rep1 (act1 14 r) * evalWord gen2 (factor1 14 r) :=
  step1_of_check 14 (by decide +kernel)

theorem step1_15 : ∀ r, gen1 15 * rep1 r =
    rep1 (act1 15 r) * evalWord gen2 (factor1 15 r) :=
  step1_of_check 15 (by decide +kernel)

theorem step1_16 : ∀ r, gen1 16 * rep1 r =
    rep1 (act1 16 r) * evalWord gen2 (factor1 16 r) :=
  step1_of_check 16 (by decide +kernel)

theorem step1 (i : Fin 17) (r : Fin 22) :
    gen1 i * rep1 r = rep1 (act1 i r) * evalWord gen2 (factor1 i r) := by
  fin_cases i
  · exact step1_0 r
  · exact step1_1 r
  · exact step1_2 r
  · exact step1_3 r
  · exact step1_4 r
  · exact step1_5 r
  · exact step1_6 r
  · exact step1_7 r
  · exact step1_8 r
  · exact step1_9 r
  · exact step1_10 r
  · exact step1_11 r
  · exact step1_12 r
  · exact step1_13 r
  · exact step1_14 r
  · exact step1_15 r
  · exact step1_16 r

theorem card1 : Nat.card H1 = 22 * Nat.card H2 :=
  wordSubgroup_card_eq_mul_next gen1 inv1 inv1_spec
    gen2 inv2 inv2_spec rep1 act1 factor1 4 point1 0
    rep1_mem H2_le rep1_base rep1_point point1_injective next1_fix step1

end Sporadic.LeechRelated.HS.OrderCertificate
