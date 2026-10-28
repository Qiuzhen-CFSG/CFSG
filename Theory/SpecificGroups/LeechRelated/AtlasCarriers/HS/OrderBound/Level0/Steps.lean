module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Level0.Data
import Mathlib.Tactic.FinCases

/-!
# HS stabilizer level 0: kernel-checked transitions and index

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

theorem step0_0 : ∀ r, gen0 0 * rep0 r =
    rep0 (act0 0 r) * evalWord gen1 (factor0 0 r) :=
  step0_of_check 0 (by decide +kernel)

theorem step0_1 : ∀ r, gen0 1 * rep0 r =
    rep0 (act0 1 r) * evalWord gen1 (factor0 1 r) :=
  step0_of_check 1 (by decide +kernel)

theorem step0_2 : ∀ r, gen0 2 * rep0 r =
    rep0 (act0 2 r) * evalWord gen1 (factor0 2 r) :=
  step0_of_check 2 (by decide +kernel)

theorem step0_3 : ∀ r, gen0 3 * rep0 r =
    rep0 (act0 3 r) * evalWord gen1 (factor0 3 r) :=
  step0_of_check 3 (by decide +kernel)

theorem step0_4 : ∀ r, gen0 4 * rep0 r =
    rep0 (act0 4 r) * evalWord gen1 (factor0 4 r) :=
  step0_of_check 4 (by decide +kernel)

theorem step0_5 : ∀ r, gen0 5 * rep0 r =
    rep0 (act0 5 r) * evalWord gen1 (factor0 5 r) :=
  step0_of_check 5 (by decide +kernel)

theorem step0_6 : ∀ r, gen0 6 * rep0 r =
    rep0 (act0 6 r) * evalWord gen1 (factor0 6 r) :=
  step0_of_check 6 (by decide +kernel)

theorem step0_7 : ∀ r, gen0 7 * rep0 r =
    rep0 (act0 7 r) * evalWord gen1 (factor0 7 r) :=
  step0_of_check 7 (by decide +kernel)

theorem step0_8 : ∀ r, gen0 8 * rep0 r =
    rep0 (act0 8 r) * evalWord gen1 (factor0 8 r) :=
  step0_of_check 8 (by decide +kernel)

theorem step0_9 : ∀ r, gen0 9 * rep0 r =
    rep0 (act0 9 r) * evalWord gen1 (factor0 9 r) :=
  step0_of_check 9 (by decide +kernel)

theorem step0_10 : ∀ r, gen0 10 * rep0 r =
    rep0 (act0 10 r) * evalWord gen1 (factor0 10 r) :=
  step0_of_check 10 (by decide +kernel)

theorem step0_11 : ∀ r, gen0 11 * rep0 r =
    rep0 (act0 11 r) * evalWord gen1 (factor0 11 r) :=
  step0_of_check 11 (by decide +kernel)

theorem step0_12 : ∀ r, gen0 12 * rep0 r =
    rep0 (act0 12 r) * evalWord gen1 (factor0 12 r) :=
  step0_of_check 12 (by decide +kernel)

theorem step0_13 : ∀ r, gen0 13 * rep0 r =
    rep0 (act0 13 r) * evalWord gen1 (factor0 13 r) :=
  step0_of_check 13 (by decide +kernel)

theorem step0_14 : ∀ r, gen0 14 * rep0 r =
    rep0 (act0 14 r) * evalWord gen1 (factor0 14 r) :=
  step0_of_check 14 (by decide +kernel)

theorem step0_15 : ∀ r, gen0 15 * rep0 r =
    rep0 (act0 15 r) * evalWord gen1 (factor0 15 r) :=
  step0_of_check 15 (by decide +kernel)

theorem step0_16 : ∀ r, gen0 16 * rep0 r =
    rep0 (act0 16 r) * evalWord gen1 (factor0 16 r) :=
  step0_of_check 16 (by decide +kernel)

theorem step0_17 : ∀ r, gen0 17 * rep0 r =
    rep0 (act0 17 r) * evalWord gen1 (factor0 17 r) :=
  step0_of_check 17 (by decide +kernel)

theorem step0_18 : ∀ r, gen0 18 * rep0 r =
    rep0 (act0 18 r) * evalWord gen1 (factor0 18 r) :=
  step0_of_check 18 (by decide +kernel)

theorem step0_19 : ∀ r, gen0 19 * rep0 r =
    rep0 (act0 19 r) * evalWord gen1 (factor0 19 r) :=
  step0_of_check 19 (by decide +kernel)

theorem step0 (i : Fin 20) (r : Fin 100) :
    gen0 i * rep0 r = rep0 (act0 i r) * evalWord gen1 (factor0 i r) := by
  fin_cases i
  · exact step0_0 r
  · exact step0_1 r
  · exact step0_2 r
  · exact step0_3 r
  · exact step0_4 r
  · exact step0_5 r
  · exact step0_6 r
  · exact step0_7 r
  · exact step0_8 r
  · exact step0_9 r
  · exact step0_10 r
  · exact step0_11 r
  · exact step0_12 r
  · exact step0_13 r
  · exact step0_14 r
  · exact step0_15 r
  · exact step0_16 r
  · exact step0_17 r
  · exact step0_18 r
  · exact step0_19 r

theorem card0 : Nat.card H0 = 100 * Nat.card H1 :=
  wordSubgroup_card_eq_mul_next gen0 inv0 inv0_spec
    gen1 inv1 inv1_spec rep0 act0 factor0 0 point0 0
    rep0_mem H1_le rep0_base rep0_point point0_injective next0_fix step0

end Sporadic.LeechRelated.HS.OrderCertificate
