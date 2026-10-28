module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Level2.Data
import Mathlib.Tactic.FinCases

/-!
# HS stabilizer level 2: kernel-checked transitions and index

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

theorem step2_0 : ∀ r, gen2 0 * rep2 r =
    rep2 (act2 0 r) * evalWord gen3 (factor2 0 r) :=
  step2_of_check 0 (by decide +kernel)

theorem step2_1 : ∀ r, gen2 1 * rep2 r =
    rep2 (act2 1 r) * evalWord gen3 (factor2 1 r) :=
  step2_of_check 1 (by decide +kernel)

theorem step2_2 : ∀ r, gen2 2 * rep2 r =
    rep2 (act2 2 r) * evalWord gen3 (factor2 2 r) :=
  step2_of_check 2 (by decide +kernel)

theorem step2_3 : ∀ r, gen2 3 * rep2 r =
    rep2 (act2 3 r) * evalWord gen3 (factor2 3 r) :=
  step2_of_check 3 (by decide +kernel)

theorem step2_4 : ∀ r, gen2 4 * rep2 r =
    rep2 (act2 4 r) * evalWord gen3 (factor2 4 r) :=
  step2_of_check 4 (by decide +kernel)

theorem step2_5 : ∀ r, gen2 5 * rep2 r =
    rep2 (act2 5 r) * evalWord gen3 (factor2 5 r) :=
  step2_of_check 5 (by decide +kernel)

theorem step2_6 : ∀ r, gen2 6 * rep2 r =
    rep2 (act2 6 r) * evalWord gen3 (factor2 6 r) :=
  step2_of_check 6 (by decide +kernel)

theorem step2_7 : ∀ r, gen2 7 * rep2 r =
    rep2 (act2 7 r) * evalWord gen3 (factor2 7 r) :=
  step2_of_check 7 (by decide +kernel)

theorem step2_8 : ∀ r, gen2 8 * rep2 r =
    rep2 (act2 8 r) * evalWord gen3 (factor2 8 r) :=
  step2_of_check 8 (by decide +kernel)

theorem step2_9 : ∀ r, gen2 9 * rep2 r =
    rep2 (act2 9 r) * evalWord gen3 (factor2 9 r) :=
  step2_of_check 9 (by decide +kernel)

theorem step2_10 : ∀ r, gen2 10 * rep2 r =
    rep2 (act2 10 r) * evalWord gen3 (factor2 10 r) :=
  step2_of_check 10 (by decide +kernel)

theorem step2_11 : ∀ r, gen2 11 * rep2 r =
    rep2 (act2 11 r) * evalWord gen3 (factor2 11 r) :=
  step2_of_check 11 (by decide +kernel)

theorem step2_12 : ∀ r, gen2 12 * rep2 r =
    rep2 (act2 12 r) * evalWord gen3 (factor2 12 r) :=
  step2_of_check 12 (by decide +kernel)

theorem step2_13 : ∀ r, gen2 13 * rep2 r =
    rep2 (act2 13 r) * evalWord gen3 (factor2 13 r) :=
  step2_of_check 13 (by decide +kernel)

theorem step2 (i : Fin 14) (r : Fin 21) :
    gen2 i * rep2 r = rep2 (act2 i r) * evalWord gen3 (factor2 i r) := by
  fin_cases i
  · exact step2_0 r
  · exact step2_1 r
  · exact step2_2 r
  · exact step2_3 r
  · exact step2_4 r
  · exact step2_5 r
  · exact step2_6 r
  · exact step2_7 r
  · exact step2_8 r
  · exact step2_9 r
  · exact step2_10 r
  · exact step2_11 r
  · exact step2_12 r
  · exact step2_13 r

theorem card2 : Nat.card H2 = 21 * Nat.card H3 :=
  wordSubgroup_card_eq_mul_next gen2 inv2 inv2_spec
    gen3 inv3 inv3_spec rep2 act2 factor2 2 point2 0
    rep2_mem H3_le rep2_base rep2_point point2_injective next2_fix step2

end Sporadic.LeechRelated.HS.OrderCertificate
