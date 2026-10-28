module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Level3.Data
import Mathlib.Tactic.FinCases

/-!
# HS stabilizer level 3: kernel-checked transitions and index

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

theorem step3_0 : ∀ r, gen3 0 * rep3 r =
    rep3 (act3 0 r) * evalWord gen4 (factor3 0 r) :=
  step3_of_check 0 (by decide +kernel)

theorem step3_1 : ∀ r, gen3 1 * rep3 r =
    rep3 (act3 1 r) * evalWord gen4 (factor3 1 r) :=
  step3_of_check 1 (by decide +kernel)

theorem step3_2 : ∀ r, gen3 2 * rep3 r =
    rep3 (act3 2 r) * evalWord gen4 (factor3 2 r) :=
  step3_of_check 2 (by decide +kernel)

theorem step3_3 : ∀ r, gen3 3 * rep3 r =
    rep3 (act3 3 r) * evalWord gen4 (factor3 3 r) :=
  step3_of_check 3 (by decide +kernel)

theorem step3_4 : ∀ r, gen3 4 * rep3 r =
    rep3 (act3 4 r) * evalWord gen4 (factor3 4 r) :=
  step3_of_check 4 (by decide +kernel)

theorem step3_5 : ∀ r, gen3 5 * rep3 r =
    rep3 (act3 5 r) * evalWord gen4 (factor3 5 r) :=
  step3_of_check 5 (by decide +kernel)

theorem step3_6 : ∀ r, gen3 6 * rep3 r =
    rep3 (act3 6 r) * evalWord gen4 (factor3 6 r) :=
  step3_of_check 6 (by decide +kernel)

theorem step3_7 : ∀ r, gen3 7 * rep3 r =
    rep3 (act3 7 r) * evalWord gen4 (factor3 7 r) :=
  step3_of_check 7 (by decide +kernel)

theorem step3_8 : ∀ r, gen3 8 * rep3 r =
    rep3 (act3 8 r) * evalWord gen4 (factor3 8 r) :=
  step3_of_check 8 (by decide +kernel)

theorem step3_9 : ∀ r, gen3 9 * rep3 r =
    rep3 (act3 9 r) * evalWord gen4 (factor3 9 r) :=
  step3_of_check 9 (by decide +kernel)

theorem step3 (i : Fin 10) (r : Fin 20) :
    gen3 i * rep3 r = rep3 (act3 i r) * evalWord gen4 (factor3 i r) := by
  fin_cases i
  · exact step3_0 r
  · exact step3_1 r
  · exact step3_2 r
  · exact step3_3 r
  · exact step3_4 r
  · exact step3_5 r
  · exact step3_6 r
  · exact step3_7 r
  · exact step3_8 r
  · exact step3_9 r

theorem card3 : Nat.card H3 = 20 * Nat.card H4 :=
  wordSubgroup_card_eq_mul_next gen3 inv3 inv3_spec
    gen4 inv4 inv4_spec rep3 act3 factor3 14 point3 0
    rep3_mem H4_le rep3_base rep3_point point3_injective next3_fix step3

end Sporadic.LeechRelated.HS.OrderCertificate
