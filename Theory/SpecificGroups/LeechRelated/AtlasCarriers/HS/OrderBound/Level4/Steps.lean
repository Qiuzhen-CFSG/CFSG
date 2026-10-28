module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Level4.Data
import Mathlib.Tactic.FinCases

/-!
# HS stabilizer level 4: kernel-checked transitions and index

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

theorem step4_0 : ∀ r, gen4 0 * rep4 r =
    rep4 (act4 0 r) * evalWord gen5 (factor4 0 r) :=
  step4_of_check 0 (by decide +kernel)

theorem step4_1 : ∀ r, gen4 1 * rep4 r =
    rep4 (act4 1 r) * evalWord gen5 (factor4 1 r) :=
  step4_of_check 1 (by decide +kernel)

theorem step4_2 : ∀ r, gen4 2 * rep4 r =
    rep4 (act4 2 r) * evalWord gen5 (factor4 2 r) :=
  step4_of_check 2 (by decide +kernel)

theorem step4_3 : ∀ r, gen4 3 * rep4 r =
    rep4 (act4 3 r) * evalWord gen5 (factor4 3 r) :=
  step4_of_check 3 (by decide +kernel)

theorem step4_4 : ∀ r, gen4 4 * rep4 r =
    rep4 (act4 4 r) * evalWord gen5 (factor4 4 r) :=
  step4_of_check 4 (by decide +kernel)

theorem step4_5 : ∀ r, gen4 5 * rep4 r =
    rep4 (act4 5 r) * evalWord gen5 (factor4 5 r) :=
  step4_of_check 5 (by decide +kernel)

theorem step4 (i : Fin 6) (r : Fin 16) :
    gen4 i * rep4 r = rep4 (act4 i r) * evalWord gen5 (factor4 i r) := by
  fin_cases i
  · exact step4_0 r
  · exact step4_1 r
  · exact step4_2 r
  · exact step4_3 r
  · exact step4_4 r
  · exact step4_5 r

theorem card4 : Nat.card H4 = 16 * Nat.card H5 :=
  wordSubgroup_card_eq_mul_next gen4 inv4 inv4_spec
    gen5 inv5 inv5_spec rep4 act4 factor4 1 point4 0
    rep4_mem H5_le rep4_base rep4_point point4_injective next4_fix step4

end Sporadic.LeechRelated.HS.OrderCertificate
