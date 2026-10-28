module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Level5.Data
import Mathlib.Tactic.FinCases

/-!
# HS stabilizer level 5: kernel-checked transitions and index

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

theorem step5_0 : ∀ r, gen5 0 * rep5 r =
    rep5 (act5 0 r) * evalWord gen6 (factor5 0 r) :=
  step5_of_check 0 (by decide +kernel)

theorem step5_1 : ∀ r, gen5 1 * rep5 r =
    rep5 (act5 1 r) * evalWord gen6 (factor5 1 r) :=
  step5_of_check 1 (by decide +kernel)

theorem step5 (i : Fin 2) (r : Fin 3) :
    gen5 i * rep5 r = rep5 (act5 i r) * evalWord gen6 (factor5 i r) := by
  fin_cases i
  · exact step5_0 r
  · exact step5_1 r

theorem card5 : Nat.card H5 = 3 * Nat.card H6 :=
  wordSubgroup_card_eq_mul_next gen5 inv5 inv5_spec
    gen6 inv6 inv6_spec rep5 act5 factor5 3 point5 0
    rep5_mem H6_le rep5_base rep5_point point5_injective next5_fix step5

end Sporadic.LeechRelated.HS.OrderCertificate
