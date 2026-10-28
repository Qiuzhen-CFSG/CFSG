module

public import CFSG.Quasithin.MainConverse.ReeSections.MaximalCover.Exhaustion.Branches
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents

/-!
# Assembly of the commuting-component branch

Carrier identification applied in both orders gives the two actual Suzuki
factors. The geometric index calculation makes their join normal in M with
quotient order two; multiplication identifies that join with their product.
This supplies exactly the Suzuki-wreath alternative required by the consumer.

The theorem is conditional on the two intrinsic Ree obligations. It does not
yet assert `commutingComponentMaximals` without premises. Final assembly stays
here, separately from the parent module assembling all exhaustion branches.

Source: Malle, J. Algebra 139 (1991), 52--69; the Sz(q)≀2 entry in the
unconditional list inside the proof of Theorem 5 of arXiv:0910.4758, pp.2--3.
-/

public section

namespace CFSG.Quasithin.MainConverse.ReeSections

open Subgroup ReeF4.MaximalSubgroups.CommutingComponents

/-- Assemble the direct-product and quotient clauses after discharging the
two explicit geometric obligations. This is not unconditional exhaustion. -/
theorem commutingComponentMaximals_of_carrierIdentification_of_pairIndex
    (hcarriers : ComponentCarrierIdentification) (hindex : IdentifiedPairIndex) :
    CommutingComponentMaximals := by
  intro m hm M hM hsolv hR L K hL hK hne hc
  obtain ⟨eL⟩ := hcarriers m hm M hM hsolv hR L K hL hK hne hc
  have hc' : ⁅K, L⁆ = ⊥ := by rw [commutator_comm K L, hc]
  obtain ⟨eK⟩ := hcarriers m hm M hM hsolv hR K L hK hL hne.symm hc'
  obtain ⟨hn, ⟨e⟩, hq⟩ := normal_suzuki_product_of_index_two hR hL hc eL eK
    (hindex m hm M hM hsolv hR L K hL hK hne hc eL eK)
  let := hn
  exact .suzukiWreath (L ⊔ K) e hq

end CFSG.Quasithin.MainConverse.ReeSections
