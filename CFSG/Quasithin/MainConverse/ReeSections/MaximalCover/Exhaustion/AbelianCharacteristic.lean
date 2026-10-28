module

public import CFSG.Quasithin.MainConverse.ReeSections.MaximalCover.Exhaustion.Branches
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic

/-!
# Prime reduction of the abelian-characteristic Ree branch

Choose a prime divisor of the nontrivial abelian characteristic subgroup and
take its first omega subgroup. At prime two a normalizer cover puts the maximal
subgroup in a proper full parabolic; maximality then gives an actual equivalence.
At an odd prime the intrinsic local calculation supplies the normal SU₃ layer
and its index-two quotient directly.

The two intrinsic calculations remain explicit inputs. This module does not
yet prove `abelianCharacteristicMaximals` or Malle exhaustion. Its unconditional
assembly must discharge both inputs in the actual exceptional fixed-point model.

Source: Malle, J. Algebra 139 (1991), 52–69; the unconditional list reproduced
inside the proof of Theorem 5 of arXiv:0910.4758, pp.2–3.
-/

public section

namespace CFSG.Quasithin.MainConverse.ReeSections

open Subgroup ReeF4.MaximalSubgroups.AbelianCharacteristic

/-- The finite-group reduction and the parabolic transport consume the two
independent local calculations. This is a conditional assembly theorem. -/
theorem abelianCharacteristicMaximals_of_local_analysis
    (h₂ : TwoLocalCover) (hodd : OddLocalStructure) : AbelianCharacteristicMaximals := by
  intro m hm M hM hnsol A hAc hAa hA
  let := hAc
  let := hAa
  obtain ⟨p, hp, E, _, hEc, hEe, hE⟩ :=
    exists_elementaryAbelian_characteristic_le A hA
  let := hEc
  by_cases hp₂ : p = 2
  · subst p
    obtain ⟨g, s, hP, hcover⟩ := h₂ m hm M hM hnsol E hEc hEe hE
    exact .parabolic_of_conjugate_normalizer_le M hM E g s hP hcover
  · obtain ⟨F, hF, hFinite, J, hcard, hconj, N, hN, ⟨e⟩, hindex⟩ :=
      hodd m hm M hM hnsol p hp hp₂ E hEc hEe hE
    let := hF
    let := hFinite
    let := hN
    exact .specialUnitary F J hcard hconj N e hindex

end CFSG.Quasithin.MainConverse.ReeSections
