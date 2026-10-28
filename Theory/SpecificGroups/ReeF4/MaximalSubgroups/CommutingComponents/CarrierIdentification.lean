module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification.Basic
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification.LeviQuotient

/-!
# Carrier identification from component placement and the seed projection

Conjugation first identifies the supplied component with the canonical fixed
middle-node Levi. The seed projection restricts to an isomorphism on that
Levi, because the seed is its product with the projection kernel and the
two factors meet trivially.

The assembly below is conditional. The geometric component-conjugacy theorem
and the Suzuki seed projection are still required before the unconditional
`componentCarrierIdentification` can be asserted. Its final assembly remains
in this module.

Source: the Suzuki-wreath entry in Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E; reproduced in the proof of Theorem 5 of
arXiv:0910.4758, pp.2–3. The seed projection uses the fixed B₂ Levi
construction of GLS3, §2.4, Table 2.4 type V.
-/

public section

namespace ReeF4.MaximalSubgroups.CommutingComponents

open Subgroup LargeLocalSeeds CarrierIdentification

/-- Conditional assembly with the geometric placement and the precise existing
seed-projection contract. Neither premise asserts carrier identification. -/
theorem componentCarrierIdentification_of_leviConjugacy_of_seedProjections
    (hconj : ComponentLeviConjugacy)
    (hprojections : ∀ m, 1 ≤ m →
      ∃ π : standardSeed (canonicalLocalBlockInput m) .suzuki →*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m,
        Function.Surjective π ∧ π.ker = seedRadical (canonicalLocalBlockInput m) .suzuki) :
    ComponentCarrierIdentification := by
  intro m hm M hM hsolv hR L K hL hK hne hc
  obtain ⟨g, hg⟩ := hconj m hm M hM hsolv hR L K hL hK hne hc
  obtain ⟨π, hπ, hker⟩ := hprojections m hm
  let e := (equivMapOfInjective L M.subtype M.subtype_injective).trans
    (((MulAut.conj g).subgroupMap (L.map M.subtype)).trans (MulEquiv.subgroupCongr hg))
  exact ⟨e.trans ((localLeviEquiv (canonicalLocalBlockInput m)).symm.trans
    (fixedLeviEquivOfProjection (canonicalLocalBlockInput m) .suzuki π hπ hker))⟩

end ReeF4.MaximalSubgroups.CommutingComponents
