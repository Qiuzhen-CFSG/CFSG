module
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.CosetIdentification.Words
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.CosetIdentification.WordGeometry.Enumeration

/-!
# Certified literal central-coset word geometry

The original three subgroup generators, 45 left representatives and ninety
inverse-action rows satisfy both finite group certificates from `Words`.
The eight subgroup words exhaust the original closure, and the 1080 products
`z^k r_i p` biject with the actual cover. Taking their literal left cosets gives
the required 135-point central transversal. The transporter equations prove
membership in that same subgroup, with the published phase and row tables.

These are unconditional group certificates. The coordinate construction and
filtration assembly remain in `CosetIdentification` and its consumers.

Source application: Aschbacher–Smith K.1.3, printed p.453 / PDF p.464,
citing GM02 Theorem 6.2 and Table 6.3. The original hexacode is due to
Gerald Höhn and the ATLAS contributors; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section

open Atlas.Codes
namespace Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification
open WordGeometry

/-- All ninety transporters belong to the closure of the original three words. -/
theorem wordTransitions : WordTransitions := by
  intro j i
  rw [transporter_eq]
  exact subgroupElement_mem _

/-- The 135 original central translates biject with the literal left-coset space. -/
theorem cosetTransversal : CosetTransversal := by
  constructor
  · intro a b hab
    have hm : (hexEvenZ ^ a.2.val * representative a.1)⁻¹ *
        (hexEvenZ ^ b.2.val * representative b.1) ∈ candidateSubgroup :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact hab)
    rw [candidate_eq_wordSubgroup] at hm
    obtain ⟨p,hp⟩ := hm
    have he : productElement (a,p) = productElement (b,0) := by
      change (hexEvenZ ^ a.2.val * representative a.1) * subgroupElement p =
        (hexEvenZ ^ b.2.val * representative b.1) * subgroupElement 0
      rw [subgroupElement_zero, mul_one, hp, mul_inv_cancel_left]
    exact congrArg Prod.fst (productElement_injective he)
  · intro q
    refine Quotient.inductionOn q ?_
    intro g
    obtain ⟨⟨a,p⟩, h⟩ := productElement_bijective.2 g
    refine ⟨a, ?_⟩
    rw [← h]
    change QuotientGroup.mk (hexEvenZ ^ a.2.val * representative a.1) =
      QuotientGroup.mk ((hexEvenZ ^ a.2.val * representative a.1) * subgroupElement p)
    exact (QuotientGroup.mk_mul_of_mem _ (subgroupElement_mem p)).symm

end Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification
