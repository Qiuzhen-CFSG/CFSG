module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.LocalDichotomy.QuotientSetup
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.LocalDichotomy.ProductIdentification
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.LocalDichotomy.QuotientGap.Transfer

/-!
# Assembly of the quotient-centralizer gap

The genuine action on L/O₂(L) is an outer involution. With pointwise fixation
of Z(L), the geometric commuting-conjugate equality gives an index-two image
of C_L(r), a nonperfect full fixed subgroup, and a missing involution.
`Transfer` also proves the fusion restriction in the actual H/K.

The covering-center premise is still an obligation, separate from the given
geometric inputs. The conditional assembly below does not assert that the
source quotient step has been completed without that premise.

Source: Aschbacher–Smith, proof of 16.4.9(2), printed p.1190.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy.QuotientGap
open ComponentTransfer.Intrinsic
variable {G : Type*} [Group G] [Finite G] {𝒦 : GroupClass}
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The quotient-centralizer conclusions, conditional on the remaining
pointwise fixation of the covering center. -/
theorem quotient_transfer_of_center_fixed (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) (hr2 : orderOf r = 2)
    (hn : r ∈ normalizer (L : Set G)) (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hzL : z ∈ L)
    (hgeom : {s : G | (∃ l ∈ L, MulAut.conj l r = s) ∧ Commute r s} = {r, r * z})
    (hfix : center L ≤ (action hn).fixedSubgroup)
    (q : L ⧸ pCore 2 L) (hq2 : orderOf (quotientAction hn q * q⁻¹) = 2)
    (hqfix : quotientAction hn (quotientAction hn q * q⁻¹) = quotientAction hn q * q⁻¹) :
    orderOf (quotientAction hn) = 2 ∧
      (¬ ∃ x : L ⧸ pCore 2 L, quotientAction hn = MulAut.conj x) ∧
      (imageInFixed hn).index = 2 ∧ ¬ Group.IsPerfect (quotientFixed hn) ∧
      ∃ v : quotientFixed hn, orderOf v = 2 ∧ v ∉ imageInFixed hn := by
  have hi := imageInFixed_index_two_of_center_fixed hG h hr2 hn hzL hgeom hfix
  exact ⟨quotientAction_order_two hG h hr2 hn hout, quotientAction_outer hG h hn hout,
    hi, quotientFixed_not_perfect hn hi,
    exists_involution_outside_image_of_center_fixed hG h hr2 hn hzL hgeom hfix q hq2 hqfix⟩

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy.QuotientGap
