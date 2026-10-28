module

public import Stellmacher.SectionOne.ExceptionalOddComplement
public import Stellmacher.SectionOne.ExceptionalProductSplit

/-!
# The exceptional full group is SL2(2) times SL2(2)

Under the Section 1 hypotheses, an elementary Sylow two-subgroup of order
four and an odd core of order nine force the entire ambient group to be
isomorphic to the product of two SL2(2) groups.

The odd-complement theorem proves that the odd core is elementary abelian
of exponent three and is a genuine complement to the given Sylow subgroup;
in particular no generation assumption is added here. The earlier
faithful-centralizer theorem supplies the trivial Sylow centralizer of
the odd core. The elementary nine-by-four product-splitting theorem then
constructs the two commuting SL2(2) factors and their full-group isomorphism.

This is the group-identification component of Stellmacher (1.6)(b),
journal p.18, following `refs/latex/stellmacher-n-group.tex`. It is
independent of the unrestricted source assertion about the offender ratio.
The order-nine and order-four inputs are proved separately in the bounded
exceptional action argument.
-/

namespace Stellmacher.SectionOne

universe u

/-- The exact Section 1 order-nine/order-four configuration identifies the
whole group with SL2(2) times SL2(2). -/
public theorem group_mulEquiv_sl2Two_prod_of_oddCore_card_nine
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS : IsElementaryAbelian 2 (S : Subgroup G))
    (hScard : Nat.card (S : Subgroup G) = 4)
    (hWcard : Nat.card (oddCore G) = 9) :
    Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  obtain ⟨hWelem, hcomp⟩ := oddCore_isComplement_sylow_of_card_nine h S hS hScard hWcard
  let _ : IsElementaryAbelian 3 (oddCore G) := hWelem
  let _ : IsElementaryAbelian 2 (S : Subgroup G) := hS
  let _ : (oddCore G).Normal := pPrimeCore_normal
  have hcent : (S : Subgroup G) ⊓ Subgroup.centralizer (oddCore G : Set G) = ⊥ :=
    RankOneThreeGroupAssembly.sylow_inf_centralizer_oddCore_eq_bot h S hS
      (IsElementaryAbelian.isPGroup 3 (oddCore G))
  exact mulEquiv_sl2Two_prod_of_elementary_nine_complement_four
    (oddCore G) S hWcard hScard hcomp hcent

end Stellmacher.SectionOne

