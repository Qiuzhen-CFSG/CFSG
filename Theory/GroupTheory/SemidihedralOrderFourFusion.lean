module
public import Theory.GroupTheory.OrderFourTransfer
public import Theory.GroupTheory.SemidihedralOrderFourCharacter

/-!
# Ambient fusion of the semidihedral order-four generators

For a finite group with no normal subgroup of index two and the stated
semidihedral presentation of a Sylow two-subgroup, the quarter-order power
of the cyclic generator and the product of the two generators are conjugate
in the ambient group. All presentation and ambient hypotheses are explicit;
no automizer index or fusion classification is assumed.

The internal parity character from `Semidihedral.exists_order_four_character`
kills all elements whose square is one, and its order-four kernel elements
are internally conjugate to the quarter-order rotation. The product `a*b`
has order four. The transfer theorem `Sylow.exists_isConj_ker_of_order_four`
gives an ambient conjugate of this product in the character's kernel:
otherwise transfer would produce a forbidden normal index-two subgroup.
Transport the internal conjugacy along the Sylow inclusion and compose.

This proves the specified order-four fusion in Alperin--Brauer--Gorenstein,
Chapter II, Section 1, Proposition 1(i), printed pp.10--11 of
`refs/files/alperin-brauer-gorenstein.pdf`. It supplies the ambient input
used at printed p.90 before passing to an involution centralizer quotient.
The complete project import chain stays below the campaign layer.
-/

universe u

/-- The two specified order-four elements fuse in the ambient group when
there is no normal subgroup of index two. -/
public theorem semidihedral_order_four_generators_isConj
    {G : Type u} [Group G] [Finite G]
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (S : Sylow 2 G) (n : ℕ) (hn : 4 ≤ n)
    (hcard : Nat.card S = 2 ^ n) (a b : S)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set S) = ⊤) :
    IsConj (((a ^ (2 ^ (n - 3))) : S) : G) (((a * b) : S) : G) := by
  obtain ⟨hab, character, hinvol, hkernel⟩ :=
    Semidihedral.exists_order_four_character n hn hcard a b ha hb hconj hgen
  have htwo : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    simp [Nat.card_eq_fintype_card]
  obtain ⟨other, hfusion, hzero⟩ := S.exists_isConj_ker_of_order_four
    hno character htwo hinvol (a * b) hab
  have horder : orderOf other = 4 := by
    obtain ⟨conjugator, hconjugator⟩ := hfusion
    have heq := SemiconjBy.orderOf_eq (conjugator : G) hconjugator
    simpa only [Subgroup.orderOf_coe, hab] using heq.symm
  exact (hfusion.trans
    ((S : Subgroup G).subtype.map_isConj (hkernel other horder hzero))).symm
