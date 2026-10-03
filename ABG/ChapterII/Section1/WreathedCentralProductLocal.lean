module
public import ABG.ChapterII.Section1.WreathedCentralProductModel

/-!
# Local structure of the canonical quaternion central product

In a chosen wreathed presentation, the ambient centralizer of V is exactly
Z(S), and V/Z(V) is a Klein four group. These are the local inputs for
the outer automizer calculation in Alperin--Brauer--Gorenstein, Chapter II
Section 1 Proposition 2, article p.12, in
`refs/latex/alperin-brauer-gorenstein-pages/page-013.tex`.

A noncentral element centralizing V would have abelian centralizer, forcing
V itself to be abelian, contrary to its quaternion subgroup. Thus the
ambient centralizer is the center. The proved orders of V and its center
give quotient order four. A cyclic central quotient forces the whole group
to be abelian, so this quotient is noncyclic and has exponent two.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

/-- The canonical central product is centric in the wreathed group. -/
public theorem V_centralizer :
    Subgroup.centralizer (P.V : Set S) = Subgroup.center S := by
  apply le_antisymm ?_ (Subgroup.center_le_centralizer _)
  intro a ha
  by_contra hn
  apply P.V_noncommutative
  apply IsMulCommutative.of_comm
  intro b c
  apply Subtype.ext
  exact (P.commute_of_commute_noncentral hn
    (ha b b.property).symm (ha c c.property).symm).eq

/-- The central quotient of the canonical central product is Klein four. -/
public theorem V_quotient_isFourGroup : IsKleinFour (P.V ⧸ Subgroup.center P.V) := by
  have hcenter : Nat.card (Subgroup.center P.V) = 2 ^ n := by
    rw [← Subgroup.card_map_of_injective P.V.subtype_injective, P.V_center, P.card_center]
  have hcard : Nat.card (P.V ⧸ Subgroup.center P.V) = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P.V)
    rw [P.card_V, hcenter, pow_add] at h
    norm_num at h
    nlinarith [show 0 < 2 ^ n by positivity]
  refine ⟨hcard, ?_⟩
  apply (not_isCyclic_iff_exponent_eq_prime (by decide : Nat.Prime 2)
    (by simpa using hcard)).mp
  intro hcyc
  let := hcyc
  exact P.V_noncommutative (isMulCommutative_of_isCyclic_quotient_center_self P.V)

/-- The centralizer and central quotient used in the outer automizer calculation. -/
public theorem V_local_structure :
    Subgroup.centralizer (P.V : Set S) = Subgroup.center S ∧
      IsKleinFour (P.V ⧸ Subgroup.center P.V) :=
  ⟨P.V_centralizer, P.V_quotient_isFourGroup⟩
end ABG.Wreathed.Presentation
