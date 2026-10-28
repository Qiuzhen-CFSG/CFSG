module

public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# An elementary eight from commuting quotient lifts

In a group of order thirty-two, let a normal elementary eight D contain the
center of order two. Two commuting involutions that generate the group
together with D generate, together with the center, an elementary eight
supplementing D. The group orders force the two successive generators to
be external, so adjoining each one doubles the subgroup order.

This is the subgroup-assembly step of the central commutator supplement
argument for Stellmacher (8.6)(a2), Journal of Algebra 190 (1997), pp.41--42.
The existence of the commuting involutory lifts is a separate prerequisite.
-/

open scoped IsMulCommutative

namespace Subgroup

public theorem exists_elementary_eight_of_commuting_involutions
    {G : Type*} [Group G] [Finite G] (D : Subgroup G) [D.Normal]
    (hD : IsElementaryAbelian 2 D) (hDcard : Nat.card D = 8)
    (hGcard : Nat.card G = 32) (hcenterD : center G ≤ D)
    (hcenter : Nat.card (center G) = 2)
    (first second : G) (hfirst : first ^ 2 = 1) (hsecond : second ^ 2 = 1)
    (hcommute : Commute first second)
    (hgen : D ⊔ zpowers first ⊔ zpowers second = ⊤) :
    ∃ C : Subgroup G, IsElementaryAbelian 2 C ∧ Nat.card C = 8 ∧ C ⊔ D = ⊤ := by
  classical
  let := hD
  have hbound (element : G) (hsquare : element ^ 2 = 1) :
      Nat.card (D ⊔ zpowers element : Subgroup G) ≤ 16 := by
    by_cases hmem : element ∈ D
    · rw [sup_eq_left.mpr (zpowers_le.mpr hmem), hDcard]
      decide
    · rw [card_sup_zpowers_of_normalizing_involution D element hsquare hmem
        (by rw [normalizer_eq_top]; trivial), hDcard]
  have hfirstD : first ∉ D := by
    intro hmem
    have htop : D ⊔ zpowers second = ⊤ := by
      simpa only [sup_eq_left.mpr (zpowers_le.mpr hmem)] using hgen
    have hcard := hbound second hsecond
    rw [htop, card_top, hGcard] at hcard
    omega
  have hsecondDfirst : second ∉ D ⊔ zpowers first := by
    intro hmem
    have htop : D ⊔ zpowers first = ⊤ := by
      simpa only [sup_eq_left.mpr (zpowers_le.mpr hmem)] using hgen
    have hcard := hbound first hfirst
    rw [htop, card_top, hGcard] at hcard
    omega
  let base : Subgroup G := center G ⊔ zpowers first
  have hbaseLe : base ≤ D ⊔ zpowers first := sup_le_sup_right hcenterD _
  have hbaseCard : Nat.card base = 4 := by
    rw [card_sup_zpowers_of_normalizing_involution (center G) first hfirst
      (fun hmem => hfirstD (hcenterD hmem))
      (by rw [normalizer_eq_top]; trivial), hcenter]
  have hbaseCentral : base ≤ centralizer ({second} : Set G) := by
    apply sup_le (center_le_centralizer _)
    exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hcommute.eq)
  have hsecondCentral : second ∈ centralizer (base : Set G) := by
    intro element helement
    exact mem_centralizer_singleton_iff.mp (hbaseCentral helement)
  have hcard : Nat.card (base ⊔ zpowers second : Subgroup G) = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution base second hsecond
      (fun hmem => hsecondDfirst (hbaseLe hmem))
      (centralizer_le_normalizer _ hsecondCentral), hbaseCard]
  let : IsElementaryAbelian 2 (center G) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun element =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (element : G) (hcenterD element.property))) }
  let : IsElementaryAbelian 2 (zpowers first) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hfirst
  let : IsElementaryAbelian 2 (zpowers second) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hsecond
  let : IsElementaryAbelian 2 base :=
    IsElementaryAbelian.sup_of_le_centralizer (by rw [centralizer_center]; exact le_top)
  have helementary : IsElementaryAbelian 2 (base ⊔ zpowers second : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hsecondCentral)
  refine ⟨base ⊔ zpowers second, helementary, hcard, ?_⟩
  apply top_unique
  rw [← hgen]
  apply sup_le
  · exact sup_le le_sup_right (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
  · exact le_sup_of_le_left le_sup_right

end Subgroup

