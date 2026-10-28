module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryRank
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Two-rank of the two small normal-component star quotients

A normal simple Sylow supplement in a core-free minimal parabolic has
trivial centralizer, so the actual group embeds by conjugation in its
component automorphism group. The proved exceptional PSL3(2) action gives
two-rank two. For derived Sp4(2), the polar equivalence with A6 and the
checked Sylow holomorph calculation in Aut(A6) give two-rank at most three.
Thus every elementary subgroup of the literal source star quotient has
order at most eight. No diagram or automorphism-coverage premise is added.

Source: Aschbacher--Smith E.2.2 and 14.6.9, printed pp.215--216,1027--1028.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
variable {H : Type*} [Group H] [Finite H]

private theorem coreFree_normal_simple_rank_le_aut
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup K] (hna : ¬ IsMulCommutative K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    primeRank 2 H ≤ primeRank 2 (MulAut K) := by
  have htwo : pCore 2 H = ⊥ := le_bot_iff.mp
    ((ChapterB.minimalParabolicTwoCore_le_core T hP).trans hJ.le)
  have hc := centralizer_eq_bot_of_simple_two_quotient K hna
    (isPGroup_quotient_of_sup_eq_top K (T : Subgroup H) T.isPGroup' hgen) htwo
  exact Theory.GroupTheory.primeRank_le_of_injective 2 (MulAut.conjNormal (H := K))
    (MulAut.conjNormal_injective_of_centralizer_eq_bot K hc)

/-- The entire actual core-free group has two-rank at most three when its
normal generating simple component is one of the two surviving binary models. -/
theorem source_coreFree_small_binary_rank_le_three
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup K] (hna : ¬ IsMulCommutative K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL K 3 2 ∨
      Nonempty (K ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    primeRank 2 H ≤ 3 := by
  apply (coreFree_normal_simple_rank_le_aut T hP hJ K hna hgen).trans
  rcases hm with hm | hm
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    rw [primeRank_congr 2 (MulAut.congr e),
      Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two F hcard]
    decide
  · obtain ⟨e⟩ := hm
    let eA := e.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
    rw [primeRank_congr 2 (MulAut.congr eA)]
    apply (primeRank_le_iff_elementary_card_le _).mpr
    intro E hE
    let := hE
    exact AlternatingSix.ShadowLocal.elementary_card_le_eight E

/-- The normal small binary component bounds the two-rank of the literal
quotient by the original minimal-parabolic core. -/
theorem source_star_small_binary_rank_le_three
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 2 ∨
      Nonempty ((K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≃*
        commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    primeRank 2 (H ⧸ ChapterB.minimalParabolicCore T hP) ≤ 3 := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let D := K.map q
  have hi := source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup D := hi.1
  let : D.Normal := hi.2.2.1
  exact source_coreFree_small_binary_rank_le_three S
    (source_star_minimal_core_free T hP).1 (source_star_minimal_core_free T hP).2
    D hi.2.1 hi.2.2.2 hm

/-- Every literal elementary image in the small binary star quotient has
order at most eight; Sylow-normality is not needed for this stronger bound. -/
theorem source_star_small_binary_elementary_card_le_eight
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 2 ∨
      Nonempty ((K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≃*
        commutator (ClassicalGroup.PSp 2 (ZMod 2))))
    (V : Subgroup H) [IsElementaryAbelian 2 V] :
    Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≤ 8 := by
  let W := V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  exact (primeRank_le_iff_elementary_card_le _).mp
    (source_star_small_binary_rank_le_three T hP hs K hK hgen hm) W inferInstance

end CFSG.Quasithin.ChapterE.Structure
