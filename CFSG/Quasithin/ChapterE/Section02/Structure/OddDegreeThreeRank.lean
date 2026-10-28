module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.SpecificGroups.OddThreeRank.Automorphisms

/-!
# The normal odd degree-three component in the source star quotient

A normal simple Sylow supplement in a core-free minimal parabolic has
trivial centralizer. Conjugation therefore embeds the full quotient in
the automorphism group of that same component. The proved automorphism
bounds for odd prime-field PSL_3 and PSU_3 give two-rank at most three.
The final theorem applies this argument to the literal original quotient
by the minimal-parabolic core, with no core-identification premise.

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

/-- The actual normal degree-three component embeds the source star group
in an automorphism group of two-rank at most three. -/
theorem source_coreFree_odd_degree_three_rank_le_three
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup K] (hna : ¬ IsMulCommutative K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL K 3 p ∨ ClassicalGroup.IsPSU K 3 p) :
    primeRank 2 H ≤ 3 := by
  apply (coreFree_normal_simple_rank_le_aut T hP hJ K hna hgen).trans
  rcases hm with hm | hm
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    rw [primeRank_congr 2 (MulAut.congr e)]
    exact Theory.SpecificGroups.OddThreeRank.psl3_automorphism_two_rank_le_three hp ho hcard
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_equiv K e.toEquiv
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      e.symm.isSimpleGroup
    rw [primeRank_congr 2 (MulAut.congr e)]
    exact Theory.SpecificGroups.OddThreeRank.psu3_automorphism_two_rank_le_three J hp ho hcard hconj

/-- The literal original minimal-parabolic quotient has two-rank at most
three whenever its generating normal component has an odd degree-three image. -/
theorem source_star_odd_degree_three_rank_le_three
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p ∨
      ClassicalGroup.IsPSU
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p) :
    primeRank 2 (H ⧸ ChapterB.minimalParabolicCore T hP) ≤ 3 := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let D := K.map q
  have hi := source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup D := hi.1
  let : D.Normal := hi.2.2.1
  exact source_coreFree_odd_degree_three_rank_le_three S
    (source_star_minimal_core_free T hP).1 (source_star_minimal_core_free T hP).2
    D hi.2.1 hi.2.2.2 hp ho hm

end CFSG.Quasithin.ChapterE.Structure
