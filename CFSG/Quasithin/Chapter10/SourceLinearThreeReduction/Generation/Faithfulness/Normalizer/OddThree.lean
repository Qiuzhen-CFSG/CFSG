module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.SmallFrattini
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LowRank
public import Theory.Representation.DegreeThreeFrattiniLinear
public import Theory.SpecificGroups.OddClassicalSylowFrattini

/-!
# Odd ternary components with arbitrary finite field parameters

The degree-three natural action bounds a Sylow two-subgroup's Frattini
quotient by sixteen, including after passage to the projective quotient.
The whole original residual pair therefore acts innerly. Its nontrivial
perfectly moved elementary image has two-rank at least three, whereas the
actual odd ternary quotient has two-rank at most two. This excludes the
square-field rows as well as the prime-field rows, with no Schreier premise.

Source: Aschbacher--Smith 4.4.10--12 and 10.2.3(2), pp.621--623,745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04

private theorem odd_psl_three_frattini {F : Type*} [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) (P : Sylow 2 PSL(3,F)) :
    Nat.card (P ⧸ frattini P) ≤ 16 := by
  apply Theory.SpecificGroups.OddClassicalSylowFrattini.card_le_of_surjective
    (QuotientGroup.mk' (center SL(3,F))) (QuotientGroup.mk'_surjective _) ?_ P
  intro Q
  exact Representation.card_frattini_quotient_le_sixteen_of_injective_generalLinear_three
    Q.isPGroup' (Matrix.SpecialLinearGroup.toGL.comp (Q : Subgroup SL(3,F)).subtype)
    (Matrix.SpecialLinearGroup.toGL_injective.comp Subtype.val_injective) h2 (by decide)

private theorem odd_psu_three_frattini {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F) (h2 : (2 : F) ≠ 0)
    (P : Sylow 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (P ⧸ frattini P) ≤ 16 := by
  apply Theory.SpecificGroups.OddClassicalSylowFrattini.card_le_of_surjective
    (Matrix.ProjGenLinGroup.mk.subgroupMap J.specialSubgroup)
    (Matrix.ProjGenLinGroup.mk.subgroupMap_surjective J.specialSubgroup) ?_ P
  intro Q
  exact Representation.card_frattini_quotient_le_sixteen_of_injective_generalLinear_three
    Q.isPGroup' (J.specialSubgroup.subtype.comp (Q : Subgroup J.specialSubgroup).subtype)
    (Subtype.val_injective.comp Subtype.val_injective) h2 (by decide)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
  (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hBV : B ≤ centralizer (D.fullModule : Set G))
  (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
  (K : Subgroup (normalizer (B : Set G)))
  (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
  (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
include D hn hp hB hBC hBV hperm hK hout

/-- Every actual odd linear-three quotient is excluded, including square fields. -/
theorem source_nonnormal_oddNormalizer_no_odd_linear_three_component
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 q) : False := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  have hup := ChapterA.Section02.odd_psl_three_twoRank_le_two ho hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : Nat.card (P ⧸ frattini P) ≤ 32 := by
    rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup _))]
    exact (odd_psl_three_frattini
      (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho
        (by simpa only [pow_one] using hF)) P').trans (by decide)
  have hFK := source_nonnormal_oddNormalizer_residual_le_of_smallFrattini
    D hn hp B hB hBC hBV hperm K hK hout P hP
  have hlo := source_nonnormal_oddNormalizer_quotient_twoRank_ge_three D hn B hBC hodd hBV K hFK
  omega

/-- Every actual odd unitary-three quotient is excluded with its fixed-field convention. -/
theorem source_nonnormal_oddNormalizer_no_odd_unitary_three_component
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSU (K ⧸ center K) 3 q) : False := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  have hup := ChapterA.Section02.odd_psu_three_twoRank_le_two ho hm
  obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv (K ⧸ center K) e.toEquiv
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : Nat.card (P ⧸ frattini P) ≤ 32 := by
    rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup _))]
    exact (odd_psu_three_frattini J
      (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho hF) P').trans (by decide)
  have hFK := source_nonnormal_oddNormalizer_residual_le_of_smallFrattini
    D hn hp B hB hBC hBV hperm K hK hout P hP
  have hlo := source_nonnormal_oddNormalizer_quotient_twoRank_ge_three D hn B hBC hodd hBV K hFK
  omega

end CFSG.Quasithin.Chapter10
