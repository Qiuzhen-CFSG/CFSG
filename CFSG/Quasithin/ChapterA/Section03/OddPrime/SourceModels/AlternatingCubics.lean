module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.Rank
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.SmallComponents
public import Theory.GroupTheory.CComponent.HexacodeTheta
public import Theory.GroupTheory.CComponent.TripleSevenTheta
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.Alternating.Aut
public import Theory.GroupAction.ComponentRankAction.OuterTwo
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models

/-!
# Cubic containment for the remaining alternating component models

In three-rank at most two, a centerless alternating component of degree at
least six contains every cubic element: its outer automorphisms form a
two-group, and the full-rank residual theorem applies. For either triple
cover, the center has order three. The central-product rank bound proves
normality, and the actual hexacode and triple-seven models have exponent
three on their Sylow three-subgroups. The inner-action calculation then
excludes an outside cubic element by adjoining it to an elementary nine.

These are the A.3.18 specializations consumed by the ordinary-component
branch of 12.4.8. All model, normality and cubic-containment assertions are
proved here or supplied by their concrete model theorems.
Source: Aschbacher–Smith A.3.18, pp.51–53, and 12.4.8, p.815.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.AlternatingCubics
open Chapter1.Section02.LocalModels
variable {H : Type*} [Group H] [Finite H] {K : Subgroup H}

private theorem cubic_mem_of_centerless (hK : IsComponent H K)
    (hc : center K = ⊥) (hr : 2 ≤ primeRank 3 K)
    (ho : IsPGroup 2 (MulAut.Outer K)) (hH : primeRank 3 H ≤ 2)
    {x : H} (hx : orderOf x = 3) : x ∈ K := by
  let e : (K ⧸ center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have he := (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual_of_outer_twoGroup
    hK (by rw [hc]; simp) hr hH e (by decide) ho).1
  rw [he]
  exact subset_closure hx

private theorem alternating_outer_two {n : ℕ} (hn : 6 ≤ n) :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin n))) := by
  by_cases hsix : n = 6
  · subst n
    exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let A := alternatingGroup (Fin n)
  have hcard : Nat.card (Equiv.Perm (Fin n) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  apply (IsPGroup.of_card hcard).of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ,rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n (by omega) hsix).surjective a
  exact ⟨QuotientGroup.mk' A σ,rfl⟩

/-- The alternating rank-two rows of A.3.18, on the literal ordinary component. -/
theorem cubic_mem_of_alternating_component (hK : IsComponent H K)
    {n : ℕ} (hn : 6 ≤ n) (hm : IsAlternating K n)
    (hH : primeRank 3 H ≤ 2) {x : H} (hx : orderOf x = 3) : x ∈ K := by
  obtain ⟨e⟩ := hm
  have hc : center K = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    have he : e z ∈ center (alternatingGroup (Fin n)) := (centerCongr e ⟨z,hz⟩).property
    rw [alternatingGroup.center_eq_bot (by simp; omega),mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hr : 2 ≤ primeRank 3 K := by
    rw [primeRank_congr 3 e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime n 3 Nat.prime_three (by decide)]
    omega
  have ho : IsPGroup 2 (MulAut.Outer K) :=
    (alternating_outer_two hn).of_equiv (MulAut.outerCongr e).symm
  exact cubic_mem_of_centerless hK hc hr ho hH hx

private theorem cubic_mem_of_cover_model
    {S : Type*} [Group S] [Finite S]
    (hK : IsComponent H K) (e : K ≃* S)
    (hc : Nat.card (center S) = 3) (hr : 2 ≤ primeRank 3 S)
    (hexp : ∀ z : S, z ^ 9 = 1 → z ^ 3 = 1)
    (ho : IsPGroup 2 (MulAut.Outer S)) (hH : primeRank 3 H ≤ 2)
    {x : H} (hx : orderOf x = 3) : x ∈ K := by
  have hz : Nat.card (center K) = 3 := (Nat.card_congr (centerCongr e).toEquiv).trans hc
  have hrK : 2 ≤ primeRank 3 K := by rwa [primeRank_congr 3 e]
  let : K.Normal := ChapterA.SQTKStructure.NonnormalOuterSource.component_normal_of_three_rank
    hH hK hz.le hrK
  apply HexacodeTheta.order_three_mem_of_normal K ?_ ?_
    (ho.of_equiv (MulAut.outerCongr e).symm) hrK hH
    (by simpa only [hx] using pow_orderOf_eq_one x)
  · intro z hzK
    have hh : (⟨z,hzK⟩ : center K) ^ Nat.card (center K) = 1 := pow_card_eq_one'
    rw [hz] at hh
    exact congrArg Subtype.val hh
  · intro z hz9
    apply e.injective
    simpa only [map_pow,map_one] using hexp (e z)
      (by simpa only [map_pow,map_one] using congrArg e hz9)

/-- Both exceptional triple covers are retained and handled by their actual
exponent-three models, not by a centerless replacement. -/
theorem cubic_mem_of_alternating_cover_component
    {J : Type*} [Group J] [Finite J] (hK : IsComponent H K) (eK : K ≃* J)
    (hm : IsAlternatingCover J 6 ∨ IsAlternatingCover J 7)
    (hH : primeRank 3 H ≤ 2) {x : H} (hx : orderOf x = 3) : x ∈ K := by
  let := hK.2
  let : IsQuasisimple J := IsQuasisimple.of_mulEquiv eK
  rcases hm with hm | hm
  · obtain ⟨_,⟨ez⟩,⟨eq⟩⟩ := hm
    have hc : Nat.card (center J) = 3 := (Nat.card_congr ez.toEquiv).trans (by simp)
    obtain ⟨e⟩ := GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode eq hc
    exact cubic_mem_of_cover_model hK (eK.trans e) Representation.Hexacode.even_center_card
      Representation.Hexacode.two_le_primeRank_even
      (fun _ h => HexacodeTheta.cube_eq_one_of_ninth h)
      Representation.Hexacode.even_outer_two hH hx
  · obtain ⟨_,⟨ez⟩,⟨eq⟩⟩ := hm
    have hc : Nat.card (center J) = 3 := (Nat.card_congr ez.toEquiv).trans (by simp)
    obtain ⟨e⟩ := GLS3.Chapter5.OddCentralCovers.triple_seven_equiv eq hc
    exact cubic_mem_of_cover_model hK (eK.trans e) GLS3.Chapter5.OddCentralCovers.tripleSeven_center_card
      GLS3.Chapter5.OddCentralCovers.tripleSeven_two_le_threeRank
      (fun _ h => GLS3.Chapter5.OddCentralCovers.tripleSeven_cube_eq_one_of_ninth h)
      GLS3.Chapter5.OddCentralCovers.tripleSeven_outer_two hH hx

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.AlternatingCubics
