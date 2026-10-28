module
public import Theory.SpecificGroups.ClassicalOrthogonal.OddFiveComparison.Kernel
public import Theory.SpecificGroups.SymplecticFour.OddFrattiniSixteen
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.SmallFrattini
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.SmallDegree

/-!
# Excluding odd prime-field PSp₄ normalizer components

The actual exterior-square comparison embeds PSp₄ into the isometry group
of a five-dimensional quadratic space. Its faithful linear representation
contradicts the doubled odd ranks in the original module automizer after
the Sylow Frattini bound places the residual in the full covering component.

Source: the symplectic row of Aschbacher--Smith Theorem B in the 4.4.3
argument, printed p.622, as used in 10.2.3(2), printed p.745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The faithful five-dimensional exterior action excludes a placed odd PSp₄ component. -/
theorem source_nonnormal_oddNormalizer_no_placed_odd_symplectic_four_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G))) (hc : pCore 2 K = ⊥)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {r : ℕ} (ho : Odd r) (hm : ClassicalGroup.IsPSp (K ⧸ center K) 2 r) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have h2 : (2 : F) ≠ 0 :=
    Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card
      (k := 1) ho (by simpa only [pow_one] using hF)
  let a := ClassicalOrthogonal.OddFiveComparison.fromPSp h2
  let f := ((Theory.AlgebraicGroup.quadraticIsometrySubgroup
    (ClassicalOrthogonal.formB 2 F)).subtype.comp a).comp e.toMonoidHom
  let σ : Representation F (K ⧸ center K) (ClassicalOrthogonal.VectorB 2 F) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f
  have hf : Function.Injective σ :=
    LinearEquiv.toLinearMap_injective.comp
      (Subtype.val_injective.comp
        ((ClassicalOrthogonal.OddFiveComparison.fromPSp_injective h2).comp e.injective))
  apply source_nonnormal_oddNormalizer_no_placed_small_degree_component
    D hn B hBC hodd hBV K hc hFK h2 σ hf
  norm_num [ClassicalOrthogonal.VectorB,ClassicalOrthogonal.VectorD,
    ClassicalOrthogonal.Index,Module.finrank_prod,Module.finrank_pi]

/-- The native Sylow bound places the residual and excludes odd prime-field PSp₄. -/
theorem source_nonnormal_oddNormalizer_no_odd_symplectic_four_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hc : pCore 2 K = ⊥) {r : ℕ} [Fact r.Prime] (ho : Odd r)
    (hm : ClassicalGroup.IsPSp (K ⧸ center K) 2 r) : False := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  have hbound : ∃ P : Sylow 2 (K ⧸ center K), Nat.card (P ⧸ frattini P) ≤ 32 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    refine ⟨P,?_⟩
    rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup _))]
    exact (Theory.SpecificGroups.SymplecticFour.OddFrattiniSixteen.projective_frattini_card_le
      ho hF Q).trans (by decide)
  obtain ⟨P,hP⟩ := hbound
  exact source_nonnormal_oddNormalizer_no_placed_odd_symplectic_four_component D hn B hBC hodd hBV K hc
    (source_nonnormal_oddNormalizer_residual_le_of_smallFrattini
      D hn hp B hB hBC hBV hperm K hK hout P hP) ho hm

end CFSG.Quasithin.Chapter10
