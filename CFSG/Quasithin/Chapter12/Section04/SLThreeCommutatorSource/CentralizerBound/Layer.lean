module

public import CFSG.Quasithin.Chapter12.Section04.OddCoreCentralization
public import CFSG.Quasithin.ChapterI.Section03.GeneralTwoOrbit.Source

/-!
# The unconditional ordinary-layer step in 12.4.8

The actual centerless PSL₂ seed centralizes the embedded odd core by A.1.29.
The proved Sylow-fixer theorem and the genuine GLS II 5.22 orbit theorem
then put it in the embedded ordinary layer of C_G(U₀). Both universal
premises retained by the earlier conditional interface are discharged here.
No map into an individual covering component is asserted or needed.

Source: Aschbacher–Smith, Lemma 12.4.8, printed p.815, using I.3.1.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
universe u

/-- The original ordinary seed lies in E(C_G(U₀)), with its literal subtype
map. The seed is PSL₂(q), not SL₂(q); no S₂ or GLS 5.22 premise remains. -/
theorem seed_layer_of_fermatMersenne
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (U U₀ K : Subgroup G) [IsMulCommutative U]
    (hU : IsPGroup 2 U) (hU₀U : U₀ ≤ U) (hU₀ : U₀ ≠ ⊥)
    (hK : IsComponentIn K (centralizer (U : Set G)))
    {q : ℕ} (hq : IsFermatOrMersennePrime q) (hmodel : ClassicalGroup.IsPSL K 2 q) :
    IsSQTK KnownSimple.IsKnownSimple (centralizer (U₀ : Set G)) ∧
      K ≤ (componentLayer (centralizer (U₀ : Set G))).map
        (centralizer (U₀ : Set G)).subtype := by
  apply OddCoreCentralization.source_12_4_8_seed_layer_of_fermatMersenne
    ?_ ?_ hG U U₀ K hU hU₀U hU₀ hK hq hmodel
  · intro S _ _ _ P
    exact ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  · intro H _ _ _ P hP I hI
    exact ChapterI.GeneralTwoOrbit.Source.twoComponentOrbit P hP I hI

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
