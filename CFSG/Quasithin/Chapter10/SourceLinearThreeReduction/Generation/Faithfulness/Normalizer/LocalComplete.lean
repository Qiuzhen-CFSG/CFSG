module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalCatalogue

/-!
# The nonnormal normalizer bound from local fixation

Covering uniqueness disposes of a nontrivial two-core. An escaping
normalizer otherwise has an ordinary component moved by the local module.
The original local normality argument and the full model exclusion give
a contradiction. Fixation is required only on this nonzero L₀T-invariant
fully moved submodule, not on the whole M-orbit.

Source: Aschbacher--Smith 4.4.3 and 4.4.14, pp.619--625, as used in 10.2.3(2).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Local fixation suffices for the entire ambient normalizer bound. -/
theorem source_local_oddPrimeActor_normalizer
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
    (hVX : V = ⁅V,localOrbit T L⁆)
    (hNV : localJoin T L ≤ normalizer (V : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) [IsMulCommutative A] (hAne : A ≠ ⊥) (hA : IsPGroup p A)
    (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hAV : A ≤ centralizer (V : Set G))
    (hAT : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G)) :
    normalizer (A : Set G) ≤ D.maximalLocal := by
  by_contra hout
  obtain ⟨hcore,K,hK,_,houtK,hKcore,hmodel,hFK,_⟩ :=
    source_local_oddPrimeActor_moved_component D hn V hVV hne hVX hNV
      hp A hAne hA hAC hAV hAT hout
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := hA.exists_card_eq
    rw [he]
    exact hp.pow
  let : K.Normal := source_local_oddActor_component_normal D V hVV hne hVX hNV
    A hAne hAC hodd hAV hcore K hK houtK hFK
  exact LocalFixed.source_no_theoremB_component D hn V hVV hne hVX hNV
    hp A hA hAC hAV hAT K hK houtK hKcore hmodel

end CFSG.Quasithin.Chapter10
