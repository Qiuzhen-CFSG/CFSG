module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowJanko
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# J₁ containing quotients in the chosen Chapter12 module

The original chosen-module input forces a prime actor on a J₁ containing
component to be cubic. If the selected right factor has A₅ quotient, its
actual cubic Hall intersection forces normalization, giving a contradiction.
This application includes parabolic right factors. With the original
H-component hypothesis, the existing non-A₅ argument and this A₅ argument
exclude J₁ for every selected component.

The literal quotients, relative normality, and smaller changed Sylow are
retained. Source: Aschbacher–Smith 5.2.2, pp.648–649, used in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D R K : Subgroup G} (C : ChosenModule T L V)
include C

/-- A J₁ container at the smaller changed Sylow forces p = 3. -/
theorem rankOne_prime_janko_container_prime
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (e : (K ⧸ pCore 2 K) ≃* Janko1.Model) : p = 3 :=
  d.source_overcomponent_janko_prime
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hz hSyl hRK hKX hK hKn e

/-- The A₅ right factor may be parabolic; it need not be a component of H. -/
theorem rankOne_prime_A5_right_not_janko_container
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) :=
  d.A5_right_not_janko_container
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hz hA5 hSyl hRK hKX hK hKn

/-- Every actual H-component excludes J₁, with no restriction on its quotient. -/
theorem rankOne_prime_component_not_janko_container
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) :=
  d.component_source_not_janko_container
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hz hC hSyl hRK hKX hK hKn

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
