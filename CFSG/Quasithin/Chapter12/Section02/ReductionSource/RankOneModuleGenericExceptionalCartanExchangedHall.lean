module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeExchangedHall
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The exchanged Hall plane for the chosen Chapter12 module

The source exchanged pair of PSL₂(4) components makes the prescribed right
Hall subgroup B elementary of order nine. An escaping cubic actor would
centralize B and join it to E₂₇ in the original two-local normalizer.
Consequently the actor is quintic, excluding the two alternating containing
components at the smaller changed Sylow. The selected right factor and the
source generating H-component remain distinct. The intrinsic A₅ quotient
recovers the required field marking and gives residual normalization in
the original degree-two branch from local Cartan control.

Source: Aschbacher–Smith 5.2.2 and 12.2.2, printed pp.648–649,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D : Subgroup G} (M : ChosenModule T L V)
include M

/-- The original Hall subgroup and its escaping actor in the exchanged four-field source row. -/
theorem rankOne_exchanged_four_hall_and_actor
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    (hm : ModelBorelPair ((normalizer (L : Set G)).subgroupOf H) C
      (BenderSuzuki.Converse.PBorel F)) :
    IsElementaryAbelian 3 B ∧ Nat.card B = 9 ∧ p = 5 := by
  have hi := M.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨hB,hBc⟩ := c.right_cubic_plane_of_exchanged_four hi hH hC hqs hc hF hm
  exact ⟨hB,hBc,c.exchanged_four_actor_prime hi hd hH hC hqs hc hF hm⟩

/-- Both alternating containing components are excluded, retaining the actual smaller Sylow. -/
theorem rankOne_prime_exchanged_four_not_alternating_container
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {R K : Subgroup G} (d : Prime.LocalData T L H B D R)
    (hz : (Prime.generated L H D R).pCoreIn 2 ≠ ⊥)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    (hm : ModelBorelPair ((normalizer (L : Set G)).subgroupOf H) C
      (BenderSuzuki.Converse.PBorel F))
    (hSyl : Chapter1.IsSylowIn 2 (Prime.normalizingSylow T R)
      (Prime.generated L H D R ⊔ Prime.normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ Prime.generated L H D R ⊔ Prime.normalizingSylow T R)
    (hK : (K.subgroupOf (Prime.generated L H D R ⊔ Prime.normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (Prime.generated L H D R ⊔ Prime.normalizingSylow T R)).Normal) :
    ¬ (Chapter1.Section02.LocalModels.IsAlternating (K ⧸ pCore 2 K) 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (K ⧸ pCore 2 K) 7) :=
  d.exchanged_four_not_alternating_container
    (M.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hz
    hC hqs hc hF hm hSyl hRK hKX hK hKn

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} (M : ChosenModule T L V)
include M

/-- Recover the actual Hall plane from the intrinsic A₅ component, with no independent field marking. -/
theorem rankOne_exchanged_A5_hall_plane
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hm : ExchangedModel ((normalizer (L : Set G)).subgroupOf H) C f)
    (hA5 : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4) :
    IsElementaryAbelian 3 B ∧ Nat.card B = 9 :=
  c.right_cubic_plane_of_exchanged_A5
    (M.rankOne_generic_input_of_many h hmany hn hpsl) hH hC hqs hc hm hA5

/-- Local control gives normalization in the original degree-two, exchanged-A₅ branch. -/
theorem rankOne_cartan_normalizes_of_exchanged_A5_degree_two
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {f : ℕ} (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hm : ExchangedModel ((normalizer (L : Set G)).subgroupOf H) C f)
    (hA5 : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4) :
    A ≤ normalizer (residual H : Set G) := by
  have hi := M.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl
  exact hi.cartan_normalizes_of_exchanged_A5_degree_two hH c hcontrol hC hqs hc hm hA5

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
