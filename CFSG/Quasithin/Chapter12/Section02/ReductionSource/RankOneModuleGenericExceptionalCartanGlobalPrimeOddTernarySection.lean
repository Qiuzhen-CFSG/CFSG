module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeOddTernarySection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Chapter 12 restrictions on the actual A₅ ternary containing branch

At the smaller changed Sylow, the literal quotient image of the selected
right factor is SL₂(5) in every odd ternary container. The field parameter
and the original prime actor are both five. Applying the same calculation
to the existing source catalogue removes all other odd ternary parameters
and the cubic linear cover, while preserving the possible cubic unitary cover.
The selected right factor can be a parabolic local component; it is not
assumed to be an actual H-component.

Source: Aschbacher–Smith 5.2.2, pp.648–649, applied in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The source A₅ ternary restriction at the literal changed Sylow and
with both original Cartan markings. -/
theorem rankOne_cartan_source_A5_odd_ternary
    {T : Sylow 2 G} {L V H A B D R K : Subgroup G} {n p q : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (d : LocalData T L H B D R)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hs : SelectedSourceModels H R)
    (P : Sylow 2 (extension T L H B D R))
    (hP : (P : Subgroup (extension T L H B D R)).map
      (extension T L H B D R).subtype = normalizingSylow T R)
    (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R) (hRK : R ≤ K)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hq : q.Prime) (ho : Odd q)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 q ∨
      ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 q ∨
      Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 q ∨
      Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 q) :
    q = 5 ∧ p = 5 ∧ n ≠ 2 ∧
      let X := generated L H D R ⊔ normalizingSylow T R
      Chapter1.Section02.LocalModels.IsSL
        ((R.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) 2 5 := by
  exact d.changedSylow_A5_odd_ternary
    (C.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hgen hthree c hd hz hs P hP hKX hRK hK hA5 hq ho hm

/-- Reduce the genuine remaining catalogue on the same selected containing
component. The right A₅ quotient is the explicit branch assumption. -/
theorem rankOne_cartan_source_A5_remaining
    {T : Sylow 2 G} {L V H B D R K : Subgroup G} {n : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (d : LocalData T L H B D R)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (P : Sylow 2 (extension T L H B D R))
    (hP : (P : Subgroup (extension T L H B D R)).map
      (extension T L H B D R).subtype = normalizingSylow T R)
    (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R) (hRK : R ≤ K)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hm : RemainingSourceContainer (generated L H D R ⊔ normalizingSylow T R) K) :
    RemainingA5SourceContainer (generated L H D R ⊔ normalizingSylow T R) K := by
  have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R) :=
    Chapter1.IsSylowIn.restrict ⟨P,hP⟩ le_sup_right le_sup_left
  exact d.remaining_A5_source_container (C.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hSyl (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK hK hA5 hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
