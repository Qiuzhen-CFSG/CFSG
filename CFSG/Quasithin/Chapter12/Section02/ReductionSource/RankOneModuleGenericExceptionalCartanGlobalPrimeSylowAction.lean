module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowComponents

/-!
# Faithful prime actions at the chosen module's smaller changed Sylow

The original chosen module supplies the generic Input. Apply the quotient
normalizer reflection to the same right factor and prime actor: the actor
retains order p, its conjugates of the quotient factor are distinct, and
its action on the proper containing quotient component is faithful.
The construction preserves the DT₀ action and the alternative in which
the changed subgroup is an ambient Sylow subgroup. The remaining model
sieve, larger-Sylow exclusion and final normalization stay with the owner
qt-d-1222-rankone-cartan-local-to-global.

Source: Aschbacher--Smith 5.2.2, pp.648--649, used in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D R : Subgroup G} (C : ChosenModule T L V)
include C

/-- Apply the literal quotient-action construction to the chosen generic module. -/
theorem rankOne_prime_changedSylow_quotient_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) :
    ∃ P : Sylow 2 (extension T L H B D R),
      let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
      Group.IsSolvable (D ⊔ normalizingSylow T R : Subgroup G) ∧
      normalizingSylow T R ≤ T₁ ∧
      T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
      ((T₁ = normalizingSylow T R ∧
        let X := generated L H D R ⊔ normalizingSylow T R
        let q := QuotientGroup.mk' (pCore 2 X)
        let Rbar := (R.subgroupOf X).map q
        let Dbar := (D.subgroupOf X).map q
        ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
          (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
          Rbar < (K.subgroupOf X).map q ∧
          ¬ ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) ∧
          Nat.card Dbar = p ∧ Disjoint Dbar (normalizer (Rbar : Set (X ⧸ pCore 2 X))) ∧
          Function.Injective (fun a : Dbar => Rbar.conjBy (a : X ⧸ pCore 2 X)) ∧
          ∃ hn : Dbar ≤ normalizer (((K.subgroupOf X).map q) : Set (X ⧸ pCore 2 X)),
            Function.Injective (((K.subgroupOf X).map q).normalizerMonoidHom.comp (inclusion hn))) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) :=
  d.changedSylow_prime_action
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
