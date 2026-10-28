module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Centralizer

/-!
# Reduction of the Bender Borel argument to solvable overgroups

The diagonal central involution supplies a nontrivial two-core in I T.
If every proper overgroup of T in I T is solvable, the survivor places
all of them in M. An escaping I therefore makes I T a member of H-star
in the original subgroup lattice. The Bender solvability input remains
an independent source obligation.

Source: Aschbacher--Smith 10.3.3, printed p.756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

theorem join_core_ne_bot (d : CentralizerData T D s) {I : Subgroup G}
    (hIC : I ≤ centralizer ({d.first * d.second} : Set G)) :
    (I ⊔ (T : Subgroup G)).pCoreIn 2 ≠ ⊥ := by
  let z := d.first * d.second
  let Y := I ⊔ (T : Subgroup G)
  let Q := zpowers z
  have hQ : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by
    simpa only [Q, Nat.card_zpowers, pow_one] using d.order)
  have hQY : Q ≤ Y := zpowers_le.mpr (mem_sup_right d.central.1)
  have hYQ : Y ≤ centralizer (Q : Set G) := by
    simpa only [Q, zpowers_eq_closure, centralizer_closure] using
      sup_le hIC d.sylow_le_centralizer
  have hcore := le_pCoreIn_of_normalizes hQ hQY
    (hYQ.trans (Subgroup.centralizer_le_normalizer _))
  intro hz
  have hQbot : Q = ⊥ := bot_unique (hcore.trans_eq hz)
  have hzone : z = 1 := mem_bot.mp (hQbot ▸ mem_zpowers z)
  have ho := d.order
  change orderOf z = 2 at ho
  simp [hzone] at ho

theorem hstar_of_solvable_proper_overgroups (d : CentralizerData T D s) {I : Subgroup G}
    (hIC : I ≤ centralizer ({d.first * d.second} : Set G))
    (hout : ¬ I ≤ D.maximalLocal)
    (hsol : ∀ P : Subgroup G, (T : Subgroup G) ≤ P →
      P < I ⊔ (T : Subgroup G) → Group.IsSolvable P) :
    I ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal := by
  refine ⟨⟨⟨join_core_ne_bot d hIC, fun _ hx => mem_sup_right hx⟩,
    fun h => hout (le_sup_left.trans h)⟩, ?_⟩
  intro P hP hPY
  by_contra hn
  let := hsol P hP.1.2 (lt_of_le_not_ge hPY hn)
  exact hP.2 (s.solvable_overgroups_le hP.1.2)

/-- It suffices to prove the genuine Bender Borel overgroup property.
The central involution supplies the two-core and solvable containment
supplies minimality outside M; neither is part of the premise. -/
theorem borelHStar_of_solvable_overgroups
    (hsol : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s) (I : Subgroup G),
      I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G)) →
      ClassificationModels.IsBenderModel (I ⧸ pCore 2 I) →
      ∀ P : Subgroup G, (T : Subgroup G) ≤ P →
        P < I ⊔ (T : Subgroup G) → Group.IsSolvable P) : BorelHStarAt T := by
  intro _ L D s d I hI hout hb
  exact hstar_of_solvable_proper_overgroups d hI.1 hout (hsol L D s d I hI hb)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
