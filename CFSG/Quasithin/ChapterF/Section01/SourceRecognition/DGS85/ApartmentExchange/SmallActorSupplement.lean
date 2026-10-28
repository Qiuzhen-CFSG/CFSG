module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SmallActorExchange
public import Theory.GroupTheory.PCoreSupplementQuotient

/-!
# The literal small actor as a supplement to the endpoint core

DGS (14.3)(a) states that the join of the two half-path radicals supplements
the core of the local group. Restricting that local quotient gives the same
SL₂ quotient on the small actor and identifies its own two-core with the
literal intersection. Thus the core containment used by the natural cubic
exchange follows from supplementation, without endpoint normalization of
the small actor.

The original six-path consumer below uses this containment in the existing
braid calculation. Supplementation and the marked natural action on the
small core remain explicit source inputs; this does not prove the (14.9)
alternative or assert naturality of the full endpoint core.

Source: DGS, *Groups and Graphs* (1985), (14.3)(a), p.212;
(14.9)(c), pp.215--216; (14.12) and (14.17), pp.217--218,221.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.WeakBNPair.RegularTree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
variable {X V : Type*} [Group X] [MulAction X V]
variable {Γ : SimpleGraph V} {a b : V} {p : Γ.Walk a b} {n : ℕ}

/-- (14.3)(a) identifies the smaller actor's two-core with its actual
intersection with the local core. -/
theorem halfPathActor_core_eq_of_supplement (J : Subgroup X) [Finite J]
    (hAJ : halfPathActor (X := X) p n ≤ J)
    (hcover : halfPathActor (X := X) p n ⊔ J.pCoreIn 2 = J) :
    (halfPathActor (X := X) p n).pCoreIn 2 =
      halfPathActor (X := X) p n ⊓ J.pCoreIn 2 :=
  pCoreIn_eq_inf_of_supplement hAJ hcover

/-- The SL₂ marking of the smaller quotient is restriction of the given
local marking on every original element. No new quotient is chosen. -/
theorem halfPathActor_linear_quotient_of_supplement
    (J : Subgroup X) [Finite J]
    (hAJ : halfPathActor (X := X) p n ≤ J)
    (hcover : halfPathActor (X := X) p n ⊔ J.pCoreIn 2 = J)
    {F : Type*} [Field F] (e : (J ⧸ pCore 2 J) ≃* SL(2,F)) :
    ∃ f : (halfPathActor (X := X) p n ⧸
        pCore 2 (halfPathActor (X := X) p n)) ≃* SL(2,F),
      ∀ r : halfPathActor (X := X) p n,
        f (QuotientGroup.mk' (pCore 2 (halfPathActor (X := X) p n)) r) =
          e (QuotientGroup.mk' (pCore 2 J) (inclusion hAJ r)) := by
  obtain ⟨f,hf⟩ := exists_pCoreQuotientEquiv_of_supplement hAJ hcover
  exact ⟨f.trans e,fun r => congrArg e (hf r)⟩

namespace ReducedCartan
open RankTwoAmalgam Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original six-path exchange follows from the smaller natural actor
and the literal local supplementation in (14.3)(a). -/
theorem source_six_small_actor_exchange_of_supplement
    (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
    (d : SixPathSmallActorGeometry c)
    (hlocal : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length=12 →
      (∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection)) →
      ∀ g : (reducedAmalgam L S).Universal,
      (∀ k, 6≤k → k≤12 → g • p.getVert k=p.getVert k) → g • a≠a →
      (¬∃ z : (reducedAmalgam L S).Universal,
        (∀ k≤6, z • p.getVert k=p.getVert k) ∧ z • (g • a)=b) →
      ∃ J : Subgroup (reducedAmalgam L S).Universal, Finite J ∧
        halfPathActor (X := (reducedAmalgam L S).Universal) p 6 ≤ J ∧
        halfPathActor (X := (reducedAmalgam L S).Universal) p 6 ⊔ J.pCoreIn 2 = J ∧
        J.pCoreIn 2 ≤
          (MulAction.stabilizer (reducedAmalgam L S).Universal (p.getVert 6)).pCoreIn 2 ∧
        Nonempty (SmallActorPathCoordinates.{uF} p 6 (cartan c))) :
    ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S))
      (cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection)) 6 := by
  apply source_six_small_actor_exchange h c d
  intro a b p hp hl hT g hg hm hfail
  obtain ⟨J,hJ,hAJ,hcover,hcore,hcoords⟩ := hlocal p hp hl hT g hg hm hfail
  let := hJ
  refine ⟨?_,hcoords⟩
  rw [halfPathActor_core_eq_of_supplement J hAJ hcover]
  exact inf_le_right.trans hcore

end ReducedCartan

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
