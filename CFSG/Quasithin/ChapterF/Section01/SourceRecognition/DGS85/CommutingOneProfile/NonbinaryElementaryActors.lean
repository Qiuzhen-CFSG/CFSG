module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryApartmentActors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NonbinaryElementaryRoots

/-!
# Source-selected elementary apartments and their actual opposite-root actors

Choose the full original Cartan and the involutions constructed from the
nonbinary elementary Chapter 11 hypotheses. On their actual universal-tree
apartment, every pair of opposite four-path radicals covers the midpoint
SL₂ quotient. Its kernel is the actor's own two-core, with its inclusion
in the midpoint core and the original covering formula both retained.

This discharges the local generation and quotient input of DGS (14.3)(a)
for both endpoint orbits. It does not yet prove exchange or root signs.
The nonelementary catalogue exclusions and full original (11.7)--(11.8)
marked assembly remain with this source family.
Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175;
(14.1)--(14.3), pp.210--212.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S
variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (helem : ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))

include h hc hb hcomm helem


/-- The nonbinary original source constructs the apartment and every actual
opposite-root quotient, with no reflection or local-catalogue premise. -/
theorem original_elementary_nonbinary_actor_quotients
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2) :
    ∃ t : Bool → (A).Universal,
      (∀ i, t i • base T i = base T i) ∧
      (∀ i, t i • base T (!i) ≠ base T (!i)) ∧
      (∀ i, t i*t i=1) ∧
      (∀ i, t i∈normalizer (cartan (chosenCartans h) : Set (A).Universal)) ∧
    ∃ m, 0 < m ∧ ∃ (K : Bool → Type) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Finite (K i)) (_ : ∀ i, CharP (K i) 2),
      (∀ i, Nat.card (K i) = 2^(if i then m else 2*m)) ∧
    ∃ e : ∀ v : Vertex F,
      (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type),
    ∀ {a b} (p : (sourceGraph A).Walk a b) (_hp : p.IsPath) (hl : p.length=8),
      (∀ z∈p.support, z∈cartanApartment A (reflectionGroup (chosenCartans h) t)) →
      Function.Surjective (halfPathLinearMap h p 4 hl
        (e ((bOne_tree_cover h).vertex (p.getVert 4)))) ∧
      (halfPathLinearMap h p 4 hl (e ((bOne_tree_cover h).vertex (p.getVert 4)))).ker =
        pCore 2 (halfPathActor (X := (A).Universal) p 4) ∧
      (halfPathActor (X := (A).Universal) p 4).pCoreIn 2 ≤
        (MulAction.stabilizer (A).Universal (p.getVert 4)).pCoreIn 2 ∧
      (halfPathActor (X := (A).Universal) p 4).map (bOne_tree_map h) ⊔
        Q F ((bOne_tree_cover h).vertex (p.getVert 4)) =
          graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4)) ∧
      ∃ E : (halfPathActor (X := (A).Universal) p 4 ⧸
          pCore 2 (halfPathActor (X := (A).Universal) p 4)) ≃*
            SL(2,K ((bOne_tree_cover h).vertex (p.getVert 4)).type),
        ∀ x : halfPathActor (X := (A).Universal) p 4,
          E (QuotientGroup.mk' _ x) = e _ (QuotientGroup.mk' _ (halfPathLocalMap h p 4 hl x)) := by
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_nonbinary_tree_reflections h hc hb hcomm helem hnb (chosenCartans h)
  exact ⟨t,htfix,htmove,htsq,htnorm,
    original_elementary_apartment_actor_quotients h hc hb hcomm helem
      (chosenCartans h) t htfix htmove htsq htnorm⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
