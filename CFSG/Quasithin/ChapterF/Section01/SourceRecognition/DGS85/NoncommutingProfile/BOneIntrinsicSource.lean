module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneTreeSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalActorApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.BOneBorelSource

/-!
# The intrinsic characteristic-two b=1 source profile

Start with an arbitrary noncommuting critical pair in the original F.1.11
reduced graph. The earlier Chapter 7 construction supplies both natural
SL₂ actions, including their quotient maps and full actor markings. The
source actor identities then discharge the normalization hypotheses of the
Chapter 10 order and regular-path calculations.

The two calculations use the same actions. Their center orders synchronize
the alternatives: the trivial centers give core orders q², full Borel core
order q³ and (r,s)=(3,4); otherwise the centers have order q, the cores have
order q³, the full Borel core has order q⁴ and (r,s)=(4,5). Both fields have
the same even order. Natural coordinates retain the actual conjugation on
both original full cores. The original S is not identified with O₂(B).

The final consumer transfers the four- or five-path profile through the
same marked universal cover used by Chapter 14, with both endpoint maps
and the whole Borel inherited from `bOne_tree_cover`. No actor catalogue,
natural-action witness, nonsolvability or path conclusion remains an input.
The b=2 branches and final classification assembly are separate obligations.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(7.1), printed pp.126--127; (10.5), pp.156--157; source path conventions
pp.60,73--74 and the reduction pp.95--96. AS F.1.9--F.1.11, pp.261--263.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open Theory.GroupTheory.WeakBNPair.RegularTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open DGS85.Reduction Noncommuting
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local instance bOneIntrinsicAlgebra {k : Type*} [Field k] [CharP k 2] :
    Algebra (ZMod 2) k := ZMod.algebra k 2

/-- All clauses of the characteristic-two b=1 profile on the original cores
and full Borel core, with both marked natural actions constructed internally. -/
theorem original_bOne_complete_profile
    (h : HypothesisF11 L S) {v w : Vertex F}
    (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) (hb : b F = 1) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let U := (commonBorel L S).pCoreIn 2
    IsElementaryAbelian 2 Q₀ ∧ IsElementaryAbelian 2 Q₁ ∧
    Q₀ = (Z F α).map (G₀ L S).subtype ∧
    Q₁ = (Z F β).map (G₀ L S).subtype ∧ U = Q₀ ⊔ Q₁ ∧
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2),
      ∃ (c₀ : BOneActionData F α β k₀ (Fin 2 → k₀))
        (c₁ : BOneActionData F β α k₁ (Fin 2 → k₁)),
      c₀.actor = graphLocalGroup F α ∧ c₁.actor = graphLocalGroup F β ∧
      Nat.card k₀ = Nat.card k₁ ∧ Even (Nat.card k₀) ∧
      OriginalNaturalCoreCoordinates false c₀ ∧ OriginalNaturalCoreCoordinates true c₁ ∧
      ((centerIn (enlargedEndpoint L S 0) = ⊥ ∧
        centerIn (enlargedEndpoint L S 1) = ⊥ ∧
        Nat.card Q₀ = Nat.card k₀ ^ 2 ∧ Nat.card Q₁ = Nat.card k₁ ^ 2 ∧
        Nat.card U = Nat.card k₀ ^ 3 ∧
        HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4 ∧
        BasedPathTransitive (X := G₀ L S) (graph F) 4 ∧
        ∀ {a d : Vertex F} (p : (graph F).Walk a d),
          IsSourcePath p → 4 ≤ p.length → Odd (Nat.card (pathFixer (X := G₀ L S) p))) ∨
      (Nat.card (centerIn (enlargedEndpoint L S 0)) = Nat.card k₀ ∧
        Nat.card (centerIn (enlargedEndpoint L S 1)) = Nat.card k₁ ∧
        Nat.card Q₀ = Nat.card k₀ ^ 3 ∧ Nat.card Q₁ = Nat.card k₁ ^ 3 ∧
        Nat.card U = Nat.card k₀ ^ 4 ∧
        HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5 ∧
        BasedPathTransitive (X := G₀ L S) (graph F) 5 ∧
        ∀ {a d : Vertex F} (p : (graph F).Walk a d),
          IsSourcePath p → 5 ≤ p.length → Odd (Nat.card (pathFixer (X := G₀ L S) p)))) := by
  obtain ⟨he₀,he₁,k₀,f₀,fin₀,ch₀,alg₀,k₁,f₁,fin₁,ch₁,alg₁,c₀,c₁,
    ha₀,ha₁,hfields,hcoord₀,hcoord₁⟩ :=
    DGS85.Reduction.original_bOne_natural_cores h hc hne hb
  have halg₀ : alg₀ = ZMod.algebra k₀ 2 := Subsingleton.elim _ _
  have halg₁ : alg₁ = ZMod.algebra k₁ 2 := Subsingleton.elim _ _
  subst alg₀ alg₁
  let : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
  let : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
  have hmark₀ := ha₀.trans (Noncommuting.Reduction.reduced_base_actor_eq_source h false)
  have hmark₁ := ha₁.trans (Noncommuting.Reduction.reduced_base_actor_eq_source h true)
  have hmodels (x : Vertex F) :
      IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)) := by
    have he : (graph F).Adj v w := SimpleGraph.dist_eq_one_iff_adj.mp (hc.1.trans hb)
    obtain ⟨n,hn,hm⟩ := reduced_cross_orbit_actor_models h hc hne he.1 x
    exact .linear n hn hm
  have hB := Noncommuting.Reduction.original_bOne_borel_core_eq_product h hmodels hc hne hb
  obtain ⟨hQ₀,hQ₁⟩ := original_cores_eq_center_spans_of_actions h c₀ c₁
  have horders := (original_center_and_core_product_orders h c₀ c₁
    (LinearEquiv.refl (ZMod 2) _) (LinearEquiv.refl (ZMod 2) _) hmark₀ hmark₁).2
  have hpaths := original_centers_reduced_path_parameters h c₀ c₁ hmark₀ hmark₁
    (LinearEquiv.refl (ZMod 2) _) (LinearEquiv.refl (ZMod 2) _)
  rw [ha₀,ha₁,reduced_graphLocalGroup_image h false,reduced_graphLocalGroup_image h true,
    ←hB] at horders
  rw [ha₀,ha₁,reduced_graphLocalGroup_image h false,reduced_graphLocalGroup_image h true] at hpaths
  have heven : Even (Nat.card k₀) := by
    let := Fintype.ofFinite k₀
    rw [Nat.card_eq_fintype_card,even_iff_two_dvd]
    exact (CharP.cast_eq_zero_iff k₀ 2 _).mp (FiniteField.cast_card_eq_zero k₀)
  refine ⟨he₀,he₁,hQ₀,hQ₁,hB,k₀,f₀,fin₀,ch₀,k₁,f₁,fin₁,ch₁,
    c₀,c₁,ha₀,ha₁,hfields,heven,hcoord₀,hcoord₁,?_⟩
  rcases horders with ⟨hz₀,hz₁,hq₀,hq₁,hU⟩ | ⟨hz₀,hz₁,hq₀,hq₁,hU⟩
  · rcases hpaths with ⟨_,_,hp,ht,ho⟩ | ⟨hz,_,_⟩
    · exact Or.inl ⟨hz₀,hz₁,hq₀,hq₁,hU,hp,ht,ho⟩
    · simp only [hz₀,Subgroup.card_bot] at hz
      exact (ne_of_gt (show 1 < Nat.card k₀ from Finite.one_lt_card)) hz.symm |>.elim
  · rcases hpaths with ⟨hz,_,_⟩ | ⟨_,_,hp,ht,ho⟩
    · simp only [hz,Subgroup.card_bot] at hz₀
      exact (ne_of_gt (show 1 < Nat.card k₀ from Finite.one_lt_card)) hz₀.symm |>.elim
    · exact Or.inr ⟨hz₀,hz₁,hq₀,hq₁,hU,hp,ht,ho⟩

open Theory.GroupTheory RankTwoAmalgam OriginalExtension in
/-- The actual universal-tree consumer needs only the original noncommuting
critical pair and b=1; its length is selected by the two source actor centers. -/
theorem original_bOne_intrinsic_tree_profile
    (h : HypothesisF11 L S) {v w : Vertex F}
    (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) (hb : b F = 1) :
    ∃ r : ℕ, (r = 3 ∨ r = 4) ∧
      (r = 3 ↔ centerIn (enlargedEndpoint L S 0) = ⊥) ∧
      (r = 3 ↔ centerIn (enlargedEndpoint L S 1) = ⊥) ∧
      HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) r (r+1) ∧
      BasedPathTransitive (X := (reducedAmalgam L S).Universal)
        (graph (Universal.cosetFamily (reducedAmalgam L S))) (r+1) ∧
      ∀ {a d} (p : (graph (Universal.cosetFamily (reducedAmalgam L S))).Walk a d),
        p.IsPath → p.length = r+1 →
          Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)) := by
  obtain ⟨_,_,_,_,_,k₀,f₀,fin₀,ch₀,k₁,f₁,fin₁,ch₁,c₀,c₁,ha₀,ha₁,_⟩ :=
    original_bOne_complete_profile h hc hne hb
  have hmark₀ := ha₀.trans (Noncommuting.Reduction.reduced_base_actor_eq_source h false)
  have hmark₁ := ha₁.trans (Noncommuting.Reduction.reduced_base_actor_eq_source h true)
  have htree := original_bOne_tree_path_alternatives h c₀ c₁ hmark₀ hmark₁
    (LinearEquiv.refl (ZMod 2) _) (LinearEquiv.refl (ZMod 2) _)
  rw [ha₀,ha₁,reduced_graphLocalGroup_image h false,reduced_graphLocalGroup_image h true] at htree
  rcases htree with ⟨hz₀,hz₁,hp,ht,ho⟩ | ⟨hz₀,hz₁,hp,ht,ho⟩
  · exact ⟨3,Or.inl rfl,⟨fun _ => hz₀,fun _ => rfl⟩,
      ⟨fun _ => hz₁,fun _ => rfl⟩,hp,ht,ho⟩
  · change Nat.card (centerIn (enlargedEndpoint L S 0)) = Nat.card k₀ at hz₀
    change Nat.card (centerIn (enlargedEndpoint L S 1)) = Nat.card k₁ at hz₁
    have hn₀ : centerIn (enlargedEndpoint L S 0) ≠ ⊥ := by
      intro he
      simp only [he,Subgroup.card_bot] at hz₀
      exact (ne_of_gt (show 1 < Nat.card k₀ from Finite.one_lt_card)) hz₀.symm
    have hn₁ : centerIn (enlargedEndpoint L S 1) ≠ ⊥ := by
      intro he
      simp only [he,Subgroup.card_bot] at hz₁
      exact (ne_of_gt (show 1 < Nat.card k₁ from Finite.one_lt_card)) hz₁.symm
    exact ⟨4,Or.inr rfl,iff_of_false (by decide) hn₀,
      iff_of_false (by decide) hn₁,hp,ht,ho⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
