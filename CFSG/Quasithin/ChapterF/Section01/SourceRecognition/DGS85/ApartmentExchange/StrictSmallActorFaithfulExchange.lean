module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorBetaCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorReflection
public import Theory.GroupTheory.WeakBNPair.RegularTree.FaithfulPathExchange

/-!
# Faithful strict actors give literal half-path exchange

The internally constructed simultaneous root and full Cartan markings,
together with the actual reversing reflection, give exchange whenever the
smaller actor's own core is trivial. At a beta midpoint the source proves
that core is trivial from the nontrivial Cartan/full-kernel condition.
The alpha nonzero natural-kernel branch remains separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))

local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S

variable {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear)
include h hc hne hb hβu hns hlinear hp hl hT

/-- The source's literal marked root pair exchanges whenever its actual
own core vanishes. The reflection and full Cartan diagonal are constructed. -/
theorem strict_source_faithful_path_exchange
    (hzero : pCore 2 (halfPathActor (X := (A).Universal) p 6)=⊥)
    (g : (A).Universal)
    (hg : ∀ j, 6≤j → j≤12 → g • p.getVert j=p.getVert j)
    (hmove : g • a≠a) :
    ∃ y : (A).Universal, (∀ j≤6, y • p.getVert j=p.getVert j) ∧ y • (g • a)=b := by
  obtain ⟨K,fK,finK,chK,hK,e,hroots⟩ :=
    strict_source_small_actor_marked_coordinates h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  let D := halfPathActor (X := (A).Universal) p 6
  let v := (bOne_tree_cover h).vertex (p.getVert 6)
  let k := K v.type
  obtain ⟨_,hker,_,_,z,hR,hV,hdiag⟩ := hroots p hp hl hT
  let f := (MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 6 hl (e v))
  have hfi : Function.Injective f := (f.ker_eq_bot_iff).mp (by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective,hker,hzero])
  obtain ⟨x,hxD,_,_,_,hrev,_⟩ :=
    strict_source_small_actor_reflection h hc hne hb hβu hns hlinear p hp hl hT
  let c := chosenCartans h
  let d := strictSourceSmallActorGeometry h hc hne hb hβu hns hlinear
  have hfix : cartan c ≤ pathFixer (X := (A).Universal) p := by
    intro x hx j _
    exact reflectionApartment_fixed c d.reflection d.normalizes x hx _
      (hT _ (p.getVert_mem_support j))
  have hfac := apartment_path_factorization h c 6 (by decide) d.reflection d.fixes d.moves
    d.squares d.normalizes d.transitive d.thick (p.drop 6)
    (by rw [SimpleGraph.Walk.drop_length,hl]; decide) (by
      intro x hx
      rw [SimpleGraph.Walk.drop_support_eq_support_drop_min] at hx
      exact hT x (List.mem_of_mem_drop hx))
  apply halfFixer_exchange_of_faithful_coordinates p 6 hl (cartan c) D hfix hfac
    le_sup_left f hfi ?_ ?_ ?_ hdiag ⟨x,hxD⟩ hrev g hg hmove
  · intro x hx
    obtain ⟨a,ha⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent k (f x)).mp
      (hR ▸ mem_map_of_mem f hx)
    exact ⟨a,ha.symm⟩
  · intro y hy
    obtain ⟨a,ha⟩ := (hV (f y)).mp (mem_map_of_mem f hy)
    exact ⟨a,ha.symm⟩
  · intro a
    obtain ⟨y,hy,he⟩ := (hV (NaturalCubic.lower a)).mpr ⟨a,rfl⟩
    exact ⟨y,hy,he⟩

/-- At a beta midpoint, the original source discharges the faithful-core
condition; the full Cartan-kernel nontriviality remains the displayed case. -/
theorem strict_source_beta_path_exchange
    (hCU : (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 6))≠⊥)
    (htype : ((bOne_tree_cover h).vertex (p.getVert 6)).type=true)
    (g : (A).Universal)
    (hg : ∀ j, 6≤j → j≤12 → g • p.getVert j=p.getVert j)
    (hmove : g • a≠a) :
    ∃ y : (A).Universal, (∀ j≤6, y • p.getVert j=p.getVert j) ∧ y • (g • a)=b :=
  strict_source_faithful_path_exchange h hc hne hb hβu hns hlinear p hp hl hT
    (strict_source_small_actor_beta_core_eq_bot h hc hne hb hβu hns hlinear
      p hp hl hT hCU htype) g hg hmove

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
