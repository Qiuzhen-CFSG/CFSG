module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourNativePaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalProfileCentral

/-!
# Regular six-path in the field-four branch

The native J₂ path certificate gives a regular nonbacktracking six-walk in the
original reduced graph.  The field-four order bound gives `sourceS ≤ 5`, while
the transported native five-path gives the matching lower bound.  At source
minimum five, every nonbacktracking five-walk is simple; regularity rules out
the only remaining possible repetition in a six-walk.  The resulting path is
therefore an actual simple regular six-path, with both endpoint actions
retained for the later Chapter 10 path-parameter arguments.

The final consumer constructs the natural center action and discharges the
centrality, edge commutator and core obstruction premises from the original
noncommuting critical pair. It retains the compatible full original
J₂/Aut(J₂) alternatives alongside these path conclusions.

Source: DGS, *Groups and Graphs* (1985), (10.9), pp.162--163.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

local instance fieldFourRegularPathsAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] :
    Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2

private theorem regular_six_isPath (h : HypothesisF11 L S)
    (hs : DGS85.sourceS (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) = 5)
    {v : Vertex F₀} (p : BasedWalk (graph F₀) 6 v)
    (hp : p.Nonbacktracking) (hr : Regular (A := G₀ L S) p) : p.toWalk.IsPath := by
  have hval (x : Vertex F₀) : 3 ≤ Nat.card ((graph F₀).neighborSet x) := by
    rw [card_neighbors_of_indices F₀
      (fun i => ((F₀ (!i)).subgroupOf (F₀ i)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) x.type
  have hsimp {x : Vertex F₀} (q : BasedWalk (graph F₀) 5 x)
      (hq : q.Nonbacktracking) : q.vertices.Nodup := by
    have hqpath := isPath_of_short_rightRegular hval 5
      (fun n hn x r hr => (sourceS_short_regular (reduced_triple h)
        (reduced_vertex_sylow h) r (by omega) hr).2) q le_rfl hq
    rw [← support_toWalk]
    exact hqpath.support_nodup
  have hpre := hsimp (p.take 5 (by decide)) (nonbacktracking_take _ p hp)
  have htail := hsimp p.2 (nonbacktracking_tail p hp)
  rcases p with ⟨a,b,c,d,e,f,z⟩
  change [v,(a : Vertex F₀),b,c,d,e].Nodup at hpre
  change [(a : Vertex F₀),b,c,d,e,f].Nodup at htail
  have hfv : (f : Vertex F₀) ≠ v := by
    intro he
    have hae : (a : Vertex F₀) ≠ (e : Vertex F₀) := by
      have hh := (List.nodup_cons.mp (List.nodup_cons.mp hpre).2).1
      intro heq
      apply hh
      simp [heq]
    have hfwd : Forward (Γ := graph F₀) (n := 6) (x := v)
        (⟨a,b,c,d,e,f,z⟩ : BasedWalk (graph F₀) 6 v) a := by
      change (graph F₀).Adj f a ∧ (a : Vertex F₀) ≠ (e : Vertex F₀)
      exact ⟨by rw [he]; exact a.property,hae⟩
    exact forward_not_mem_vertices_of_rightRegular hval _ hr.2 hfwd (by
      change (a : Vertex F₀) ∈ [v,a,b,c,d,e,f]
      simp)
  apply Walk.IsPath.mk'
  change [v,(a : Vertex F₀),b,c,d,e,f].Nodup
  refine List.nodup_cons.mpr ⟨?_,htail⟩
  have hh := (List.nodup_cons.mp hpre).1
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hh ⊢
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hfv.symm⟩

private theorem six_source_regular {v : Vertex F₀}
    (p : BasedWalk (graph F₀) 6 v) (hr : Regular (A := G₀ L S) p) :
    PathRegular p.toWalk := by
  rcases p with ⟨a,b,c,d,e,f,z⟩
  constructor
  · intro x hx y hy
    obtain ⟨g,hg,hgy⟩ := hr.2 x y hx hy
    refine ⟨g,?_,hgy⟩
    intro i hi
    apply hg
    rw [←support_toWalk]
    exact Walk.getVert_mem_support _ i
  · intro x hx y hy
    have hx' : Backward (Γ := graph F₀) (n := 6) (x := v)
        (⟨a,b,c,d,e,f,z⟩ : BasedWalk (graph F₀) 6 v) x := by
      exact hx
    have hy' : Backward (Γ := graph F₀) (n := 6) (x := v)
        (⟨a,b,c,d,e,f,z⟩ : BasedWalk (graph F₀) 6 v) y := by
      exact hy
    obtain ⟨g,hg,hgy⟩ := hr.1 x y hx' hy'
    refine ⟨g,?_,hgy⟩
    intro i hi
    apply hg
    rw [←support_toWalk]
    have hh := Walk.getVert_mem_support
      (BasedWalk.toWalk (G := graph F₀) (n := 6) (x := v) ⟨a,b,c,d,e,f,z⟩).reverse i
    simpa only [Walk.support_reverse,List.mem_reverse] using hh

/-- The field-four J₂ branch supplies the literal source minimum and a simple
regular six-path at the original reduced alpha vertex. -/
theorem original_bTwo_field_four_regular_six_path
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    DGS85.sourceS
        (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) = 5 ∧
      ∃ p : BasedWalk (graph F₀) 6 α,
        p.Nonbacktracking ∧ p.toWalk.IsPath ∧
          PathRegular p.toWalk ∧ Regular (A := G₀ L S) p := by
  have hs := original_bTwo_field_four_sourceS_eq_five
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨p,hp,hr⟩ := original_bTwo_field_four_regular_six_walk
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  exact ⟨hs,p,hp,regular_six_isPath h hs p hp hr,six_source_regular p hr,hr⟩

/-- The original critical-pair branch supplies both the full marked
J₂/Aut(J₂) alternative and the regular six-path. The earlier center action,
centrality, commutator and core obstruction premises are all discharged. -/
theorem original_bTwo_field_four_marked_paths
    (h : HypothesisF11 L S) {u t : Vertex F₀}
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hb : b F₀ = 2) (hβu : (graph F₀).Adj β u)
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) (hK : Nat.card K = 4)
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype) :
    (Nonempty (Theory.GroupTheory.RankTwoAmalgam.Iso
        (OriginalExtension.originalAmalgam L S).reverse
        GreenBook.HallJanko.j2Model.toMarking.amalgam) ∨
      Nonempty (Theory.GroupTheory.RankTwoAmalgam.Iso
        (OriginalExtension.originalAmalgam L S).reverse
        GreenBook.HallJanko.autJ2Model.toMarking.amalgam)) ∧
    DGS85.sourceS
        (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) = 5 ∧
      ∃ p : BasedWalk (graph F₀) 6 α,
        p.Nonbacktracking ∧ p.toWalk.IsPath ∧
          PathRegular p.toWalk ∧ Regular (A := G₀ L S) p := by
  have hab : (graph F₀).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ :=
    reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have he : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β hab
  exact ⟨original_bTwo_field_four_original_j2_or_autJ2_iso h hb c hactor hcentral
      ht htne hcomm hnot e hD (LinearEquiv.refl _ _) hK,
    original_bTwo_field_four_regular_six_path h hb c hactor hcentral ht htne hcomm hnot
      e hD (LinearEquiv.refl _ _) hK⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
