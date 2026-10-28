module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourPathUpperTransport

/-!
# Exact source path parameters in the field-four exceptional branch

The transported native obstruction bounds every regular nonbacktracking
path by six. The book's path convention also permits a repeated last vertex;
except for the length-two return, these source paths are nonbacktracking,
so the same upper bound applies. Combining it with the already constructed
simple regular six-path and the source minimum five gives the literal
`HasSourcePathParameters ... 6 5`.

The critical-pair consumer constructs the earlier center action and retains
the full original J₂/Aut(J₂) marked-amalgam alternative. Its hypothesis `hD`
is the unchanged equality involving the original beta core and the actual
opposite reduced core; this module does not assume or replace its discharge.

Source: DGS, *Groups and Graphs* (1985), path convention p.60, extrema
pp.73--74, and (10.9), printed pp.162--163.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.Walk SimpleGraph.BasedWalk
open SimpleGraph.PathTransitivePolygon Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.WeakBNPair.RegularTree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open DGS85.Reduction
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G}
private theorem based_penultimate {V : Type*} {Γ : SimpleGraph V} {a b c : V}
    (hab : Γ.Adj a b) (p : Γ.Walk b c) :
    (ofWalk (Walk.cons hab p)).penultimate = (Walk.cons hab p).penultimate := by
  induction p generalizing a with
  | nil => rfl
  | cons h p ih => exact ih h

private theorem forward_ofWalk {V : Type*} {Γ : SimpleGraph V} {a b z : V}
    (p : Γ.Walk a b) : Theory.GroupAction.CubicTree.Forward (ofWalk p) z ↔
      Γ.Adj b z ∧ z ≠ p.penultimate := by
  cases p with
  | nil =>
    change Γ.Adj a z ↔ Γ.Adj a z ∧ z ≠ a
    exact ⟨fun hz => ⟨hz,hz.ne.symm⟩,And.left⟩
  | cons hab p =>
    change (Γ.Adj (ofWalk (Walk.cons hab p)).endpoint z ∧
      z ≠ (ofWalk (Walk.cons hab p)).penultimate) ↔ _
    rw [endpoint_ofWalk,based_penultimate]

private theorem nb_ofWalk_iff {V : Type*} {Γ : SimpleGraph V} {a b : V} (p : Γ.Walk a b) :
    (ofWalk p).Nonbacktracking ↔ ∀ i, i+2 ≤ p.length → p.getVert i ≠ p.getVert (i+2) := by
  induction p with
  | nil =>
    constructor
    · intro _ i hi; simp only [length_nil] at hi; omega
    · intro _; trivial
  | @cons a b c hab p ih =>
    cases p with
    | nil =>
      constructor
      · intro _ i hi; simp only [length_cons,length_nil] at hi; omega
      · intro _; trivial
    | @cons b d c hbd p =>
      change (d ≠ a ∧ (ofWalk (Walk.cons hbd p)).Nonbacktracking) ↔ _
      rw [ih]
      constructor
      · rintro ⟨hne,hp⟩ i hi
        cases i with
        | zero => simpa only [getVert_zero,getVert_cons_succ] using hne.symm
        | succ i => exact hp i (by simp only [length_cons] at *; omega)
      · intro hp
        refine ⟨by simpa only [getVert_zero,getVert_cons_succ] using
          (hp 0 (by simp only [length_cons]; omega)).symm,?_⟩
        intro i hi
        exact hp (i+1) (by simp only [length_cons] at *; omega)

private theorem sourcePath_nonbacktracking {a b : Vertex (family P)} (p : (graph (family P)).Walk a b)
    (hp : IsSourcePath p) (hne : p.length ≠ 2) : (ofWalk p).Nonbacktracking := by
  rcases hp with hp | ⟨hab,hp⟩
  · exact nonbacktracking_ofWalk_of_isPath p hp
  · subst b
    rw [nb_ofWalk_iff]
    intro i hi he
    by_cases hlt : i+2 < p.length
    · have h1 : i ≤ p.dropLast.length := by rw [length_dropLast]; omega
      have h2 : i+2 ≤ p.dropLast.length := by rw [length_dropLast]; omega
      have hh := hp.getVert_injOn h1 h2
        (by rwa [getVert_dropLast (by omega : i < p.length), getVert_dropLast hlt])
      omega
    · have hlast : i+2 = p.length := by omega
      have h1 : i ≤ p.dropLast.length := by rw [length_dropLast]; omega
      have hh := hp.getVert_injOn h1 (Nat.zero_le _) (by
        rw [getVert_dropLast (by omega : i < p.length),getVert_zero]
        rwa [hlast,getVert_length] at he)
      omega


private theorem fixer_support {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (g : G) :
    g ∈ pathFixer (X := G) p ↔ ∀ z ∈ p.support, g • z = z := by
  constructor
  · intro hg z hz
    obtain ⟨k,rfl,hk⟩ := mem_support_iff_exists_getVert.mp hz
    exact hg k hk
  · intro hg k _
    exact hg _ (p.getVert_mem_support k)

private theorem rightRegular_vertices {n k : ℕ} {a b : Vertex (family P)}
    (p : BasedWalk (graph (family P)) n a) (q : BasedWalk (graph (family P)) k b)
    (he : p.vertices = q.vertices) : RightRegular (A := G) p ↔ RightRegular (A := G) q := by
  have hn : n = k := by
    have hh := congrArg List.length he
    simp only [BasedWalk.length_vertices] at hh
    omega
  subst k
  exact ⟨rightRegular_of_vertices_eq p q he,rightRegular_of_vertices_eq q p he.symm⟩

private theorem exit_regular_iff {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) :
    PathExitTransitive p ↔ RightRegular (A := G) (ofWalk p) := by
  constructor
  · intro hr z w hz hw
    obtain ⟨g,hg,he⟩ := hr z ((forward_ofWalk p).mp hz) w ((forward_ofWalk p).mp hw)
    exact ⟨g,fun y hy => (fixer_support p g).mp hg y
      (by rwa [vertices_ofWalk] at hy),he⟩
  · intro hr z hz w hw
    obtain ⟨g,hg,he⟩ := hr z w ((forward_ofWalk p).mpr hz) ((forward_ofWalk p).mpr hw)
    exact ⟨g,(fixer_support p g).mpr (fun y hy => hg y
      (by rwa [vertices_ofWalk])),he⟩

private theorem walk_regular_iff {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) :
    PathRegular p ↔ Regular (A := G) (ofWalk p) := by
  have he : (ofWalk p.reverse).vertices = (reverse (ofWalk p)).vertices := by
    rw [vertices_ofWalk,Walk.support_reverse,vertices_reverse,vertices_ofWalk]
  have hr : RightRegular (A := G) (ofWalk p.reverse) ↔
      RightRegular (A := G) (reverse (ofWalk p)) :=
    rightRegular_vertices _ _ he
  rw [PathRegular,exit_regular_iff,exit_regular_iff,hr,rightRegular_reverse_iff]
  exact and_comm


variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance fieldFourExactPathsAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] :
    Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2

/-- The literal source extrema in the field-four exceptional branch are
`r = 6` and `s = 5`, including both vertex orbits and permitted closed paths. -/
theorem original_bTwo_field_four_path_parameters
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
    HasSourcePathParameters
      (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 5 := by
  obtain ⟨eJ⟩ := original_bTwo_field_four_reduced_iso
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨hs,p,hp,hpath,hreg,hr⟩ := original_bTwo_field_four_regular_six_path
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  constructor
  · refine ⟨⟨α,p.endpoint,p.toWalk,Or.inl hpath,length_toWalk p,hreg⟩,?_⟩
    rintro n ⟨a,b,q,hq,hql,hqr⟩
    by_cases hn : n ≤ 6
    · exact hn
    · have hnb := sourcePath_nonbacktracking q hq (by omega)
      have hh := marked_regular_length_le_six h eJ (ofWalk q) hnb
        ((walk_regular_iff q).mp hqr)
      omega
  · have hh := (sourceS_spec (reduced_triple h) (reduced_vertex_sylow h)).2
    rw [hs] at hh
    exact hh

/-- The original critical-pair application retains the full J₂/Aut(J₂)
marking and the actual opposite-core equality while supplying both extrema. -/
theorem original_bTwo_field_four_marked_parameters
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
      HasSourcePathParameters
        (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 5 := by
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
    original_bTwo_field_four_path_parameters h hb c hactor hcentral ht htne hcomm hnot
      e hD (LinearEquiv.refl _ _) hK⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
