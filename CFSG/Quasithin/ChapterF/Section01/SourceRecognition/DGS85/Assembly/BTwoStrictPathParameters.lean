module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictSevenPath
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictOrders
public import Theory.GroupAction.RankTwoCosetGeometry.SevenPathCounting
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SourceRootTransitivityLowerBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.StrictSourcePathParameters

/-!
# The strict source path parameters

The marked edge two-core has order `q₀³ q₁³`, the number of seven-paths
through an edge. Its orbit on the Cartan seven-path with odd fixer fills
that set. Reversal supplies both vertex types, so every source path of
length at most six is regular. All longer source paths have odd fixers,
and odd valence makes them nonregular. Thus the literal source extrema
are `r = 6` and `s = 7`, including the source's closed-path convention.

Source: DGS, *Groups and Graphs* (1985), (10.10)(a)--(c), printed p.164.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.Walk SimpleGraph.BasedWalk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true

private theorem nb_ofWalk_iff {V : Type*} {Γ : SimpleGraph V} {a b : V}
    (p : Γ.Walk a b) :
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

private theorem sourcePath_nonbacktracking {a b : Vertex F}
    (p : (graph F).Walk a b) (hp : IsSourcePath p) (hne : p.length ≠ 2) :
    (ofWalk p).Nonbacktracking := by
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

/-- The strict branch has the literal source parameters `(6,7)` and odd
fixers of every source path of length at least seven. The two field
markings are those on the original endpoints. -/
theorem original_bTwo_strict_path_parameters
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    (K : Bool → Type) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,K i)) :
    HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 7 ∧
      ∀ {a d : Vertex F} (p : (graph F).Walk a d),
        IsSourcePath p → 7 ≤ p.length →
          Odd (Nat.card (pathFixer (X := G₀ L S) p)) := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  let eSL (i : Bool) : SL(2,K i) ≃* PSL(2,K i) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi (K i))
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  let eG (i : Bool) := (reduced_graphLinearQuotient h i (e i)).trans (eSL i).symm
  have hi (i : Bool) : ((F (!i)).subgroupOf (F i)).index = Nat.card (K i)+1 := by
    have hadj : (graph F).Adj (base F i) (base F (!i)) :=
      ⟨by change i ≠ !i; cases i <;> decide,
        Subgroup.CosetGeometry.incident_base _ _ _⟩
    have he := source_linear_edge_index_of_quotient H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hadj (eG i)
    rw [show stabilizer F (base F i) = F i from
        Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F (base F (!i)) = F (!i) from
        Subgroup.CosetGeometry.stabilizer_base _ _] at he
    exact he
  have hval := card_neighbors_of_indices F (fun i => Nat.card (K i)+1) hi
  have hval3 (v : Vertex F) : 3 ≤ Nat.card ((graph F).neighborSet v) := by
    rw [card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three H (reduced_vertex_sylow h) v.type
  have hvalodd (v : Vertex F) : Odd (Nat.card ((graph F).neighborSet v)) := by
    rw [hval]
    have heven : Even (Nat.card (K v.type)) := by
      let := Fintype.ofFinite (K v.type)
      rw [Nat.card_eq_fintype_card,even_iff_two_dvd]
      exact (CharP.cast_eq_zero_iff (K v.type) 2 _).mp
        (FiniteField.cast_card_eq_zero (K v.type))
    exact heven.add_one
  obtain ⟨z,hyz,hzu⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet y)
    (by rw [←Nat.card_coe_set_eq]; have := hval3 y; omega) u
  obtain ⟨g,_,_,hg⟩ :=
    original_bTwo_seven_path_fixer_odd h hc hne hb hβu ht htne hy hyne hns
  obtain ⟨p,_,hp,ho⟩ := hg z hyz hzu
  obtain ⟨htrans,hodd7⟩ := seven_path_geometry_of_odd_witness F
    (fun i => Nat.card (K i)) (fun _ => Nat.card_pos) hval
    (fun {_ _} had =>
      original_strict_edge_core_card_at h hc hne hb hβu ht htne hy hyne hns K e had)
    p hp ho
  have hs : 7 ≤ sourceS (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) :=
    sourceS_ge_of_root_transitive H (reduced_vertex_sylow h) (fun i => htrans (base F i))
  have hreg {a d : Vertex F} (q : (graph F).Walk a d)
      (hq : IsSourcePath q) (hl : q.length ≤ 6) : PathRegular q := by
    by_contra hbad
    have hmin := (sourceS_spec H (reduced_vertex_sylow h)).2.2
      (show q.length ∈ sourceNonregularLengths
          (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) from
        ⟨a,d,q,hq,rfl,hbad⟩)
    omega
  have hodd {a d : Vertex F} (q : (graph F).Walk a d)
      (hq : IsSourcePath q) (hl : 7 ≤ q.length) :
      Odd (Nat.card (pathFixer (X := G₀ L S) q)) := by
    have hh := long_path_fixer_odd_of_seven F hodd7 (ofWalk q)
      (sourcePath_nonbacktracking q hq (by omega)) hl
    rwa [pathStabilizer_ofWalk] at hh
  exact CommutingOneProfile.OddValenceSourceGeometry.source_path_parameters_six_seven
    (fun i => (P₀ L S i).subgroupOf (G₀ L S)) (fun v => ⟨hval3 v,hvalodd v⟩) hreg hodd

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
