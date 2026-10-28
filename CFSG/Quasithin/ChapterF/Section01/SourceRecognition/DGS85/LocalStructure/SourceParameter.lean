module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.RankOnePaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneClosedPaths
public import Theory.GroupAction.CubicTree.ShortRegularPaths

/-!
# The source minimum nonregular path length

DGS p.73 defines s as the minimum nonregular path length, and r as the
maximum regular path length. The first nonregular walk construction gives
s after conversion to the literal p.60 path convention. Short regularity
makes the chosen walk simple; the allowed two-edge closed return has the
same fixer and exits as its edge. This module proves that conversion and
applies 6.7 at the actual source minimum, preserving the full Borel.

Source: DGS, *Groups and Graphs* (1985), pp.60, 73--74 and 123.
-/

public noncomputable section
open scoped Pointwise
open Subgroup SimpleGraph SimpleGraph.Walk SimpleGraph.BasedWalk
open SimpleGraph.PathTransitivePolygon Theory.GroupAction.CubicTree
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open NoncommutingProfile
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

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

private theorem regular_vertices {n k : ℕ} {a b : Vertex (family P)}
    (p : BasedWalk (graph (family P)) n a) (q : BasedWalk (graph (family P)) k b)
    (he : p.vertices = q.vertices) : Regular (A := G) p ↔ Regular (A := G) q := by
  have hn : n = k := by
    have hh := congrArg List.length he
    simp only [BasedWalk.length_vertices] at hh
    omega
  subst k
  exact ⟨fun hh => ⟨leftRegular_of_vertices_eq p q he hh.1,
      rightRegular_of_vertices_eq p q he hh.2⟩,
    fun hh => ⟨leftRegular_of_vertices_eq q p he.symm hh.1,
      rightRegular_of_vertices_eq q p he.symm hh.2⟩⟩

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

private theorem based_regular_iff {n : ℕ} {a : Vertex (family P)}
    (p : BasedWalk (graph (family P)) n a) :
    PathRegular p.toWalk ↔ Regular (A := G) p := by
  rw [walk_regular_iff]
  exact regular_vertices _ _ (by rw [vertices_ofWalk,support_toWalk])

private theorem closed_two_regular_of_one
    {s : ℕ}
    (hshort : ∀ n < s, ∀ v : Vertex (family P), ∀ p : BasedWalk (graph (family P)) n v,
      p.Nonbacktracking → Regular (A := G) p)
    {a : Vertex (family P)} (p : (graph (family P)).Walk a a)
    (hl : p.length = 2) (hs : 1 < s) : PathRegular p := by
  cases p with
  | nil => simp at hl
  | cons hab t =>
    cases t with
    | nil => simp at hl
    | cons hba t =>
      cases t with
      | cons h t => simp only [length_cons] at hl; omega
      | nil =>
        have ht : PathExitTransitive (Walk.cons hba Walk.nil) :=
          (exit_regular_iff _).mpr (hshort 1 (by omega) _ _ trivial).2
        have hf : PathExitTransitive (Walk.cons hab (Walk.cons hba Walk.nil)) := by
          intro z hz x hx
          obtain ⟨g,hg,he⟩ := ht z hz x hx
          refine ⟨g,?_,he⟩
          intro j hj
          have ha := hg 1 (by simp)
          have hb := hg 0 (by simp)
          simp only [length_cons,length_nil] at hj
          interval_cases j <;> assumption
        have hr : (Walk.cons hab (Walk.cons hba Walk.nil)).reverse =
            Walk.cons hab (Walk.cons hba Walk.nil) := by simp
        exact ⟨hf,hr ▸ hf⟩


/-- Nonregular lengths in the literal DGS p.60 path convention. -/
@[expose] def sourceNonregularLengths : Set ℕ :=
  {n | ∃ a b : Vertex (family P), ∃ p : (graph (family P)).Walk a b,
    IsSourcePath p ∧ p.length = n ∧ ¬ PathRegular p}

/-- The first failing based walk realizes the book's minimum, including its
permitted closed paths. Both vertex orbits and the marked base edge are retained. -/
theorem source_first_nonregular_parameter (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B) :
    ∃ n : ℕ, IsLeast (sourceNonregularLengths (P := P)) (n+1) ∧
      (∀ k < n+1, ∀ v : Vertex (family P), ∀ p : BasedWalk (graph (family P)) k v,
        p.Nonbacktracking → Regular (A := G) p) ∧
      (∀ v : Vertex (family P), ∀ k ≤ n+1, RootPathTransitive (graph (family P)) G v k) ∧
      ∃ i : Bool, ∃ p : BasedWalk (graph (family P)) (n+1) (base (family P) i),
        p.Nonbacktracking ∧ ¬ RightRegular (A := G) p ∧ p.toWalk.IsPath ∧
        base (family P) false ∈ p.vertices ∧ base (family P) true ∈ p.vertices := by
  obtain ⟨n,hshort,ht,i,p,hp,hn,ha,hb⟩ := source_first_nonregular_path h hS
  have hval : ∀ v : Vertex (family P), 3 ≤ Nat.card ((graph (family P)).neighborSet v) := by
    intro v
    rw [card_neighbors_of_indices (family P)
      (fun j => ((family P (!j)).subgroupOf (family P j)).index) (fun _ => rfl)]
    exact source_valence_ge_three h hS v.type
  have hsimp := isPath_of_short_rightRegular hval (n+1)
    (fun k hk v q hq => (hshort k hk v q hq).2) p le_rfl hp
  refine ⟨n,?_,hshort,ht,i,p,hp,hn,hsimp,ha,hb⟩
  refine ⟨⟨_,_,p.toWalk,Or.inl hsimp,length_toWalk p,
    fun hh => hn ((based_regular_iff p).mp hh).2⟩,?_⟩
  rintro m ⟨a,b,q,hq,hl,hbad⟩
  by_contra hlt
  have hlen : q.length < n+1 := by omega
  apply hbad
  by_cases htwo : q.length = 2
  · rcases hq with hq | ⟨rfl,hq⟩
    · exact (walk_regular_iff q).mpr (hshort q.length hlen a _
        (nonbacktracking_ofWalk_of_isPath q hq))
    · exact closed_two_regular_of_one hshort q htwo (by omega)
  · exact (walk_regular_iff q).mpr (hshort q.length hlen a _
      (sourcePath_nonbacktracking q hq htwo))

/-- DGS s, the least nonregular source path length over both vertex orbits. -/
@[expose] def sourceS : ℕ := sInf (sourceNonregularLengths (P := P))

/-- The minimum is positive and attained in the original source path convention. -/
theorem sourceS_spec (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B) :
    0 < sourceS (P := P) ∧ IsLeast (sourceNonregularLengths (P := P)) (sourceS (P := P)) := by
  obtain ⟨n,hs,_⟩ := source_first_nonregular_parameter h hS
  have he : sourceS (P := P) = n+1 := by
    apply le_antisymm (Nat.sInf_le hs.1)
    exact hs.2 (Nat.sInf_mem ⟨n+1,hs.1⟩)
  rw [he]
  exact ⟨by omega,hs⟩

/-- Chapter 3 transitivity holds through the exact source minimum. -/
theorem sourceS_transitive (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (v : Vertex (family P)) {k : ℕ} (hk : k ≤ sourceS (P := P)) :
    RootPathTransitive (graph (family P)) G v k := by
  obtain ⟨n,hs,_,ht,_⟩ := source_first_nonregular_parameter h hS
  have he := (sourceS_spec h hS).2.unique hs
  rw [he] at hk
  exact ht v k hk

/-- Every shorter based walk is regular at both endpoints. -/
theorem sourceS_short_regular (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {k : ℕ} {v : Vertex (family P)} (p : BasedWalk (graph (family P)) k v)
    (hk : k < sourceS (P := P)) (hp : p.Nonbacktracking) : Regular (A := G) p := by
  obtain ⟨n,hs,hshort,_⟩ := source_first_nonregular_parameter h hS
  have he := (sourceS_spec h hS).2.unique hs
  rw [he] at hk
  exact hshort k hk v p hp

/-- A nonregular source path of length s has no backtrack, including the
source convention allowing the last vertex to repeat the first. -/
theorem sourceS_nonregular_nonbacktracking (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b)
    (hp : IsSourcePath p) (hl : p.length = sourceS (P := P))
    (hn : ¬ RightRegular (A := G) (ofWalk p)) : (ofWalk p).Nonbacktracking := by
  by_cases htwo : p.length = 2
  · rcases hp with hp | ⟨rfl,hp⟩
    · exact nonbacktracking_ofWalk_of_isPath p hp
    · have hr := closed_two_regular_of_one
        (fun k hk v q hq => sourceS_short_regular h hS q hk hq) p htwo
        (by omega : 1 < sourceS (P := P))
      exact (hn ((walk_regular_iff p).mp hr).2).elim
  · exact sourcePath_nonbacktracking p hp htwo

/-- The two literal descriptions of the pointwise fixer agree on every vertex. -/
theorem pathStabilizer_ofWalk {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) :
    pathStabilizer (family P) (ofWalk p) = pathFixer (X := G) p := by
  ext g
  rw [fixer_support]
  change (∀ z ∈ (ofWalk p).vertices, g • z = z) ↔ _
  rw [vertices_ofWalk]

/-- Source 6.7 at s itself, with all catalogue branching and transitivity
premises discharged and no enlargement-model assumption. -/
theorem sourceS_path_borel_product (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {n : ℕ} (hs : n+1 = sourceS (P := P)) {v : Vertex (family P)}
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    (ha : base (family P) false ∈ p.vertices) (hb : base (family P) true ∈ p.vertices) :
    (B : Set G) = ((B ⊓ pathStabilizer (family P) p : Subgroup G) : Set G) *
      (B.pCoreIn 2 : Set G) :=
  source_rankOne_path_borel_product h hB (sourceS_transitive h hS v hs.le) p hp ha hb

/-- DGS 6.7 for every source path of length s through the marked edge,
including the permitted two-edge closed return. -/
theorem sourceS_source_path_borel_product (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b)
    (hp : IsSourcePath p) (hl : p.length = sourceS (P := P))
    (ha : base (family P) false ∈ p.support) (hb : base (family P) true ∈ p.support) :
    (B : Set G) = ((B ⊓ pathFixer (X := G) p : Subgroup G) : Set G) *
      (B.pCoreIn 2 : Set G) := by
  have hnb : (ofWalk p).Nonbacktracking ∨ B ≤ pathFixer (X := G) p := by
    by_cases htwo : p.length = 2
    · rcases hp with hp | ⟨rfl,hp⟩
      · exact Or.inl (nonbacktracking_ofWalk_of_isPath p hp)
      · right
        cases p with
        | nil => simp at htwo
        | @cons a c a hac t =>
          cases t with
          | nil => simp at htwo
          | cons hca t =>
            cases t with
            | cons h t => simp only [length_cons] at htwo; omega
            | nil =>
              have hmem (x : Vertex (family P)) (hx : x ∈ (Walk.cons hac (Walk.cons hca Walk.nil)).support) :
                  x = a ∨ x = c := by
                simp only [Walk.support,List.mem_cons,List.not_mem_nil,or_false] at hx
                exact hx.elim Or.inl (fun hh => hh.elim Or.inr Or.inl)
              have ha' := hmem _ ha
              have hb' := hmem _ hb
              have hne : base (family P) false ≠ base (family P) true := by
                intro he
                have hh := congrArg (fun v : Vertex (family P) => v.type) he
                cases hh
              have hacbase : (a = base (family P) false ∧ c = base (family P) true) ∨
                  (a = base (family P) true ∧ c = base (family P) false) := by
                rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
                · exact (hne (ha'.trans hb'.symm)).elim
                · exact Or.inl ⟨ha'.symm,hb'.symm⟩
                · exact Or.inr ⟨hb'.symm,ha'.symm⟩
                · exact (hne (ha'.trans hb'.symm)).elim
              intro g hg
              have hgf : g • base (family P) false = base (family P) false := by
                change g ∈ stabilizer (family P) (base (family P) false)
                rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base]
                exact h.intersection ▸ hg |>.1
              have hgt : g • base (family P) true = base (family P) true := by
                change g ∈ stabilizer (family P) (base (family P) true)
                rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base]
                exact h.intersection ▸ hg |>.2
              apply (fixer_support _ g).mpr
              intro z hz
              rcases hmem z hz with rfl | rfl <;>
                rcases hacbase with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
    · exact Or.inl (sourcePath_nonbacktracking p hp htwo)
  rcases hnb with hnb | hfix
  · obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero
      (show p.length ≠ 0 by have := (sourceS_spec h hS).1; omega)
    let q : BasedWalk (graph (family P)) (n+1) a :=
      Eq.rec (motive := fun k _ => BasedWalk (graph (family P)) k a) (ofWalk p) hn
    have hq : q.vertices = p.support := by
      exact (BasedWalk.vertices_cast hn _).trans (vertices_ofWalk p)
    have hqnb : q.Nonbacktracking := by
      exact (BasedWalk.nonbacktracking_cast hn _).mpr hnb
    have hf : pathStabilizer (family P) q = pathStabilizer (family P) (ofWalk p) := by
      ext g
      change (∀ z ∈ q.vertices, g • z = z) ↔ (∀ z ∈ (ofWalk p).vertices, g • z = z)
      rw [hq,vertices_ofWalk]
    have hh := sourceS_path_borel_product h hB hS (hn.symm.trans hl) q hqnb
      (by rw [hq]; exact ha) (by rw [hq]; exact hb)
    rw [hf] at hh
    rwa [pathStabilizer_ofWalk] at hh
  · rw [inf_eq_left.mpr hfix]
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨x,hx,1,(B.pCoreIn 2).one_mem,mul_one x⟩
    · rintro x ⟨a,ha,b,hb,rfl⟩
      exact B.mul_mem ha (pCoreIn_le 2 B hb)

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual reduced graph has a simple path of source length s and a
complement to the original full-Borel core inside its original image. -/
theorem reduced_sourceS_path_complement (h : HypothesisF11 L S) :
    ∃ n : ℕ, n+1 = sourceS (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) ∧
      ∃ i : Bool, ∃ p : BasedWalk (graph (reducedFamily L S)) (n+1) (base (reducedFamily L S) i),
        p.Nonbacktracking ∧ ¬ RightRegular (A := G₀ L S) p ∧ p.toWalk.IsPath ∧
        ∃ D : Subgroup G,
          D ≤ B₀ L S ⊓ (pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype ∧
          Disjoint D ((commonBorel L S).pCoreIn 2) ∧
          D ⊔ (commonBorel L S).pCoreIn 2 = B₀ L S ∧ Nat.Coprime 2 (Nat.card D) := by
  obtain ⟨n,hs,_,ht,i,p,hp,hn,hsimp,ha,hb⟩ :=
    source_first_nonregular_parameter (reduced_triple h) (reduced_vertex_sylow h)
  refine ⟨n,((sourceS_spec (reduced_triple h) (reduced_vertex_sylow h)).2.unique hs).symm,
    i,p,hp,hn,hsimp,?_⟩
  exact reduced_path_original_complement h (reduced_rankOne_branching h)
    (ht _ _ le_rfl) p hp ha hb

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
