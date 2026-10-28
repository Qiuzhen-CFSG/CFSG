module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneRegularPaths

/-!
# Source path conventions and the exact b=1 extrema

DGS p.60 allows the last vertex of a path to repeat the first. Such a
closed path of length at least three cannot be regular: its first neighbor
is fixed by the whole stabilizer and lies in the terminal complement of
size q. A closed path cannot extend a regular simple prefix of length at
least two, for the same reason. Thus the short regularity already proved
excludes all closed paths that could change r or s. The allowed two-edge
return has the same stabilizer as its edge and is regular.

For longer closed paths, their simple prefixes have odd stabilizers, so
the full stabilizers are odd as well. This yields the literal source
maximum and minimum over both orbits, including the closed-path clause.

Source: DGS, *Groups and Graphs* (1985), path definition p.60, regularity
and extremal definitions pp.73--74, and (10.5)(c,d), pp.156--157.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The paths of DGS p.60: all vertices are distinct, except that the first and
last may agree. The latter clause includes the length-two return along an edge. -/
def IsSourcePath {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) : Prop :=
  p.IsPath ∨ (a = b ∧ p.dropLast.IsPath)

/-- The source extrema include paths whose only repeated vertex is the endpoint. -/
def HasSourcePathParameters (r s : ℕ) : Prop :=
  IsGreatest {n | ∃ a b : Vertex (family P), ∃ p : (graph (family P)).Walk a b,
    IsSourcePath p ∧ p.length = n ∧ PathRegular p} r ∧
  IsLeast {n | ∃ a b : Vertex (family P), ∃ p : (graph (family P)).Walk a b,
    IsSourcePath p ∧ p.length = n ∧ ¬PathRegular p} s

private theorem pathFixer_le_dropLast {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) : pathFixer (X := G) p ≤ pathFixer (X := G) p.dropLast := by
  cases p with
  | nil => exact le_rfl
  | cons ha t =>
    intro g hg j hj
    have hl : j < (Walk.cons ha t).length := by rw [length_dropLast] at hj; simp only [length_cons] at *; omega
    rw [getVert_dropLast hl]
    exact hg j hl.le

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : LocallyRankOneTriple P B)
    (c₀ : BOneActionData (family P) (base (family P) false) (base (family P) true) k₀ W₀)
    (c₁ : BOneActionData (family P) (base (family P) true) (base (family P) false) k₁ W₁)
    (hn₀ : B ≤ normalizer (c₀.actor : Set G)) (hn₁ : B ≤ normalizer (c₁.actor : Set G))
local instance bOneClosedAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
include h c₀ c₁ hn₀ hn₁

private theorem not_exit_transitive_of_fixed_exit
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀))
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) (hp : ¬p.Nil)
    {z : Vertex (family P)} (hz : z ∈ pathExits p)
    (hfix : ∀ g ∈ pathFixer (X := G) p, g • z = z) : ¬ PathExitTransitive p := by
  have hc : 1 < (pathExits p).ncard := by
    rw [←Nat.card_coe_set_eq,pathExits_card h c₀ c₁ hn₀ hn₁ E₀ p hp]
    exact Finite.one_lt_card
  obtain ⟨x,hx,hne⟩ := Set.exists_ne_of_one_lt_ncard hc z
  intro ht
  obtain ⟨g,hg,he⟩ := ht z hz x hx
  exact hne (he.symm.trans (hfix g hg))

/-- A closed source path of length at least three is nonregular, since its first
neighbor is a fixed point in the terminal exit set of size q. -/
theorem closed_source_path_not_regular
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) {a : Vertex (family P)}
    (p : (graph (family P)).Walk a a) (hp : p.dropLast.IsPath) (hlen : 3 ≤ p.length) :
    ¬ PathRegular p := by
  have hz : p.getVert 1 ∈ pathExits p := by
    refine ⟨?_,?_⟩
    · change (graph (family P)).Adj a (p.getVert 1)
      simpa only [getVert_zero] using p.adj_getVert_succ (by omega : 0 < p.length)
    · intro he
      have hj1 : 1 < p.length := by omega
      have hj2 : p.length-1 < p.length := by omega
      have hv : p.dropLast.getVert 1 = p.dropLast.getVert (p.length-1) := by
        rw [getVert_dropLast hj1,getVert_dropLast hj2]
        exact he
      have hh := hp.getVert_injOn (show 1 ≤ p.dropLast.length by rw [length_dropLast]; omega)
        (show p.length-1 ≤ p.dropLast.length by rw [length_dropLast]) hv
      omega
  intro hr
  exact not_exit_transitive_of_fixed_exit h c₀ c₁ hn₀ hn₁ E₀ p
    (not_nil_iff_lt_length.mpr (by omega)) hz (fun g hg => hg 1 (by omega)) hr.1

/-- A closed source path cannot extend a regular simple prefix of length at least two. -/
theorem no_closed_source_path_of_regular_prefix
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) {a : Vertex (family P)}
    (p : (graph (family P)).Walk a a) (hp : p.dropLast.IsPath) (hlen : 3 ≤ p.length)
    (hreg : PathRegular p.dropLast) : False := by
  have hpos : 0 < p.dropLast.length := by rw [length_dropLast]; omega
  have hz : a ∈ pathExits p.dropLast := by
    refine ⟨p.adj_penultimate (not_nil_iff_lt_length.mpr (by omega)),?_⟩
    intro he
    have hh := hp.getVert_injOn (Nat.zero_le p.dropLast.length)
      (Nat.sub_le p.dropLast.length 1)
      (show p.dropLast.getVert 0 = p.dropLast.getVert (p.dropLast.length-1) from
        p.dropLast.getVert_zero.trans he)
    rw [length_dropLast] at hh
    omega
  exact not_exit_transitive_of_fixed_exit h c₀ c₁ hn₀ hn₁ E₀ p.dropLast
    (not_nil_iff_lt_length.mpr hpos) hz
    (fun g hg => by simpa only [getVert_zero] using hg 0 (Nat.zero_le _)) hreg.1

/-- The two-edge return permitted by the source definition has the same fixer
and endpoint complement as its single underlying edge. -/
theorem closed_two_path_regular
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    {a : Vertex (family P)} (p : (graph (family P)).Walk a a) (hlen : p.length = 2) : PathRegular p := by
  cases p with
  | nil => simp at hlen
  | cons hab t =>
    cases t with
    | nil => simp at hlen
    | cons hba t =>
      cases t with
      | cons h t => simp only [length_cons] at hlen; omega
      | nil =>
        have ht := (one_path_regular h c₀ c₁ hn₀ hn₁ E₀ E₁
          (Walk.cons hba Walk.nil) (by simpa using hba.ne) (by simp)).1
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

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : LocallyRankOneTriple P B)
    (c₀ : BOneActionData (family P) (base (family P) false) (base (family P) true) k₀ W₀)
    (c₁ : BOneActionData (family P) (base (family P) true) (base (family P) false) k₁ W₁)
    (hn₀ : B ≤ normalizer (c₀.actor : Set G)) (hn₁ : B ≤ normalizer (c₁.actor : Set G))
local instance bOneClosedParametersAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
include h c₀ c₁ hn₀ hn₁

private theorem closed_path_regular_of_le_two
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    {a : Vertex (family P)} (p : (graph (family P)).Walk a a) (hlen : p.length ≤ 2) : PathRegular p := by
  by_cases h2 : p.length = 2
  · exact closed_two_path_regular h c₀ c₁ hn₀ hn₁ E₀ E₁ p h2
  · cases p with
    | nil =>
      have hf : PathExitTransitive (Walk.nil : (graph (family P)).Walk a a) := by
        intro z hz x hx
        obtain ⟨g,hg,he⟩ := locally_transitive (family P) hz.1 hx.1
        refine ⟨g,?_,he⟩
        intro j hj
        have : j = 0 := by simpa only [length_nil,Nat.le_zero] using hj
        subst j
        exact hg
      exact ⟨hf,hf⟩
    | cons ha t =>
      cases t with
      | nil => exact False.elim (ha.ne rfl)
      | cons ha t => simp only [length_cons] at hlen h2; omega

private theorem source_parameters_of_simple
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (r : ℕ) (hr : r = 3 ∨ r = 4) (hpar : HasPathParameters (P := P) r (r+1))
    (hreg : ∀ {a b : Vertex (family P)} (p : (graph (family P)).Walk a b),
      p.IsPath → 0 < p.length → p.length ≤ r → PathRegular p)
    (hodd : ∀ {a b : Vertex (family P)} (p : (graph (family P)).Walk a b),
      p.IsPath → r+1 ≤ p.length → Odd (Nat.card (pathFixer (X := G) p))) :
    HasSourcePathParameters (P := P) r (r+1) ∧
    ∀ {a b : Vertex (family P)} (p : (graph (family P)).Walk a b),
      IsSourcePath p → r+1 ≤ p.length → Odd (Nat.card (pathFixer (X := G) p)) := by
  have hclosed {a : Vertex (family P)} (p : (graph (family P)).Walk a a)
      (hp : p.dropLast.IsPath) (h3 : 3 ≤ p.length) : r+1 < p.length := by
    by_contra hn
    apply no_closed_source_path_of_regular_prefix h c₀ c₁ hn₀ hn₁ E₀ p hp h3
    exact hreg p.dropLast hp (by rw [length_dropLast]; omega) (by rw [length_dropLast]; omega)
  refine ⟨⟨?_,?_⟩,?_⟩
  · obtain ⟨a,b,p,hp,hl,hR⟩ := hpar.1.1
    refine ⟨⟨a,b,p,Or.inl hp,hl,hR⟩,?_⟩
    rintro n ⟨u,v,t,ht,hlt,hRt⟩
    rcases ht with ht | ⟨rfl,ht⟩
    · exact hpar.1.2 ⟨u,v,t,ht,hlt,hRt⟩
    · by_cases h3 : 3 ≤ t.length
      · exact False.elim (closed_source_path_not_regular h c₀ c₁ hn₀ hn₁ E₀ t ht h3 hRt)
      · omega
  · obtain ⟨a,b,p,hp,hl,hR⟩ := hpar.2.1
    refine ⟨⟨a,b,p,Or.inl hp,hl,hR⟩,?_⟩
    rintro n ⟨u,v,t,ht,hlt,hRt⟩
    rcases ht with ht | ⟨rfl,ht⟩
    · exact hpar.2.2 ⟨u,v,t,ht,hlt,hRt⟩
    · by_cases h3 : 3 ≤ t.length
      · have := hclosed t ht h3
        omega
      · exact False.elim (hRt (closed_path_regular_of_le_two h c₀ c₁ hn₀ hn₁ E₀ E₁ t (by omega)))
  · intro a b p hp hl
    rcases hp with hp | ⟨rfl,hp⟩
    · exact hodd p hp hl
    · have hh := hclosed p hp (by omega)
      have ho := hodd p.dropLast hp (by rw [length_dropLast]; omega)
      exact Odd.of_dvd_nat ho (card_dvd_of_le (pathFixer_le_dropLast p))

/-- Exact source 10.5(c,d), including closed paths allowed by the definition on
p.60, and the based transitivity interface used by the apartment construction. -/
theorem bOne_source_path_parameters
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁)) :
    (centerIn c₀.actor = ⊥ ∧ centerIn c₁.actor = ⊥ ∧
      HasSourcePathParameters (P := P) 3 4 ∧
      BasedPathTransitive (X := G) (graph (family P)) 4 ∧
      ∀ {a b : Vertex (family P)} (p : (graph (family P)).Walk a b),
        IsSourcePath p → 4 ≤ p.length → Odd (Nat.card (pathFixer (X := G) p))) ∨
    (Nat.card (centerIn c₀.actor) = Nat.card k₀ ∧
      Nat.card (centerIn c₁.actor) = Nat.card k₁ ∧
      HasSourcePathParameters (P := P) 4 5 ∧
      BasedPathTransitive (X := G) (graph (family P)) 5 ∧
      ∀ {a b : Vertex (family P)} (p : (graph (family P)).Walk a b),
        IsSourcePath p → 5 ≤ p.length → Odd (Nat.card (pathFixer (X := G) p))) := by
  have hreg {a b : Vertex (family P)} (p : (graph (family P)).Walk a b)
      (hp : p.IsPath) (hpos : 0 < p.length)
      (hl : p.length ≤ 3 ∨ (p.length ≤ 4 ∧ Nat.card (centerIn c₀.actor) = Nat.card k₀)) :
      PathRegular p := by
    by_cases h1 : p.length = 1
    · exact one_path_regular h c₀ c₁ hn₀ hn₁ E₀ E₁ p hp h1
    · exact short_path_regular h c₀ c₁ hn₀ hn₁ E₀ E₁ p hp (by omega)
  rcases bOne_path_parameters h c₀ c₁ hn₀ hn₁ E₀ E₁ with
    ⟨hc₀,hc₁,hpar,htrans,hodd⟩ | ⟨hc₀,hc₁,hpar,htrans,hodd⟩
  · have hs := source_parameters_of_simple h c₀ c₁ hn₀ hn₁ E₀ E₁ 3 (Or.inl rfl) hpar
      (fun {_ _} p hp hpos hl => hreg p hp hpos (Or.inl hl)) hodd
    exact Or.inl ⟨hc₀,hc₁,hs.1,htrans,hs.2⟩
  · have hs := source_parameters_of_simple h c₀ c₁ hn₀ hn₁ E₀ E₁ 4 (Or.inr rfl) hpar
      (fun {_ _} p hp hpos hl => hreg p hp hpos (Or.inr ⟨hl,hc₀⟩)) hodd
    exact Or.inr ⟨hc₀,hc₁,hs.1,htrans,hs.2⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
