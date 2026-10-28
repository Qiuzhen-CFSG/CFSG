module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneRootActions

/-!
# Exact regular-path parameters in the b=1 branch

Every short path is regular at both ends by its actual root action. At the
next length the stabilizer is odd and cannot be transitive on an even set
of q exits. Thus the regular lengths are exactly zero through three when
the local centers vanish, and zero through four when their order is q.
Actual simple paths realize both extrema, over both vertex orbits. The
closed paths additionally permitted on source p.60 are handled in
`BOneClosedPaths`, which supplies the unrestricted source extrema.

Prefix alignment also gives the precise based path-transitivity interface
consumed by Chapter 14. These conclusions require neither an acyclic graph
nor a finite ambient completion. The marked Chapter 6--7 actions remain
explicit inputs and must be discharged by source assembly.

Source: DGS, *Groups and Graphs* (1985), definitions pp.73--74, (3.4)(c),
p.74, and (10.5)(c,d), p.156.
-/

@[expose] public noncomputable section
open Subgroup

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
local instance bOneRegularPathsAlgebra1 {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
include h c₀ c₁ hn₀ hn₁

private theorem pathExits_nonempty (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀))
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) (hp : ¬ p.Nil) :
    (pathExits p).Nonempty := by
  apply Set.nonempty_of_ncard_ne_zero
  rw [←Nat.card_coe_set_eq,pathExits_card h c₀ c₁ hn₀ hn₁ E₀ p hp]
  exact Nat.card_pos.ne'

/-- Every edge is regular in the actual source action. -/
theorem one_path_regular
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) (hp : p.IsPath)
    (hlen : p.length = 1) : PathRegular p := by
  have hf {u v : Vertex (family P)} (t : (graph (family P)).Walk u v)
      (ht : t.IsPath) (hl : t.length = 1) : PathExitTransitive t := by
    have htnil : ¬t.Nil := by rw [←length_eq_zero_iff,hl]; decide
    obtain ⟨z,hz,hnew⟩ := short_path_has_new_exit h c₀ c₁ hn₀ hn₁ E₀ t.reverse
      (by simpa only [length_reverse,hl] using (show 0 < 1 by decide))
      (by simp only [length_reverse,hl]; omega)
    change (graph (family P)).Adj u z ∧ z ≠ t.reverse.penultimate at hz
    have hnew : z ∉ t.support := by simpa only [support_reverse,List.mem_reverse] using hnew
    let e := Walk.cons hz.1.symm t
    have he : e.IsPath := ht.cons hnew
    have hl2 : e.length = 2 := by simp [e,hl]
    have hr := (short_path_regular h c₀ c₁ hn₀ hn₁ E₀ E₁ e he (Or.inl hl2)).1
    have hEx : pathExits e = pathExits t := by
      simp only [pathExits,e,penultimate_cons_of_not_nil _ _ htnil]
    intro c hc x hx
    obtain ⟨g,hg,hgx⟩ := hr c (hEx ▸ hc) x (hEx ▸ hx)
    refine ⟨g,?_,hgx⟩
    intro j hj
    have hh := hg (j+1) (by simp only [e,length_cons]; omega)
    simpa only [e,getVert_cons_succ] using hh
  exact ⟨hf p hp hlen,hf p.reverse hp.reverse (by simpa only [length_reverse] using hlen)⟩

/-- Odd stabilizers cannot be transitive on the even endpoint complement. -/
theorem not_pathExitTransitive_of_odd
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀))
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) (hp : ¬p.Nil)
    (hodd : Odd (Nat.card (pathFixer (X := G) p))) : ¬ PathExitTransitive p := by
  intro ht
  obtain ⟨z,hz⟩ := pathExits_nonempty h c₀ c₁ hn₀ hn₁ E₀ p hp
  let H := pathFixer (X := G) p
  have he : MulAction.orbit H z = pathExits p := by
    apply Set.Subset.antisymm
    · rintro _ ⟨g,rfl⟩
      exact pathFixer_preserves_exits p g g.property z hz
    · intro x hx
      obtain ⟨g,hg,hgx⟩ := ht z hz x hx
      exact ⟨⟨g,hg⟩,hgx⟩
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H z)
  rw [Nat.card_prod,he,pathExits_card h c₀ c₁ hn₀ hn₁ E₀ p hp] at hc
  have hfield : Even (Nat.card k₀) := by
    let := Fintype.ofFinite k₀
    rw [Nat.card_eq_fintype_card,even_iff_two_dvd]
    exact (CharP.cast_eq_zero_iff k₀ 2 _).mp (FiniteField.cast_card_eq_zero k₀)
  exact (Nat.not_even_iff_odd.mpr hodd) (hc ▸ hfield.mul_right _)

/-- The two b=1 branches have exactly the printed regular lengths on the source graph. -/
theorem path_regular_length_dichotomy
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    :
    (centerIn c₀.actor = ⊥ ∧ centerIn c₁.actor = ⊥ ∧
      ∀ {a b : Vertex (family P)} (p : (graph (family P)).Walk a b),
        p.IsPath → 0 < p.length → (PathRegular p ↔ p.length ≤ 3)) ∨
    (Nat.card (centerIn c₀.actor) = Nat.card k₀ ∧
      Nat.card (centerIn c₁.actor) = Nat.card k₁ ∧
      ∀ {a b : Vertex (family P)} (p : (graph (family P)).Walk a b),
        p.IsPath → 0 < p.length → (PathRegular p ↔ p.length ≤ 4)) := by
  rcases paired_center_order_dichotomy h c₀ c₁ E₀ E₁ hn₀ hn₁ with ⟨hc₀,hc₁⟩ | ⟨hc₀,hc₁⟩
  · left
    refine ⟨hc₀,hc₁,?_⟩
    intro a b p hp hpos
    constructor
    · intro hr
      by_contra hn
      exact not_pathExitTransitive_of_odd h c₀ c₁ hn₀ hn₁ E₀ p (not_nil_iff_lt_length.mpr hpos)
        (pathFixer_odd_of_four_le_of_centers_bot h c₀ c₁ hn₀ hn₁ hc₀ hc₁ p hp (by omega)) hr.1
    · intro hl
      by_cases h1 : p.length = 1
      · exact one_path_regular h c₀ c₁ hn₀ hn₁ E₀ E₁ p hp h1
      · exact short_path_regular h c₀ c₁ hn₀ hn₁ E₀ E₁ p hp (by omega)
  · right
    refine ⟨hc₀,hc₁,?_⟩
    intro a b p hp hpos
    constructor
    · intro hr
      by_contra hn
      exact not_pathExitTransitive_of_odd h c₀ c₁ hn₀ hn₁ E₀ p (not_nil_iff_lt_length.mpr hpos)
        (pathFixer_odd_of_five_le h c₀ c₁ hn₀ hn₁ p hp (by omega)) hr.1
    · intro hl
      by_cases h1 : p.length = 1
      · exact one_path_regular h c₀ c₁ hn₀ hn₁ E₀ E₁ p hp h1
      · exact short_path_regular h c₀ c₁ hn₀ hn₁ E₀ E₁ p hp (by omega)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem path_nil_regular (a : Vertex (family P)) :
    PathRegular (Walk.nil : (graph (family P)).Walk a a) := by
  have hf : PathExitTransitive (Walk.nil : (graph (family P)).Walk a a) := by
    intro z hz x hx
    obtain ⟨g,hg,he⟩ := locally_transitive (family P) hz.1 hx.1
    refine ⟨g,?_,he⟩
    intro j hj
    have : j = 0 := by simpa only [length_nil,Nat.le_zero] using hj
    subst j
    exact hg
  exact ⟨hf,hf⟩

/-- Successively align prefixes, then use the actual prefix fixer to align the next vertex. -/
theorem basedPathTransitive_of_regular_prefixes (n : ℕ)
    (hreg : ∀ {a b : Vertex (family P)} (p : (graph (family P)).Walk a b),
      p.IsPath → p.length < n → PathExitTransitive p) :
    BasedPathTransitive (X := G) (graph (family P)) n := by
  induction n with
  | zero =>
    intro a b c p q hp hq hlp hlq
    refine ⟨1,?_⟩
    intro j hj
    have : j = 0 := by omega
    subst j
    simp
  | succ n ih =>
    have ht : BasedPathTransitive (X := G) (graph (family P)) n := ih (fun {_ _} p hp hl => hreg p hp (by omega))
    intro a b c p q hp hq hlp hlq
    have hpn : ¬p.Nil := by rw [←length_eq_zero_iff,hlp]; omega
    have hqn : ¬q.Nil := by rw [←length_eq_zero_iff,hlq]; omega
    have hpl : p.dropLast.length = n := by rw [length_dropLast,hlp]; omega
    have hql : q.dropLast.length = n := by rw [length_dropLast,hlq]; omega
    obtain ⟨g,hg⟩ := ht p.dropLast q.dropLast hp.dropLast hq.dropLast hpl hql
    have hg' (j : ℕ) (hj : j ≤ n) : g • p.getVert j = q.getVert j := by
      have hh := hg j hj
      rwa [getVert_dropLast (by omega : j < p.length),getVert_dropLast (by omega : j < q.length)] at hh
    have hgp : g • p.penultimate = q.penultimate := by
      simpa only [penultimate,hlp,hlq,Nat.add_sub_cancel] using hg' n le_rfl
    have hqadj : (graph (family P)).Adj q.penultimate c := q.adj_penultimate hqn
    have hgadj : (graph (family P)).Adj q.penultimate (g • b) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr
        (p.adj_penultimate hpn)
      change (graph (family P)).Adj (g • p.penultimate) (g • b) at hh
      rwa [hgp] at hh
    have hcexit : c ∈ pathExits q.dropLast := by
      refine ⟨hqadj,?_⟩
      change c ≠ q.dropLast.penultimate
      intro he
      have hj : n-1 < q.length := by omega
      have hv : q.dropLast.penultimate = q.getVert (n-1) := by
        rw [penultimate,hql,getVert_dropLast hj]
      have hi := hq.getVert_injOn (by omega : n-1 ≤ q.length) (le_rfl : q.length ≤ q.length)
        (hv.symm.trans he.symm |>.trans q.getVert_length.symm)
      omega
    have hgexit : g • b ∈ pathExits q.dropLast := by
      refine ⟨hgadj,?_⟩
      change g • b ≠ q.dropLast.penultimate
      intro he
      have hj : n-1 < q.length := by omega
      have hv : q.dropLast.penultimate = q.getVert (n-1) := by
        rw [penultimate,hql,getVert_dropLast hj]
      have he' : b = p.getVert (n-1) := (MulAction.toPerm g).injective
        (he.trans (hv.trans (hg' (n-1) (by omega)).symm))
      have hi := hp.getVert_injOn (by omega : n-1 ≤ p.length) (le_rfl : p.length ≤ p.length)
        (he'.symm.trans p.getVert_length.symm)
      omega
    obtain ⟨t,htfix,hmove⟩ := hreg q.dropLast hq.dropLast (by omega) (g • b) hgexit c hcexit
    refine ⟨t*g,?_⟩
    intro j hj
    by_cases hle : j ≤ n
    · rw [mul_smul,hg' j hle]
      have hh := htfix j (by omega)
      rwa [getVert_dropLast (by omega : j < q.length)] at hh
    · have hje : j = n+1 := by omega
      subst j
      have hpb : p.getVert (n+1) = b := hlp ▸ p.getVert_length
      have hqc : q.getVert (n+1) = c := hlq ▸ q.getVert_length
      rw [hpb,hqc,mul_smul,hmove]

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
local instance bOneRegularPathsAlgebra2 {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
include h c₀ c₁ hn₀ hn₁

/-- The source graph contains actual paths of every length through five. -/
theorem exists_path_of_length_le_five
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (n : ℕ) (hn : n ≤ 5) :
    ∃ b : Vertex (family P), ∃ p : (graph (family P)).Walk (base (family P) false) b,
      p.IsPath ∧ p.length = n := by
  induction n with
  | zero => exact ⟨_,Walk.nil,by simp,by simp⟩
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact ⟨_,Walk.cons c₀.adjacent Walk.nil,by simpa using c₀.adjacent.ne,by simp⟩
    · obtain ⟨b,p,hp,hl⟩ := ih (by omega)
      obtain ⟨z,hz,hnew⟩ := short_path_has_new_exit h c₀ c₁ hn₀ hn₁ E₀ p (by omega) (by omega)
      change (graph (family P)).Adj b z ∧ z ≠ p.penultimate at hz
      exact ⟨z,p.concat hz.1,hp.concat hnew hz.1,by simp only [length_concat,hl]⟩

omit h c₀ c₁ hn₀ hn₁ in
/-- The maximum and minimum restricted to simple paths, over both vertex orbits.
`HasSourcePathParameters` additionally includes the closed paths allowed on DGS p.60. -/
def HasPathParameters (r s : ℕ) : Prop :=
  IsGreatest {n | ∃ a b : Vertex (family P), ∃ p : (graph (family P)).Walk a b,
    p.IsPath ∧ p.length = n ∧ PathRegular p} r ∧
  IsLeast {n | ∃ a b : Vertex (family P), ∃ p : (graph (family P)).Walk a b,
    p.IsPath ∧ p.length = n ∧ ¬PathRegular p} s

private theorem path_parameters_of_regular_lengths
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (r : ℕ) (hr : r = 3 ∨ r = 4)
    (hreg : ∀ {a b : Vertex (family P)} (p : (graph (family P)).Walk a b),
      p.IsPath → 0 < p.length → (PathRegular p ↔ p.length ≤ r)) :
    HasPathParameters (P := P) r (r+1) ∧
      BasedPathTransitive (X := G) (graph (family P)) (r+1) := by
  obtain ⟨b,p,hp,hlp⟩ := exists_path_of_length_le_five h c₀ c₁ hn₀ hn₁ E₀ r (by omega)
  obtain ⟨c,q,hq,hlq⟩ := exists_path_of_length_le_five h c₀ c₁ hn₀ hn₁ E₀ (r+1) (by omega)
  have hzero {a b : Vertex (family P)} (t : (graph (family P)).Walk a b) (hl : t.length = 0) :
      PathRegular t := by
    cases t with
    | nil => exact path_nil_regular _
    | cons ha t => simp only [length_cons] at hl; omega
  refine ⟨⟨⟨⟨_,b,p,hp,hlp,(hreg p hp (by omega)).mpr hlp.le⟩,?_⟩,
    ⟨⟨_,c,q,hq,hlq,?_⟩,?_⟩⟩,?_⟩
  · rintro n ⟨u,v,t,ht,hlt,hR⟩
    by_cases hz : t.length = 0
    · omega
    · have := (hreg t ht (by omega)).mp hR
      omega
  · intro hR
    have := (hreg q hq (by omega)).mp hR
    omega
  · rintro n ⟨u,v,t,ht,hlt,hR⟩
    have hpos : 0 < t.length := by
      by_contra hn
      exact hR (hzero t (by omega))
    have hh : ¬t.length ≤ r := by
      intro hh
      exact hR ((hreg t ht hpos).mpr hh)
    omega
  · apply basedPathTransitive_of_regular_prefixes
    intro u v t ht hlt
    by_cases hz : t.length = 0
    · exact (hzero t hz).1
    · exact ((hreg t ht (by omega)).mpr (by omega)).1

/-- The simple-path extrema and odd stabilizers in 10.5, with the same centers
and marked natural actions. `BOneClosedPaths` adds the closed-path clause. -/
theorem bOne_path_parameters
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁)) :
    (centerIn c₀.actor = ⊥ ∧ centerIn c₁.actor = ⊥ ∧
      HasPathParameters (P := P) 3 4 ∧
      BasedPathTransitive (X := G) (graph (family P)) 4 ∧
      ∀ {a b : Vertex (family P)} (p : (graph (family P)).Walk a b),
        p.IsPath → 4 ≤ p.length → Odd (Nat.card (pathFixer (X := G) p))) ∨
    (Nat.card (centerIn c₀.actor) = Nat.card k₀ ∧
      Nat.card (centerIn c₁.actor) = Nat.card k₁ ∧
      HasPathParameters (P := P) 4 5 ∧
      BasedPathTransitive (X := G) (graph (family P)) 5 ∧
      ∀ {a b : Vertex (family P)} (p : (graph (family P)).Walk a b),
        p.IsPath → 5 ≤ p.length → Odd (Nat.card (pathFixer (X := G) p))) := by
  rcases path_regular_length_dichotomy h c₀ c₁ hn₀ hn₁ E₀ E₁ with ⟨hc₀,hc₁,hr⟩ | ⟨hc₀,hc₁,hr⟩
  · obtain ⟨hpar,htrans⟩ := path_parameters_of_regular_lengths h c₀ c₁ hn₀ hn₁ E₀ 3 (Or.inl rfl) hr
    exact Or.inl ⟨hc₀,hc₁,hpar,htrans,fun {_ _} p hp hl =>
      pathFixer_odd_of_four_le_of_centers_bot h c₀ c₁ hn₀ hn₁ hc₀ hc₁ p hp hl⟩
  · obtain ⟨hpar,htrans⟩ := path_parameters_of_regular_lengths h c₀ c₁ hn₀ hn₁ E₀ 4 (Or.inr rfl) hr
    exact Or.inr ⟨hc₀,hc₁,hpar,htrans,fun {_ _} p hp hl =>
      pathFixer_odd_of_five_le h c₀ c₁ hn₀ hn₁ p hp hl⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
