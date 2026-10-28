module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.MixedPathRegularity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneClosedPaths

/-!
# Source path extrema in odd-valence graphs

Five-walk transitivity and odd longer fixers give regularity exactly through
length four. This is transferred to the literal DGS path convention, which
allows the last vertex to repeat the first: every such path is nonbacktracking
except for the closed two-edge return, whose fixer and exits equal those of
its edge. A regular simple path has no exit in its support, so actual simple
paths realize lengths four and five. Thus the exact source extrema are r=4
and s=5, and all source paths of length at least five have odd fixers.

Only odd valences at least three, the proved short regularity, and the
odd long-walk fixers are used. No tree or girth hypothesis is added.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
path convention p.60, regularity and extrema pp.73--74, (11.7)(f), (11.8)(g), pp.174--177.
UnitaryPathParameters applies the result to the original full-Borel branch.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.Walk SimpleGraph.BasedWalk
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.WeakBNPair.RegularTree
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open NoncommutingProfile

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

private theorem nb_reverse {V : Type*} {Γ : SimpleGraph V} {a b : V}
    (p : Γ.Walk a b) (hp : (ofWalk p).Nonbacktracking) :
    (ofWalk p.reverse).Nonbacktracking := by
  rw [nb_ofWalk_iff] at hp ⊢
  intro i hi
  rw [length_reverse] at hi
  simp only [getVert_reverse]
  convert (hp (p.length-(i+2)) (by omega)).symm using 1
  congr 1
  omega

namespace OddValenceSourceGeometry
variable {G : Type*} [Group G] (P : Fin 2 → Subgroup G)
local notation "F" => family P
local notation "M" => G
local notation "α" => base F false
variable (hval : ∀ v : Vertex (family P),
      3 ≤ Nat.card ((graph (family P)).neighborSet v) ∧
      Odd (Nat.card ((graph (family P)).neighborSet v)))
    (hreg : ∀ {n : ℕ} {a : Vertex (family P)} (p : BasedWalk (graph (family P)) n a),
      p.Nonbacktracking → (Regular (A := G) p ↔ n ≤ 4))
    (hodd : ∀ {a b : Vertex (family P)} (p : (graph (family P)).Walk a b), 5 ≤ p.length →
      (∀ i, i+2 ≤ p.length → p.getVert i ≠ p.getVert (i+2)) →
        Odd (Nat.card (pathFixer (X := G) p)))

include hval hreg hodd

omit hval hodd in
private theorem short_walk_exit_transitive {a b : Vertex F} (p : (graph F).Walk a b)
    (hp : (ofWalk p).Nonbacktracking) (hl : p.length ≤ 4) : PathExitTransitive p := by
  have hr := (hreg (ofWalk p) hp).mpr hl
  intro z hz w hw
  obtain ⟨g,hg,hgw⟩ := hr.2 z w ((forward_ofWalk p).mpr hz) ((forward_ofWalk p).mpr hw)
  refine ⟨g,?_,hgw⟩
  rw [mem_pathFixer_support]
  intro y hy
  exact hg y (by rw [vertices_ofWalk]; exact hy)

omit hreg in
private theorem long_walk_not_regular {a b : Vertex F} (p : (graph F).Walk a b)
    (hp : (ofWalk p).Nonbacktracking) (hl : 5 ≤ p.length) : ¬ PathRegular p := by
  have ho := hodd p hl
    ((nb_ofWalk_iff p).mp hp)
  have hval := hval b
  let : Finite ((graph F).neighborSet b) := Nat.finite_of_card_ne_zero
    (by have := hval.1; omega)
  have hcard := card_pathExit p (by rw [←length_eq_zero_iff]; omega)
  have heven : Even (Nat.card (pathExits p)) := by
    change Even (Nat.card (pathExit p))
    obtain ⟨k,hk⟩ := hval.2
    exact ⟨k,by omega⟩
  have hpos : 0 < Nat.card (pathExits p) := by
    change 0 < Nat.card (pathExit p)
    have := hval.1
    omega
  obtain ⟨z,hz⟩ := Set.nonempty_of_ncard_ne_zero (s := pathExits p)
    (by rw [←Nat.card_coe_set_eq]; omega)
  intro hr
  have he : MulAction.orbit (pathFixer (X := M) p) z = pathExits p := by
    apply Set.Subset.antisymm
    · rintro _ ⟨g,rfl⟩
      exact pathFixer_preserves_exits p g g.property z hz
    · intro w hw
      obtain ⟨g,hg,hgw⟩ := hr.1 z hz w hw
      exact ⟨⟨g,hg⟩,hgw⟩
  have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (pathFixer (X := M) p) z)
  rw [Nat.card_prod,he] at hh
  exact (Nat.not_even_iff_odd.mpr ho) (hh ▸ heven.mul_right _)

omit hval hreg hodd in
private theorem source_path_nb {a b : Vertex F} (p : (graph F).Walk a b)
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

omit hval hodd in
private theorem closed_two_regular {a : Vertex F} (p : (graph F).Walk a a)
    (hl : p.length = 2) : PathRegular p := by
  cases p with
  | nil => simp at hl
  | cons hab t =>
    cases t with
    | nil => simp at hl
    | cons hba t =>
      cases t with
      | cons h t => simp only [length_cons] at hl; omega
      | nil =>
        have ht := short_walk_exit_transitive P hreg
          (Walk.cons hba Walk.nil) trivial (by simp)
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

/-- Exact regularity with the literal DGS p.60 path convention, including
the allowed closed two-edge return. -/
theorem source_path_regular_iff {a b : Vertex F} (p : (graph F).Walk a b)
    (hp : IsSourcePath p) : PathRegular p ↔ p.length ≤ 4 := by
  by_cases htwo : p.length = 2
  · have hr : PathRegular p := by
      rcases hp with hp | ⟨he,_⟩
      · have hnb := nonbacktracking_ofWalk_of_isPath p hp
        exact ⟨short_walk_exit_transitive P hreg p hnb (by omega),
          short_walk_exit_transitive P hreg p.reverse
            (nb_reverse p hnb) (by rw [length_reverse]; omega)⟩
      · subst b
        exact closed_two_regular P hreg p htwo
    exact ⟨fun _ => by omega,fun _ => hr⟩
  have hnb := source_path_nb P p hp htwo
  constructor
  · intro hr
    by_contra hn
    exact long_walk_not_regular P hval hodd p hnb (by omega) hr
  · intro hl
    exact ⟨short_walk_exit_transitive P hreg p hnb hl,
      short_walk_exit_transitive P hreg p.reverse
        (nb_reverse p hnb) (by rwa [length_reverse])⟩


omit hodd in
private theorem short_path_extension {a b : Vertex F} (p : (graph F).Walk a b)
    (hp : p.IsPath) (hl : p.length ≤ 4) :
    ∃ z, ∃ haz : (graph F).Adj b z, (p.concat haz).IsPath := by
  by_cases hn : p.Nil
  · cases hn
    obtain ⟨z,hz,hza⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph F).neighborSet a)
      (by rw [←Nat.card_coe_set_eq]; exact lt_of_lt_of_le (by decide) (hval a).1) a
    exact ⟨z,hz,Walk.IsPath.concat hp (by simpa using hza) hz⟩
  let : Finite ((graph F).neighborSet b) := Nat.finite_of_card_ne_zero
    (by have := (hval b).1; omega)
  have hcard := card_pathExit p hn
  have hvalb := (hval b).1
  have hlarge : 1 < (pathExits p).ncard := by
    rw [←Nat.card_coe_set_eq]
    change 1 < Nat.card (pathExit p)
    omega
  obtain ⟨z,hz⟩ := Set.nonempty_of_ncard_ne_zero (s := pathExits p) (by omega)
  have hnew : z ∉ p.support := by
    intro hzs
    obtain ⟨w,hw,hwz⟩ := Set.exists_ne_of_one_lt_ncard hlarge z
    obtain ⟨g,hg,hgw⟩ := short_walk_exit_transitive P hreg p
      (nonbacktracking_ofWalk_of_isPath p hp) hl z hz w hw
    have hfix := (mem_pathFixer_support p g).mp hg z hzs
    exact hwz (hgw.symm.trans hfix)
  exact ⟨z,hz.1,hp.concat hnew hz.1⟩

omit hodd in
/-- Actual simple paths realize every length through five. The endpoint
transitivity prevents an exit from revisiting an earlier fixed vertex. -/
theorem source_exists_short_path (n : ℕ) (hn : n ≤ 5) :
    ∃ b : Vertex F, ∃ p : (graph F).Walk α b, p.IsPath ∧ p.length = n := by
  induction n with
  | zero => exact ⟨α,Walk.nil,by simp,by simp⟩
  | succ n ih =>
    obtain ⟨b,p,hp,hl⟩ := ih (by omega)
    obtain ⟨z,haz,hpath⟩ := short_path_extension P hval hreg p hp (by omega)
    exact ⟨z,p.concat haz,hpath,by rw [length_concat,hl]⟩

/-- The literal DGS extrema from short regularity and odd longer fixers: both DGS path extrema,
including closed source paths, and odd stabilizers at every length at least five. -/
theorem source_path_parameters :
    HasSourcePathParameters (P := P) 4 5 ∧
      ∀ {a b : Vertex F} (p : (graph F).Walk a b), IsSourcePath p → 5 ≤ p.length →
        Odd (Nat.card (pathFixer (X := M) p)) := by
  obtain ⟨b,p,hp,hlp⟩ := source_exists_short_path P hval hreg 4 (by decide)
  obtain ⟨c,q,hq,hlq⟩ := source_exists_short_path P hval hreg 5 (by decide)
  have hr {a b : Vertex F} (p : (graph F).Walk a b) (hp : IsSourcePath p) :=
    source_path_regular_iff P hval hreg hodd p hp
  refine ⟨⟨⟨⟨α,b,p,Or.inl hp,hlp,(hr p (Or.inl hp)).mpr hlp.le⟩,?_⟩,
    ⟨⟨α,c,q,Or.inl hq,hlq,?_⟩,?_⟩⟩,?_⟩
  · rintro n ⟨a,b,t,ht,hlt,hreg⟩
    have := (hr t ht).mp hreg
    omega
  · intro hh
    have := (hr q (Or.inl hq)).mp hh
    omega
  · rintro n ⟨a,b,t,ht,hlt,hnot⟩
    have hn : ¬t.length ≤ 4 := fun hn => hnot ((hr t ht).mpr hn)
    omega
  · intro a b t ht hl
    exact hodd t hl
      ((nb_ofWalk_iff t).mp (source_path_nb P t ht (by omega)))

end OddValenceSourceGeometry

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
