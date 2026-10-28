module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SourcePathExtrema
public import Theory.GroupTheory.WeakBNPair.RegularTree.RootRegularity

/-!
# Odd-valence geometry for the strict source profile

Short regularity on the literal DGS source paths gives simple paths through
length seven: a transitive path fixer cannot have an exit in the fixed
support. Conversely, an odd long-path fixer cannot act transitively on the
positive even exit set at an odd-valence vertex. These two arguments
discharge the extension and nonregularity inputs of `SourcePathExtrema`.

The local action's regularity through length six and odd fixers from length
seven remain explicit; no residual or model assertion is assumed implicitly.

Source: DGS, *Groups and Graphs* (1985), pp.60, 73--74 and (10.10), p.164.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.Walk
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open NoncommutingProfile

namespace OddValenceSourceGeometry
variable {G : Type*} [Group G] (P : Fin 2 → Subgroup G)
local notation "F" => family P
local notation "α" => base F false

/-- Regular simple paths of length at most six have a new endpoint exit. -/
theorem strict_short_path_extension
    (hval : ∀ v : Vertex F, 3 ≤ Nat.card ((graph F).neighborSet v))
    (hreg : ∀ {a b : Vertex F} (p : (graph F).Walk a b),
      IsSourcePath p → p.length ≤ 6 → PathRegular p)
    {a b : Vertex F} (p : (graph F).Walk a b)
    (hp : p.IsPath) (hl : p.length ≤ 6) :
    ∃ z, ∃ haz : (graph F).Adj b z, (p.concat haz).IsPath := by
  by_cases hn : p.Nil
  · cases hn
    obtain ⟨z, hz, hza⟩ := Set.exists_ne_of_one_lt_ncard
      (s := (graph F).neighborSet a)
      (by rw [← Nat.card_coe_set_eq]; exact lt_of_lt_of_le (by decide) (hval a)) a
    exact ⟨z, hz, Walk.IsPath.concat hp (by simpa using hza) hz⟩
  let : Finite ((graph F).neighborSet b) :=
    Nat.finite_of_card_ne_zero (by have := hval b; omega)
  have hcard := card_pathExit p hn
  have hlarge : 1 < (pathExits p).ncard := by
    rw [← Nat.card_coe_set_eq]
    change 1 < Nat.card (pathExit p)
    have := hval b
    omega
  obtain ⟨z, hz⟩ := Set.nonempty_of_ncard_ne_zero
    (s := pathExits p) (by omega)
  have hnew : z ∉ p.support := by
    intro hzs
    obtain ⟨w, hw, hwz⟩ := Set.exists_ne_of_one_lt_ncard hlarge z
    obtain ⟨g, hg, hgw⟩ := (hreg p (Or.inl hp) hl).1 z hz w hw
    obtain ⟨j, rfl, hj⟩ := mem_support_iff_exists_getVert.mp hzs
    exact hwz (hgw.symm.trans (hg j hj))
  exact ⟨z, hz.1, hp.concat hnew hz.1⟩

/-- An odd path fixer on an odd-valence graph cannot be regular once
its walk has positive length. -/
theorem strict_long_path_not_regular
    (hval : ∀ v : Vertex F, 3 ≤ Nat.card ((graph F).neighborSet v) ∧
      Odd (Nat.card ((graph F).neighborSet v)))
    {a b : Vertex F} (p : (graph F).Walk a b) (hl : 0 < p.length)
    (ho : Odd (Nat.card (pathFixer (X := G) p))) : ¬ PathRegular p := by
  have hv := hval b
  let : Finite ((graph F).neighborSet b) :=
    Nat.finite_of_card_ne_zero (by have := hv.1; omega)
  have hcard := card_pathExit p (by rw [← length_eq_zero_iff]; omega)
  have heven : Even (Nat.card (pathExits p)) := by
    change Even (Nat.card (pathExit p))
    obtain ⟨k, hk⟩ := hv.2
    exact ⟨k, by omega⟩
  have hpos : 0 < Nat.card (pathExits p) := by
    change 0 < Nat.card (pathExit p)
    have := hv.1
    omega
  obtain ⟨z, hz⟩ := Set.nonempty_of_ncard_ne_zero (s := pathExits p)
    (by rw [← Nat.card_coe_set_eq]; omega)
  intro hr
  have he : MulAction.orbit (pathFixer (X := G) p) z = pathExits p := by
    apply Set.Subset.antisymm
    · rintro _ ⟨g, rfl⟩
      exact pathFixer_preserves_exits p g g.property z hz
    · intro w hw
      obtain ⟨g, hg, hgw⟩ := hr.1 z hz w hw
      exact ⟨⟨g, hg⟩, hgw⟩
  have hh := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (pathFixer (X := G) p) z)
  rw [Nat.card_prod, he] at hh
  exact (Nat.not_even_iff_odd.mpr ho) (hh ▸ heven.mul_right _)

/-- The strict source extrema follow from short regularity and odd long
fixers; simple extensions and long nonregularity are proved here. -/
theorem source_path_parameters_six_seven
    (hval : ∀ v : Vertex F, 3 ≤ Nat.card ((graph F).neighborSet v) ∧
      Odd (Nat.card ((graph F).neighborSet v)))
    (hreg : ∀ {a b : Vertex F} (p : (graph F).Walk a b),
      IsSourcePath p → p.length ≤ 6 → PathRegular p)
    (hodd : ∀ {a b : Vertex F} (p : (graph F).Walk a b),
      IsSourcePath p → 7 ≤ p.length →
        Odd (Nat.card (pathFixer (X := G) p))) :
    HasSourcePathParameters (P := P) 6 7 ∧
      ∀ {a b : Vertex F} (p : (graph F).Walk a b),
        IsSourcePath p → 7 ≤ p.length →
          Odd (Nat.card (pathFixer (X := G) p)) := by
  have hbad {a b : Vertex F} (p : (graph F).Walk a b)
      (hp : IsSourcePath p) (hl : 7 ≤ p.length) : ¬ PathRegular p :=
    strict_long_path_not_regular P hval p (by omega) (hodd p hp hl)
  have hexists : ∀ n : ℕ, n ≤ 7 →
      ∃ b : Vertex F, ∃ p : (graph F).Walk α b,
        p.IsPath ∧ p.length = n := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨α, Walk.nil, by simp, by simp⟩
    | succ n ih =>
        intro hn
        obtain ⟨b, p, hp, hlen⟩ := ih (by omega)
        obtain ⟨z, haz, hnext⟩ := strict_short_path_extension P
          (fun v => (hval v).1) hreg p hp (by omega)
        exact ⟨z, p.concat haz, hnext, by simp only [length_concat, hlen]⟩
  obtain ⟨b, p, hp, hpl⟩ := hexists 6 (by decide)
  obtain ⟨c, q, hq, hql⟩ := hexists 7 (by decide)
  exact DGS85.source_path_parameters_six_seven hreg
    (fun t ht hl => hbad t ht hl) hodd
    ⟨α, b, p, hp, hpl, hreg p (Or.inl hp) (by omega)⟩
    ⟨α, c, q, Or.inl hq, hql, hbad q (Or.inl hq) (by omega)⟩

end OddValenceSourceGeometry
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
