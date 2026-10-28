module

public import Theory.GroupAction.CubicTree.Tracks
public import Theory.GroupTheory.FiniteSubgroupFiltration
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Pointwise track fixers and finite realizing segments

The track fixer is the literal pointwise stabilizer of the integer line.
The track translation normalizes it. With finite vertex stabilizers, every
forward ray has the same fixer as the entire track, and the descending finite
segment fixers eventually reach this subgroup. The last step reuses the finite
subgroup filtration theorem.

This is the finite-stabilizer argument behind the maximal subarc in
Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.1), printed p.394.
The same literal fixer occurs in the central-involution intervals of Section 6.
-/

@[expose] public section
open Subgroup SimpleGraph
namespace Theory.GroupAction.CubicTree.Track
variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable (t : Track Γ G)

def fixer : Subgroup G := fixingSubgroup G (Set.range t.vertex)

@[simp] theorem mem_fixer {g : G} : g ∈ t.fixer ↔ ∀ i, g • t.vertex i = t.vertex i := by
  simp only [fixer, mem_fixingSubgroup_iff, Set.forall_mem_range]

theorem fixer_le_stabilizer (i : ℤ) : t.fixer ≤ MulAction.stabilizer G (t.vertex i) :=
  fun _ hg => (t.mem_fixer.mp hg) i

instance finite_fixer [Finite (MulAction.stabilizer G (t.vertex 0))] : Finite t.fixer :=
  Finite.of_injective (Subgroup.inclusion (t.fixer_le_stabilizer 0))
    (Subgroup.inclusion_injective _)

theorem fixer_eq_rayFixer
    (hfin : ∀ i, Finite (MulAction.stabilizer G (t.vertex i))) (a : ℤ) :
    t.fixer = t.rayFixer a := by
  apply le_antisymm
  · intro g hg i hi
    exact t.mem_fixer.mp hg i
  · intro g hg
    exact t.mem_fixer.mpr (t.fixes_all_of_fixes_ray hfin hg)

theorem translation_mem_normalizer_fixer :
    t.translation ∈ normalizer (t.fixer : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    apply t.mem_fixer.mpr
    intro i
    rw [mul_smul, mul_smul, t.inverse_translate, t.mem_fixer.mp hg, t.translate]
    congr 1
    omega
  · intro hg
    apply t.mem_fixer.mpr
    intro i
    have he := t.mem_fixer.mp hg (i+2)
    rw [mul_smul, mul_smul, t.inverse_translate] at he
    rw [show i + 2 - 2 = i by omega, ← t.translate i] at he
    exact (MulAction.toPerm t.translation).injective he

def segmentFixer (a : ℤ) (n : ℕ) : Subgroup G :=
  fixingSubgroup G (t.vertex '' Set.Icc a (a+n))

@[simp] theorem mem_segmentFixer {a : ℤ} {n : ℕ} {g : G} :
    g ∈ t.segmentFixer a n ↔ ∀ i, a ≤ i → i ≤ a+n → g • t.vertex i = t.vertex i := by
  simp only [segmentFixer, mem_fixingSubgroup_iff, Set.forall_mem_image,
    Set.mem_Icc, and_imp]

theorem segmentFixer_antitone (a : ℤ) : Antitone (t.segmentFixer a) := by
  intro n m hnm g hg
  rw [mem_segmentFixer] at hg ⊢
  intro i hai hin
  exact hg i hai (by omega)

@[simp] theorem segmentFixer_zero (a : ℤ) :
    t.segmentFixer a 0 = MulAction.stabilizer G (t.vertex a) := by
  ext g
  rw [mem_segmentFixer]
  constructor
  · intro hg
    exact hg a le_rfl (by simp)
  · intro hg i hai hia
    change g • t.vertex a = t.vertex a at hg
    have : i = a := by omega
    simpa only [this] using hg

theorem fixer_le_segmentFixer (a : ℤ) (n : ℕ) : t.fixer ≤ t.segmentFixer a n := by
  intro g hg
  exact t.mem_segmentFixer.mpr (fun i _ _ => t.mem_fixer.mp hg i)

theorem iInf_segmentFixer (a : ℤ) : (⨅ n, t.segmentFixer a n) = t.rayFixer a := by
  ext g
  simp only [mem_iInf, mem_segmentFixer]
  constructor
  · intro hg i hai
    exact hg (i-a).toNat i hai (by omega)
  · intro hg n i hai hin
    exact hg i hai

theorem segmentFixer_stabilizes
    (hfin : ∀ i, Finite (MulAction.stabilizer G (t.vertex i))) (a : ℤ) :
    ∃ N : ℕ, ∀ n, N ≤ n → t.segmentFixer a n = t.fixer := by
  have : Finite (t.segmentFixer a 0) := by rw [t.segmentFixer_zero]; exact hfin a
  obtain ⟨N, hN⟩ := Subgroup.finite_filtration_stabilizes _ (t.segmentFixer_antitone a)
  exact ⟨N, fun n hn => (hN n hn).trans
    ((t.iInf_segmentFixer a).trans (t.fixer_eq_rayFixer hfin a).symm)⟩

end Theory.GroupAction.CubicTree.Track
