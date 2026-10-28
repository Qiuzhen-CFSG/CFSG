module

public import CFSG.Quasithin.ChapterG.Section03.Source
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Orbit geometry for G.3.1

The canonical blocks are finite orbits and hence have finite-dimensional spans.
Surjectivity of their actual restriction actions identifies each block with all
nonzero vectors in its span. The restriction of a root group and its actual
kernel are kept explicit for the subsequent rank calculation.

Source: Aschbacher--Smith, Lemma G.3.1, printed pp. 337--338.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section03
open BinaryLinear BinaryTransvectionGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

namespace LocalRank

theorem block_finite (G : Subgroup (GL V)) [Finite G] (Δ : Set V)
    (i : OrbitBlock G Δ) : i.val.Finite := by
  obtain ⟨x, _, hi⟩ := i.property
  rw [hi]
  exact Finite.finite_mulAction_orbit x

instance finiteDimensional_blockSpace (G : Subgroup (GL V)) [Finite G] (Δ : Set V)
    (i : OrbitBlock G Δ) : FiniteDimensional (ZMod 2) (blockSpace G Δ i) :=
  Module.Finite.span_of_finite _ (block_finite G Δ i)

theorem block_stable (G : Subgroup (GL V)) (Δ : Set V) (i : OrbitBlock G Δ)
    (g : generated G Δ) {x : V} (hx : x ∈ i.val) : g.val x ∈ i.val := by
  obtain ⟨a, _, hi⟩ := i.property
  rw [hi] at hx ⊢
  obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hx
  exact MulAction.mem_orbit_iff.mpr ⟨g * k, rfl⟩

private theorem linear_transitive [FiniteDimensional (ZMod 2) V]
    {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) : ∃ e : GL V, e v = w := by
  let d := (LinearEquiv.coord (ZMod 2) V v hv).trans
    (LinearEquiv.coord (ZMod 2) V w hw).symm
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq d
  refine ⟨e, ?_⟩
  have hh := he ⟨v, Submodule.mem_span_singleton_self v⟩
  have hd : d ⟨v, Submodule.mem_span_singleton_self v⟩ =
      ⟨w, Submodule.mem_span_singleton_self w⟩ := by
    apply (LinearEquiv.coord (ZMod 2) V w hw).injective
    simp [d, LinearEquiv.coord_self]
  rw [hd] at hh
  exact hh.symm

/-- The points of a fully acting canonical block are exactly its nonzero vectors. -/
theorem all_points {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) (hfull : FullAction G Δ) (i : OrbitBlock G Δ) :
    i.val = {v | v ∈ blockSpace G Δ i ∧ v ≠ 0} := by
  ext v
  constructor
  · intro hv
    exact ⟨Submodule.subset_span hv, h.nonzero v (block_subset h i hv)⟩
  · rintro ⟨hv, hv0⟩
    obtain ⟨x, hx, hi⟩ := i.property
    have hxi : x ∈ i.val := hi ▸ MulAction.mem_orbit_self x
    let x' : blockSpace G Δ i := ⟨x, Submodule.subset_span hxi⟩
    let v' : blockSpace G Δ i := ⟨v, hv⟩
    have hx' : x' ≠ 0 := fun he => h.nonzero x hx (congrArg Subtype.val he)
    have hv' : v' ≠ 0 := fun he => hv0 (congrArg Subtype.val he)
    obtain ⟨e, he⟩ := linear_transitive hx' hv'
    obtain ⟨g, hg⟩ := hfull.surjective i e
    have hgv : g.val x = v := by
      have hh := congrArg (fun e : GL (blockSpace G Δ i) => (e x' : V)) hg
      exact hh.trans (congrArg Subtype.val he)
    rw [← hgv]
    exact block_stable G Δ i ⟨g.val, blockGroup_le_generated h i g.property⟩ hxi

/-- Restriction of the actual ambient root group to one of its block spaces. -/
def rootAction {G : Subgroup (GL V)} {Δ : Set V} (i : OrbitBlock G Δ)
    {x : V} (hx : x ∈ i.val) : rootGroup G x →* GL (blockSpace G Δ i) :=
  (spanAction G i.val).comp (Subgroup.inclusion (rootGroup_le_generated G hx))

@[simp] theorem rootAction_apply {G : Subgroup (GL V)} {Δ : Set V}
    (i : OrbitBlock G Δ) {x : V} (hx : x ∈ i.val) (g : rootGroup G x)
    (v : blockSpace G Δ i) : (rootAction i hx g v : V) = g.val v := rfl

theorem rootAction_ker {G : Subgroup (GL V)} {Δ : Set V}
    (i : OrbitBlock G Δ) {x : V} (hx : x ∈ i.val) :
    (rootAction i hx).ker = fixingKernel (rootGroup G x) (blockSpace G Δ i) := by
  ext g
  change rootAction i hx g = 1 ↔ ∀ v ∈ blockSpace G Δ i, g.val v = v
  constructor
  · intro hg v hv
    exact congrArg (fun e : GL (blockSpace G Δ i) => (e ⟨v, hv⟩ : V)) hg
  · intro hg
    ext v
    exact hg v v.property

/-- Restriction preserves the rank-one displacement and the fixed center. -/
theorem rootAction_range_le_radical {G : Subgroup (GL V)} {Δ : Set V}
    (i : OrbitBlock G Δ) {x : V} (hx : x ∈ i.val) :
    (rootAction i hx).range ≤ radical (centerLine
      (⟨x, Submodule.subset_span hx⟩ : blockSpace G Δ i)) := by
  rintro _ ⟨g, rfl⟩
  refine ⟨?_, ?_⟩
  · intro v hv
    apply Subtype.ext
    apply g.property.2.1
    rcases (mem_centerLine_iff _ v).mp hv with rfl | rfl
    · exact Submodule.zero_mem _
    · exact Submodule.mem_span_singleton_self x
  · intro v
    apply (mem_centerLine_iff _ _).mpr
    rcases (mem_centerLine_iff x (g.val v - v)).mp (g.property.2.2 v) with hh | hh
    · exact Or.inl (Subtype.ext hh)
    · exact Or.inr (Subtype.ext hh)

end LocalRank
end CFSG.Quasithin.ChapterG.Section03
