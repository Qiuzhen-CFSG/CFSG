module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Transvections

/-!
# Point radicals for binary automorphism reconstruction

The radical of a one-dimensional subspace remembers that subspace through
its common fixed vectors. Over the binary field a line has a unique nonzero
vector, so distinct points give distinct radicals.

`PreservesPointRadicals` states a geometric property of an actual group
automorphism. Proving this property after a possible inverse transpose,
and proving that this property forces an inner automorphism, are separate
obligations. The definitions here do not assume either assertion.

Source: the binary specialization of GLS3, Theorem 2.5.12 and §2.7,
`refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115.
-/

@[expose] public section

namespace BinaryLinear.OuterCyclic

/-- The point radical consists of maps fixing the line through `v` pointwise
and acting trivially modulo that line. -/
def pointRadical (n : ℕ) (v : Space n) : Subgroup (LinearGroup n) :=
  radical (Submodule.span (ZMod 2) {v})

/-- An automorphism carries each nonzero point radical to a point radical. -/
def PreservesPointRadicals {n : ℕ} (a : MulAut (LinearGroup n)) : Prop :=
  ∀ v : Space n, v ≠ 0 → ∃ w : Space n, w ≠ 0 ∧
    (pointRadical n v).map a.toMonoidHom = pointRadical n w

theorem pointRadical_injective {n : ℕ} {v w : Space n} (hv : v ≠ 0) (hw : w ≠ 0)
    (he : pointRadical n v = pointRadical n w) : v = w := by
  have hw0 : Submodule.span (ZMod 2) {w} ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hw
  have hmem : v ∈ Submodule.span (ZMod 2) {w} := by
    apply (mem_iff_fixed_radical hw0 v).mpr
    intro g hg
    have hg' : g ∈ pointRadical n v := he.symm ▸ hg
    exact hg'.1 v (Submodule.mem_span_singleton_self v)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have ha0 : a ≠ 0 := by
    intro hz
    exact hv (by simpa [hz] using ha.symm)
  have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
  simpa [ha1] using ha.symm

end BinaryLinear.OuterCyclic
