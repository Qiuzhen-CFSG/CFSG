module

public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.ThreeAutomorphisms
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic

/-!
# Intrinsic outer actions on binary minimal parabolics

Automorphism coverage in dimensions three through five identifies every
outer automorphism with inverse transpose composed with an inner automorphism.
The actual flag geometry then forces a preserved minimal parabolic to be the
middle node in dimension four. When a full Sylow flag is preserved, its nodes
are reversed, including the inner adjustment. Two distinct individually
preserved minimal parabolics containing a common Sylow force the action to
be inner, even when their original bases differ.

These are the automorphism deductions in Aschbacher–Smith 13.8.25,
printed pp.959–960 (PDF pp.976–977) of `refs/quasithin.pdf`.
-/

public section

namespace BinaryLinear.InvariantNodeActions
open OuterCyclic

/-- Inner/inverse-transpose coverage in all three source dimensions. -/
theorem smallDimension_inner_graph {n : ℕ} (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (a : MulAut (LinearGroup n)) :
    ∃ g : LinearGroup n, a = MulAut.conj g ∨ a = graphLinear n * MulAut.conj g := by
  by_cases hn : n = 3
  · subst n
    exact ThreeAutomorphisms.inner_graph a
  · exact OuterCyclic.inner_graph (by omega) a

/-- The non-inner case uses the actual inverse transpose, with its inner adjustment. -/
theorem outer_eq_graph_inner {n : ℕ} (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (a : MulAut (LinearGroup n)) (ha : a ∉ MulAut.innerSubgroup _) :
    ∃ g : LinearGroup n, a = graphLinear n * MulAut.conj g := by
  obtain ⟨g, hg | hg⟩ := smallDimension_inner_graph hn₀ hn₁ a
  · exact (ha ⟨g, hg.symm⟩).elim
  · exact ⟨g, hg⟩

/-- An outer automorphism preserving the full flag reverses every marked node. -/
theorem outer_reverses_minimalParabolic {m : ℕ} (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4)
    (b : Basis m) (a : MulAut (LinearGroup (m + 1)))
    (ha : a ∉ MulAut.innerSubgroup _)
    (hB : (cutStabilizer b Set.univ).map a.toMonoidHom = cutStabilizer b Set.univ)
    (i : Fin m) :
    (minimalParabolic b i).map a.toMonoidHom = minimalParabolic b i.rev := by
  obtain ⟨g, rfl⟩ := outer_eq_graph_inner (by omega) (by omega) a ha
  exact graph_inner_reverses_minimalParabolic b g hB i

/-- A preserved minimal parabolic has omitted dimension two in dimension four. -/
theorem outer_preserves_minimalParabolic_middle {m : ℕ}
    (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4) (b : Basis m) (i : Fin m)
    (a : MulAut (LinearGroup (m + 1))) (ha : a ∉ MulAut.innerSubgroup _)
    (hP : (minimalParabolic b i).map a.toMonoidHom = minimalParabolic b i) :
    m = 3 ∧ i.val + 1 = 2 := by
  obtain ⟨g, rfl⟩ := outer_eq_graph_inner (by omega) (by omega) a ha
  have h := graph_inner_preserves_minimalParabolic_middle b i g hP
  omega

/-- Individual preservation of two distinct parabolics over a common Sylow is inner. -/
theorem preserving_two_minimalParabolics_is_inner {m : ℕ}
    (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4) (b c : Basis m) (i j : Fin m)
    (T : Sylow 2 (LinearGroup (m + 1)))
    (hTP : (T : Subgroup (LinearGroup (m + 1))) ≤ minimalParabolic b i)
    (hTQ : (T : Subgroup (LinearGroup (m + 1))) ≤ minimalParabolic c j)
    (hne : minimalParabolic b i ≠ minimalParabolic c j)
    (a : MulAut (LinearGroup (m + 1)))
    (hP : (minimalParabolic b i).map a.toMonoidHom = minimalParabolic b i)
    (hQ : (minimalParabolic c j).map a.toMonoidHom = minimalParabolic c j) :
    a ∈ MulAut.innerSubgroup _ := by
  by_contra ha
  obtain ⟨g, rfl⟩ := outer_eq_graph_inner (by omega) (by omega) a ha
  exact graph_inner_not_preserves_two_minimalParabolics b c i j T g hTP hTQ hne ⟨hP, hQ⟩

end BinaryLinear.InvariantNodeActions
