module

public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.CentralizerConjugateGeneration

/-!
# Abelian conjugate spans and normal centralizers

An abelian conjugate span of a self-centralizing subgroup equals its seed.
Consequently its conjugating group normalizes the seed. A normal subgroup
centralizing a seed centralizes its whole conjugate span.

These are the elementary centralizer arguments used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 1 March 2004 manuscript,
13.6.6 and 13.6.12, printed pp.927 and 929.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- The two existing constructions of the centralizer conjugate span agree. -/
public theorem centralizerConjugateClosure_eq_conjugateSpanBy (V : Subgroup G) (z : G) :
    centralizerConjugateClosure V z = conjugateSpanBy V (centralizer ({z} : Set G)) := by
  rw [centralizerConjugateClosure_eq_closure, conjugateSpanBy]
  congr 1
  ext x
  constructor
  · rintro ⟨c, v, hv, he⟩
    exact ⟨c, c.property, v, hv, he⟩
  · rintro ⟨c, hc, v, hv, he⟩
    exact ⟨⟨c, hc⟩, v, hv, he⟩

/-- Subgroups of an abelian conjugate span are abelian, including spans
under smaller groups of conjugators. -/
public theorem conjugateSpanBy_isMulCommutative_of_le
    {V W H K : Subgroup G} (hVW : V ≤ W) (hHK : H ≤ K)
    [IsMulCommutative (conjugateSpanBy W K)] :
    IsMulCommutative (conjugateSpanBy V H) := by
  apply le_centralizer_iff_isMulCommutative.mp
  have h := conjugateSpanBy_mono hVW hHK
  exact h.trans ((le_centralizer _).trans (centralizer_le h))

/-- An abelian conjugate span cannot enlarge a self-centralizing seed. -/
public theorem conjugateSpanBy_eq_of_abelian_selfCentralizing
    (V H : Subgroup G) [IsMulCommutative (conjugateSpanBy V H)]
    (hC : centralizer (V : Set G) ≤ V) : conjugateSpanBy V H = V := by
  apply le_antisymm _ (le_conjugateSpanBy V H)
  exact ((le_centralizer _).trans
    (centralizer_le (le_conjugateSpanBy V H))).trans hC

/-- The conjugating group normalizes a self-centralizing seed with abelian span. -/
public theorem le_normalizer_of_abelian_conjugateSpanBy
    (V H : Subgroup G) [IsMulCommutative (conjugateSpanBy V H)]
    (hC : centralizer (V : Set G) ≤ V) : H ≤ normalizer (V : Set G) := by
  have h := le_normalizer_conjugateSpanBy V H
  rwa [conjugateSpanBy_eq_of_abelian_selfCentralizing V H hC] at h

/-- Relative normality propagates centralization of the seed to its span. -/
public theorem le_centralizer_conjugateSpanBy_of_normalizes
    (X Z H : Subgroup G) (hN : H ≤ normalizer (X : Set G))
    (hC : X ≤ centralizer (Z : Set G)) :
    X ≤ centralizer (conjugateSpanBy Z H : Set G) := by
  apply le_centralizer_iff.mpr
  apply (closure_le _).mpr
  rintro _ ⟨h, hh, z, hz, rfl⟩
  apply mem_centralizer_iff.mpr
  intro x hx
  have hx' : h⁻¹ * x * h ∈ X := by
    simpa using (mem_normalizer_iff.mp (hN (H.inv_mem hh)) x).mp hx
  have he := mem_centralizer_iff.mp (hC hx') z hz
  have he' := congrArg (fun y : G => h * y * h⁻¹) he
  simpa [mul_assoc] using he'.symm

end Subgroup
