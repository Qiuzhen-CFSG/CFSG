module

public import CFSG.Quasithin.ChapterG.Section09.Basic
public import Theory.Representation.Triality.PrimitiveDegree

/-!
# The triality exclusion in G.9 for exponents at least two

The original G.9 representation restricts faithfully to its component and,
through the specified triality isomorphism, to the genuine binary carrier.
The primitive-prime argument gives `12*n ≤ d` on this same vector space.
The original elementary abelian actor gives the upper bound
`d ≤ 2*(primeRank 2 (MulAut L) + 1)`. Transporting the explicit model rank
estimate along the same isomorphism gives `d ≤ 10*n + 2`, a contradiction
for `n ≥ 2`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.356
(PDF p.367, `refs/quasithin.pdf`). The automorphism-rank estimate remains an
explicit input; there is no representation-degree premise. At `n = 1`, the
primitive-prime bound is only twelve and does not exclude the source case.
The stronger general `24*n` degree bound and the endpoint require separate
representation-theoretic arguments.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

/-- The `n ≥ 2` triality branch is impossible under the model automorphism-rank
estimate. The degree bound is proved for the actual faithfully restricted action. -/
theorem not_triality_of_primitive_degree
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} (hn : 2 ≤ n)
    (model : Triality.Standard.IsTrialityGroupAt (2 ^ n) L)
    (hrank : primeRank 2
      (MulAut (Triality.Standard.BinaryCarrier n (by omega))) ≤ 5 * n) : False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff L n (by omega)).mp model
  have hdegree := Triality.PrimitiveDegree.finrank_ge n (by omega)
    ((ρ.comp L.subtype).comp e.symm.toMonoidHom)
    ((h.faithful.comp L.subtype_injective).comp e.symm.injective)
  have hupper := h.single_component_degree_bound
  rw [Theory.GroupTheory.primeRank_equiv 2 (MulAut.congr e)] at hupper
  omega

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
