module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.Preparation
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.InnerActors
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.SchurOuter

/-!
# The cubic degree argument for K.3.3

The source cubic actor in the full linear normalizer of the central-cover
pullback gives binary degree at most `6*s`. An actor moving the Schur field
already gives this bound, including the endpoint `s = 2`. Otherwise the
Schur-linear outer exclusion places the actor in the literal action image,
where the inner root-geometric estimate applies. All actor estimates are
discharged, without assuming the pullback faithful or the normalizer SQTK.

Combining with the independently proved lower bound gives degree exactly
`6*s`. Natural-module recognition remains a separate representation theorem.

Source: Aschbacher--Smith, printed pp.451, 456; Guralnick--Malle II,
Theorem 4.10, Proposition 4.11 and Table 7.
-/

public section
open BenderSuzuki.MatrixGroups Representation Subgroup
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree

variable {F V G : Type*} [Field F] [Finite F] [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
  (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  (h : SourceHypotheses ρ L) (π : J.specialSubgroup →* L)
  (hπ : Function.Surjective π) (hker : π.ker ≤ center J.specialSubgroup)

include hs hcard hconj h hπ hker

/-- The numerical upper bound in K.3.3 for the original binary module and
the specified surjective central SU₃ cover. Both inner and outer actors,
the endpoint `s = 2`, and possible central covering kernels are retained. -/
theorem source_degree_le : Module.finrank (ZMod 2) V ≤ 6 * s := by
  rcases source_degree_le_or_inner_actor J hs hcard hconj h π hπ hker with hd | ha
  · exact hd
  · obtain ⟨A, hA, _, hc, hinner⟩ := ha
    exact source_degree_le_of_inner_actor J hs hcard hconj h π hπ hker A hA hc hinner

/-- The exact binary degree in K.3.3, before natural-module recognition or
injectivity of the central covering map has been established. -/
theorem source_degree_eq : Module.finrank (ZMod 2) V = 6 * s :=
  Nat.le_antisymm (source_degree_le J hs hcard hconj h π hπ hker)
    (source_degree_lower J h π hπ hs hcard hconj)

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree
