module

public import CFSG.Quasithin.Chapter12.Section06.CentralLine.Coordinates
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.WeakClosure

/-!
# Eliminating the central line: intersection and weak-closure bridges

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemmas 12.6.19–23, printed pp.828–830
(PDF pp.845–847).

The proved bridges retain L-controlled element fusion, the TI property in M,
actual conjugate intersections and centralizer transport. The seven-dimensional
core and six-dimensional natural quotient have separate linear markings and
weight-four predicates. The intrinsic bound on weight-four subspaces gives
respectively r(G,V) ≥ 4 and r(G,V) ≥ 3. An escaping centralizer transports to
all of the weight-four orbit. The actual E.3 centralizer span normalizes Vᵍ,
and the first two clauses of 12.6.22 imply W₁ ≤ C_T(V) and w(G,V) > 1.

This is not yet the full source implication. It still needs the proof of
12.6.19 (including its odd-index clause), the nontrivial-commutator alternative
12.6.20(4), the permutation deduction of 12.6.22(1–2), and the construction
and A₅-action contradiction for the genuine local H* in 12.6.23. In particular,
no theorem here asserts C_V(L)=1. Source assembly must supply fusion rather
than assume it, discharge the intrinsic permutation premises, apply the full
12.2.13 alternatives to obtain escape, and instantiate the earlier 12.2, 12.3
and E.3 source results. Final assembly remains in this module's owning task.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06.CentralLine
open Subgroup ChapterE BinaryPermutation
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The concrete bridge consumed by the permutation contradiction in 12.6.22:
every nonidentity vector in the literal [A,U] has weight four. The rank
premise for the E.3 span argument is discharged by the marked core calculation. -/
theorem core_centralizerSpan_weightFour
    {L V M A : Subgroup G} [IsElementaryAbelian 2 V]
    (e : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hbound : ∀ X : Submodule (ZMod 2) (core (Fin 8)),
      (∀ x ∈ X, x ≠ 0 → coreWeightFour x) → Module.finrank (ZMod 2) X ≤ 3)
    (hL : L ≤ normalizer (V : Set G)) (hf : ControlsElementFusion L V)
    (hTI : HasTIConjugatesIn V M)
    (hC : ∀ v ∈ V, v ≠ 1 → v ∉ markedVectors e coreWeightFour →
      centralizer ({v} : Set G) ≤ M)
    {g : G} (hg : g ∉ normalizer (V : Set G))
    (hA : A ≤ V.map (MulAut.conj g).toMonoidHom)
    (hAN : A ≤ normalizer (V : Set G)) :
    ∀ v ∈ ⁅A, centralizerSpan V A g⁆, v ≠ 1 → v ∈ markedVectors e coreWeightFour := by
  obtain ⟨hi, hr⟩ := core_intersections_and_globalR e hbound hL hf hTI hC
  intro v hv hv1
  exact (hi g hg).1 v (commutator_centralizerSpan_le hA hAN hr hv) hv1

end CFSG.Quasithin.Chapter12.Section06.CentralLine
