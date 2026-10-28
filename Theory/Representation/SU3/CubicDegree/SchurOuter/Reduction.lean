module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.Literal
public import Theory.Representation.SU3.CubicDegree.SchurOuter.Models

/-!
# Assembly of the two outer unitary steps

The normalizer two-rank is at most s+1. The adjoint fixed-space bound 3s is
strictly greater than twice this rank when s>2. At s=2 it also excludes actors
of rank at most one; the separate rank-at-least-two bound gives codimension
at least eight, while twice the rank is at most six. Thus every actor induces
inner conjugation. The literal lifting theorem then removes all scalar
ambiguity and puts the actual operators in the image.

The graph-stable model reduction and its adjoint fixed-space bounds remain
explicit premises. These conditional theorems do not discharge either source
step of Guralnick--Malle II, Proposition 4.11, internal pp.31--32.
-/

public section
open BenderSuzuki.MatrixGroups Representation Representation.BinaryOffender
open Subgroup
namespace Representation.SU3.CubicDegree.SchurOuter
variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
  (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
  (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]
  (hk : σ.ker ≤ center J.specialSubgroup)

include hs hcard hconj hk

/-- Conditional assembly with the two independent source steps explicit. -/
theorem actor_le_image_of_adjoint_steps
    (hmodels : GraphStableReduction J σ s) (hbounds : AdjointFixedSpaceBounds J σ s)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hcu : IsCubic (normalizerRepresentation σ) A)
    (hc : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A)
    (hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t) :
    A ≤ (actionImage σ).subgroupOf (linearNormalizer σ) := by
  apply (elementary_le_image_iff_inner σ inferInstance A hA.2).mpr
  intro t ht
  by_contra hn
  have hm := hmodels A hA hcu hc hl t ht hn
  obtain ⟨hthree, htwo⟩ := hbounds hm A hA hl t ht hn
  have hr := elementary_rank_le J hs hcard hconj σ inferInstance hk A hA
  by_cases hs2 : s = 2
  · by_cases ha : 2 ≤ rank A
    · have hb := htwo hs2 ha
      omega
    · omega
  · omega

/-- The equivalent strict obstruction, with the same source obligations. -/
theorem strict_fixedCodim_of_adjoint_steps
    (hmodels : GraphStableReduction J σ s) (hbounds : AdjointFixedSpaceBounds J σ s)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hcu : IsCubic (normalizerRepresentation σ) A)
    (hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t)
    (ho : ¬ A ≤ (actionImage σ).subgroupOf (linearNormalizer σ)) :
    2 * rank A < fixedCodim (normalizerRepresentation σ) A := by
  by_contra! hc
  exact ho (actor_le_image_of_adjoint_steps J hs hcard hconj σ hk
    hmodels hbounds A hA hcu hc hl)

end Representation.SU3.CubicDegree.SchurOuter
