module

public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.SpecificGroups.Triality.FullParabolicActions.Definitions
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Restrictions on every subnormal candidate in a triality parabolic

For a relatively subnormal subgroup X of a genuine full triality parabolic,
its two-core is its intersection with the root radical. Thus its quotient
by that core is the actual image of X in the full Levi complement. Its
commutator layer is computed from the same intersection, not from the core
of the entire parabolic.

If X is short, subnormality and two-perfection force the whole external
radical commutator into U(X). Consequently every element of that commutator
has square one. These restrictions include the central node at q = 2 and
do not equate X with either a parabolic or its prime-to-two residual.

Source: Aschbacher–Smith C.1.7/C.1.12, pp.123–124, and E.6.8, pp.247–248;
GLS3 §2.6. The root radicals and actual Levi projections are supplied by
`Triality.ParabolicLocalStructure` and `Triality.FullParabolicActions.Definitions`.
-/

@[expose] public section
noncomputable section

open Subgroup
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open scoped commutatorElement

namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry.IntrinsicBlocks

variable (P : Parameters) (hp : P.prime = 2) (a : Node)
include hp

/-- The intrinsic two-core of every subnormal candidate is its intersection
with the actual root radical. -/
theorem candidate_twoCore (X : Subgroup (parabolic P a)) (hs : X.IsSubnormal) :
    pCore 2 X = ((radical P a).subgroupOf (parabolic P a)).comap X.subtype := by
  rw [pCore_subnormal_eq_comap 2 hs, parabolic_twoCore_eq P hp a]

/-- The core quotient of a candidate is its actual full-Levi image. This
is not an identification with the whole Levi or the local factor. -/
def candidateQuotientEquivLeviImage (X : Subgroup (parabolic P a)) (hs : X.IsSubnormal) :
    X ⧸ pCore 2 X ≃* X.map (fullLeviProjection P hp a) := by
  let f := (fullLeviProjection P hp a).subgroupMap X
  have hk : f.ker = pCore 2 X := by
    rw [Subgroup.ker_subgroupMap, fullLeviProjection_ker,
      candidate_twoCore P hp a X hs]
    rfl
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((fullLeviProjection P hp a).subgroupMap_surjective X))

/-- The quotient equivalence is induced by the actual Levi projection. -/
@[simp] theorem candidateQuotientEquivLeviImage_mk
    (X : Subgroup (parabolic P a)) (hs : X.IsSubnormal) (x : X) :
    (candidateQuotientEquivLeviImage P hp a X hs
      (QuotientGroup.mk' (pCore 2 X) x)).val = fullLeviProjection P hp a x := rfl

/-- Subnormality survives projection onto the full Levi. -/
theorem candidate_leviImage_subnormal (X : Subgroup (parabolic P a))
    (hs : X.IsSubnormal) : (X.map (fullLeviProjection P hp a)).IsSubnormal :=
  hs.map (fullLeviProjection_surjective P hp a)

/-- No two-core is lost inside the candidate's full-Levi image. -/
theorem candidate_leviImage_twoCore (X : Subgroup (parabolic P a))
    (hs : X.IsSubnormal) : pCore 2 (X.map (fullLeviProjection P hp a)) = ⊥ := by
  rw [pCore_subnormal_eq_comap 2 (candidate_leviImage_subnormal P hp a X hs),
    fullLevi_twoCore_eq_bot P hp a, MonoidHom.comap_bot]
  exact (MonoidHom.ker_eq_bot_iff _).mpr (Subgroup.subtype_injective _)

/-- Compute the candidate's own U-layer in its parabolic. -/
theorem candidate_blockU_map (X : Subgroup (parabolic P a)) (hs : X.IsSubnormal) :
    (ChapterC.blockU X).map X.subtype =
      ⁅X ⊓ (radical P a).subgroupOf (parabolic P a), X⁆ := by
  rw [ChapterC.blockU, map_commutator, candidate_twoCore P hp a X hs,
    map_comap_eq, range_subtype, ← MonoidHom.range_eq_map, range_subtype]

/-- The external radical action lies in the candidate's intrinsic U-layer. -/
theorem radical_commutator_le_candidate_blockU (X : Subgroup (parabolic P a))
    (hs : X.IsSubnormal) (htwo : IsPPerfect 2 X) :
    ⁅(radical P a).subgroupOf (parabolic P a), X⁆ ≤
      (ChapterC.blockU X).map X.subtype := by
  rw [← parabolic_twoCore_eq P hp a]
  exact commutator_le_core_commutator_of_isSubnormal X (pCore 2 (parabolic P a))
    hs htwo pCore_isPGroup le_normalizer_of_normal

/-- Two-perfection identifies the external radical commutator with the
candidate's own U-layer, through its actual embedding in the parabolic. -/
theorem radical_commutator_eq_candidate_blockU (X : Subgroup (parabolic P a))
    (hs : X.IsSubnormal) (htwo : IsPPerfect 2 X) :
    ⁅(radical P a).subgroupOf (parabolic P a), X⁆ =
      (ChapterC.blockU X).map X.subtype := by
  apply le_antisymm (radical_commutator_le_candidate_blockU P hp a X hs htwo)
  rw [candidate_blockU_map P hp a X hs]
  exact commutator_mono inf_le_right le_rfl

/-- Shortness makes every element of the whole external commutator square
one, not only each individual root commutator. -/
theorem short_radical_commutator_square (X : Subgroup (parabolic P a))
    (hs : X.IsSubnormal) (hb : ChapterC.IsShort X) {x : parabolic P a}
    (hx : x ∈ ⁅(radical P a).subgroupOf (parabolic P a), X⁆) : x ^ 2 = 1 := by
  obtain ⟨u, hu, rfl⟩ := radical_commutator_le_candidate_blockU P hp a X hs hb.twoPerfect hx
  have he := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    hb.elementary.exponent_dvd_p (⟨u, hu⟩ : ChapterC.blockU X)
  exact congrArg (fun v : ChapterC.blockU X => ((v : X) : parabolic P a)) he

/-- Pointwise conjugation restriction on every candidate, including candidates
whose intrinsic quotient has order three at q = 2. -/
theorem short_radical_action_square (X : Subgroup (parabolic P a))
    (hs : X.IsSubnormal) (hb : ChapterC.IsShort X)
    (r : parabolic P a) (hr : r.val ∈ radical P a)
    (x : parabolic P a) (hx : x ∈ X) : (⁅r, x⁆ : parabolic P a) ^ 2 = 1 :=
  short_radical_commutator_square P hp a X hs hb (commutator_mem_commutator hr hx)

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry.IntrinsicBlocks
