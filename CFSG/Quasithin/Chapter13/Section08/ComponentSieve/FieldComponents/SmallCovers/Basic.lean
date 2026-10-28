module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.BinaryOffender.Basic
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.Commutator.ConjugateSpan

/-!
# The fixed-space and residual deductions for the small covers

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 13.8.21(2), printed pp.955–956 (combined manuscript, 1 March 2004).

In the M₂₂ branch the irreducible rank-two seed is fixed by the two-core
of L₁T. The parabolic fixed-space comparison and the code-module fixed
line then give a dimension contradiction. The comparison and code-module
identification are still inputs: this is not a proof of the M₂₂ exclusion
from the standing source hypotheses alone.

For the cover branches we define Y using the two-residual of the literal
preimage of Z(K/O₂(K)). Characteristicity gives its relative normality and
excludes Y = L₀ using N_G(L₀) = M. The solvable-overgroup argument excluding
Y = L₁, identification Y = L₁,+, reduction through K₁, the module recognition,
and the terminal contradiction on the actual U_H remain assembly obligations.
The complete actual-isomorphism catalogue is owned by LocalAnalysis.Components.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers
open Subgroup Representation.BinaryOffender

variable {G : Type*} [Group G]

/-- O²(O₂,Z(X)), as an intrinsic subgroup of X. The inner operation is
preimage of the center after O₂, not the center of O₂(X). -/
def coverResidual (X : Type*) [Group X] : Subgroup X :=
  (pResidual 2 (centralPreimage (pCore 2 X))).map
    (centralPreimage (pCore 2 X)).subtype

instance coverResidual_characteristic (X : Type*) [Group X] :
    (coverResidual X).Characteristic := by
  unfold coverResidual
  infer_instance

/-- The literal ambient subgroup Y attached to K. -/
def coverResidualIn (K : Subgroup G) : Subgroup G :=
  (coverResidual K).map K.subtype

theorem coverResidualIn_le (K : Subgroup G) : coverResidualIn K ≤ K :=
  map_subtype_le _

/-- Relative normality suffices; no normality of K in G is imposed. -/
theorem normalizes_coverResidualIn (H K : Subgroup G) (hKH : K ≤ H)
    [(K.subgroupOf H).Normal] : H ≤ normalizer (coverResidualIn K : Set G) :=
  (le_normalizer_of_normal_subgroupOf hKH).trans
    (normalizer_le_normalizer_characteristic_image K (coverResidual K))

/-- Relative normality of the actual residual image. -/
theorem coverResidualIn_normal (H K : Subgroup G) (hKH : K ≤ H)
    [(K.subgroupOf H).Normal] : ((coverResidualIn K).subgroupOf H).Normal :=
  normal_subgroupOf_of_le_normalizer (normalizes_coverResidualIn H K hKH)

/-- A seed identity before quotienting propagates to its actual H-conjugate
span. This requires the displayed equality for V₃ itself; an equality only
after dividing by V₁ is not silently strengthened. Y remains intrinsic. -/
theorem UH_eq_commutator_coverResidual (H K V₃ : Subgroup G) (hKH : K ≤ H)
    [(K.subgroupOf H).Normal] (hseed : V₃ = ⁅V₃, coverResidualIn K⁆) :
    Source.UH H V₃ = ⁅Source.UH H V₃, coverResidualIn K⁆ :=
  conjugateSpanBy_eq_commutator_of_seed V₃ H (coverResidualIn K)
    (coverResidualIn K) ((coverResidualIn_le K).trans hKH)
    (normalizes_coverResidualIn H K hKH) le_rfl hseed

/-- The source's normalizer identity rules out Y = L₀. -/
theorem coverResidualIn_ne_L0 (H K L₀ M : Subgroup G) (hKH : K ≤ H)
    [(K.subgroupOf H).Normal] (hHM : ¬ H ≤ M)
    (hnorm : normalizer (L₀ : Set G) = M) : coverResidualIn K ≠ L₀ := by
  intro heq
  have hn := normalizes_coverResidualIn H K hKH
  rw [heq, hnorm] at hn
  exact hHM hn

/-- A subgroup of a four-group whose binary rank exceeds one is the whole
four-group. This is the use of 13.8.18(4), without any action conclusion. -/
theorem eq_four_of_rank_gt_one [Finite G] (A R : Subgroup G)
    (hAR : A ≤ R) (hR : Nat.card R = 4) (hA : 1 < rank A) : A = R := by
  apply Subgroup.eq_of_le_of_card_ge hAR
  rw [hR]
  exact Nat.pow_le_of_le_log (Nat.card_pos.ne') (show 2 ≤ Nat.log 2 (Nat.card A) from hA)

section Seed
variable [Finite G]
variable {I S : Type*} [AddCommGroup I] [Module (ZMod 2) I]
    [FiniteDimensional (ZMod 2) I] [AddCommGroup S] [Module (ZMod 2) S]
    [FiniteDimensional (ZMod 2) S]

omit [FiniteDimensional (ZMod 2) I] in
/-- An irreducible seed is fixed by the intrinsic two-core of its actual
parabolic actor. The equivariant map embeds it in the component module. -/
theorem seed_le_fixedSpace_twoCore (ρ : Representation (ZMod 2) G I)
    (P : Subgroup G) (σ : Representation (ZMod 2) P S)
    [Representation.IsIrreducible σ] (e : S →ₗ[ZMod 2] I)
    (he : ∀ p s, e (σ p s) = ρ p.val (e s)) :
    e.range ≤ fixedSpace ρ (P.pCoreIn 2) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk := Representation.normal_p_subgroup_le_ker σ (pCore 2 P)
    (pCore_isPGroup (p := 2))
  rintro _ ⟨s, rfl⟩ ⟨_, p, hp, rfl⟩
  change ρ p.val (e s) = e s
  rw [← he, show σ p = 1 from hk hp]
  rfl

/-- The terminal M₂₂ dimension contradiction, retaining the actual two
parabolic actors and an equivariant rank-two seed. H.16.2(1) supplies the
fixed-line dimension after the code-module and subgroup identifications. -/
theorem no_rank_two_seed_in_parabolic_fixed_line
    (ρ : Representation (ZMod 2) G I) (P Q : Subgroup G)
    (σ : Representation (ZMod 2) P S) [Representation.IsIrreducible σ]
    (e : S →ₗ[ZMod 2] I) (hinj : Function.Injective e)
    (he : ∀ p s, e (σ p s) = ρ p.val (e s))
    (hseed : Module.finrank (ZMod 2) S = 2)
    (hcompare : fixedSpace ρ (P.pCoreIn 2) ≤ fixedSpace ρ (Q.pCoreIn 2))
    (hline : Module.finrank (ZMod 2) (fixedSpace ρ (Q.pCoreIn 2)) = 1) : False := by
  have hle := Submodule.finrank_mono
    ((seed_le_fixedSpace_twoCore ρ P σ e he).trans hcompare)
  rw [LinearMap.finrank_range_of_inj hinj, hseed, hline] at hle
  omega

end Seed
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers
