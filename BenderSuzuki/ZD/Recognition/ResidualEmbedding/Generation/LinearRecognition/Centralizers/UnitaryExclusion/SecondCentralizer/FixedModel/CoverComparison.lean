module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.AmbientTorus
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Generation.Comparison
public import Theory.SpecificGroups.SU3.Quasisimplicity

/-!
# Comparing the two unitary covers before identifying fixed points

If the second distinguished centralizer F lay in Lᵤ, the equal-parameter
central-quotient comparison would imply F = Lᵤ. Since F centralizes B, the
assumed identity C_{Lᵤ}(B) = L B would then give Lᵤ = L B. Perfectness removes
the central factor B, contradicting L < Lᵤ. Distinguished generation therefore
also excludes a trivial action of u on F.

The comparison retains the full center of either SU₃ or PSU₃; no equality
of their unquotiented orders is asserted.
Source: GLS4, Chapter 2, final paragraph of Lemma 13.2.
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion.FixedModel
open Subgroup Theory.GroupTheory _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {n : ℕ}

private def centerQuotientCongr {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    (H ⧸ center H) ≃* (K ⧸ center K) :=
  QuotientGroup.congr (center H) (center K) e (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact MulEquivClass.apply_mem_center e hx
    · intro hy
      exact ⟨e.symm y, MulEquivClass.apply_mem_center e.symm hy, e.apply_symm_apply y⟩)

private theorem cover_facts (hn : 2 ≤ n) (hG : IsUnitaryCentralizerCoverAt n G) :
    commutator G = ⊤ ∧ IsSimpleBenderGroupAtExponent n (G ⧸ center G) := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, hm⟩ := hG
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  have hconj := External.huppert_II_10_4_conj_eq_frobenius J (2 ^ n) hcard hfixed
  have hz := HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hcard hconj
  rcases hm with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · let := J.projective_isPerfect_of_fixed_card hq hcard hfixed
    let := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    refine ⟨Group.IsPerfect.commutator_eq_top, .isPSU3 ?_⟩
    exact ⟨E, inferInstance, inferInstance, J, hJ, hcard, hfixed,
      ⟨(centerQuotientCongr e).trans
        ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)⟩⟩
  · let := J.special_isPerfect_of_fixed_card hq hcard hfixed
    let := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    refine ⟨Group.IsPerfect.commutator_eq_top, .isPSU3 ?_⟩
    exact ⟨E, inferInstance, inferInstance, J, hJ, hcard, hfixed,
      ⟨(centerQuotientCongr e).trans
        ((QuotientGroup.quotientMulEquivOfEq (J.specialToProjective_ker_eq_center hz).symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective
            J.specialToProjective_surjective))⟩⟩

/-- Unitary covers at the same field parameter cannot be properly nested.
The comparison is on the quotients by their full centers. -/
public theorem cover_eq_of_le (hn : 2 ≤ n) (H K : Subgroup G) (hle : H ≤ K)
    (hH : IsUnitaryCentralizerCoverAt n H) (hK : IsUnitaryCentralizerCoverAt n K) : H = K := by
  have hh : IsUnitaryCentralizerCoverAt n (H.subgroupOf K) := by
    obtain ⟨E, _, _, J, hJ, hc, hf, hm⟩ := hH
    refine ⟨E, inferInstance, inferInstance, J, hJ, hc, hf, ?_⟩
    rcases hm with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl ⟨(subgroupOfEquivOfLe hle).trans e⟩
    · exact Or.inr ⟨(subgroupOfEquivOfLe hle).trans e⟩
  obtain ⟨hp, hq⟩ := cover_facts hn hK
  have he := TwoGeneratorComparison.unitary_subgroup_eq_top_of_bender_quotient
    (H.subgroupOf K) hn hp hq hh
  have hm := congrArg (Subgroup.map K.subtype) he
  simpa only [map_subgroupOf_eq_of_le hle, ← MonoidHom.range_eq_map, range_subtype] using hm

variable {Z : Set G} {M : Subgroup G} {z t u : G}
/-- The torus-centralizer identity and perfectness exclude containment of
the second distinguished centralizer in the first unitary cover. -/
public theorem second_not_le_first (hn : 2 ≤ n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hCB : centralizerClosure Z u ⊓ centralizer (ambientFixedTorus Z M t u : Set G) =
      residualGenerated M z t ⊔ ambientFixedTorus Z M t u)
    (hc : IsUnitaryCentralizerCoverAt n
      (distinguishedCentralizer Z (ambientFixedTorus Z M t u))) :
    ¬ distinguishedCentralizer Z (ambientFixedTorus Z M t u) ≤ centralizerClosure Z u := by
  intro hle
  let F := distinguishedCentralizer Z (ambientFixedTorus Z M t u)
  let U := centralizerClosure Z u
  let L := residualGenerated M z t
  let B := ambientFixedTorus Z M t u
  have he : F = U := cover_eq_of_le hn F U hle hc (hunitary u huD hu).2
  have hUC : U ≤ centralizer (B : Set G) := by
    rw [← he]
    exact (closure_le _).mpr (fun _ hx => hx.2)
  have hgen : L ⊔ B = U := hCB.symm.trans (inf_eq_left.mpr hUC)
  have hBC : B ≤ centralizer (U : Set G) := by
    intro b hb x hx
    exact (mem_centralizer_iff.mp (hUC hx) b hb).symm
  have hp : ⁅U, U⁆ = U := by
    have hp : commutator U = ⊤ := (cover_facts hn (hunitary u huD hu).2).1
    have hm := congrArg (Subgroup.map U.subtype) hp
    simpa only [U.map_subtype_commutator, ← MonoidHom.range_eq_map, range_subtype] using hm
  have hUL : U ≤ L := by
    rw [← hp, commutator_eq_of_central_supplement hgen hBC]
    exact commutator_le_self L
  exact (hunitary u huD hu).1.not_ge hUL

/-- Conjugation by u acts nontrivially on the second distinguished
centralizer. Pointwise fixation would put every distinguished generator in Lᵤ. -/
public theorem second_action_nontrivial (h : IsProductDisconnected Z M) (hn : 2 ≤ n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hCB : centralizerClosure Z u ⊓ centralizer (ambientFixedTorus Z M t u : Set G) =
      residualGenerated M z t ⊔ ambientFixedTorus Z M t u)
    (hc : IsUnitaryCentralizerCoverAt n
      (distinguishedCentralizer Z (ambientFixedTorus Z M t u))) :
    (distinguishedCentralizer Z (ambientFixedTorus Z M t u)).normalizerMonoidHom
      ⟨u, ambientFixedTorus_second_normalizes h⟩ ≠ 1 := by
  intro he
  apply second_not_le_first hn hunitary huD hu hCB hc
  apply (closure_le _).mpr
  intro x hx
  apply Subgroup.subset_closure
  refine ⟨hx.1, mem_centralizer_singleton_iff.mpr ?_⟩
  have hh := congrArg (fun a : MulAut (distinguishedCentralizer Z
    (ambientFixedTorus Z M t u)) => ((a ⟨x, Subgroup.subset_closure hx⟩).val : G)) he
  change u * x * u⁻¹ = x at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm
end BenderSuzuki.ZD.UnitaryExclusion.FixedModel
