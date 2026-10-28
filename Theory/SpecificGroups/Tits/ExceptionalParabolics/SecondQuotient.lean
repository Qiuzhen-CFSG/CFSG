module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.Embedding
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Geometry
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The second Tits two-core and its marked linear quotient

The canonical Atlas embedding sends all eight positive Parrott generators into
the positive fixed matrix subgroup and the second reflection into the linear
seed. Restricting it to the second parabolic and composing with the full-Ree
projection therefore gives a homomorphism to the genuine PSL₂(2).

Its kernel is a two-group. The local Sylow normalizer makes the intrinsic
two-core a proper subgroup of the Sylow group of order 2048, so its order is
at most 1024. The parabolic order 6144 and target order six force surjectivity.
The target has trivial two-core, which identifies the kernel intrinsically
and gives its exact order. The quotient equivalence keeps the full-Ree
projection's formula on representatives.

Source: Aschbacher--Smith, F.1.12(I)(9), printed p.263 (PDF p.274), and
14.2.21, printed pp.988--989; Parrott (1972), p.683, with generator conventions
in `refs/original/n-group-global/parrott-tits-presentation.md`.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds Subgroup
open ReeF4.DerivedTits.Realization
open ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates

private theorem pair_mem (i : Fin 4) : pairElement i ∈ splitUnipotent 0 := by
  rw [pairElement_eq]
  apply Subgroup.mul_mem
  all_goals exact subset_closure ⟨_, _, ((rootBlocks .positive).roots (.inl (i, _))).property, rfl⟩

private theorem quartet_mem (i : Fin 4) : quartetElement i ∈ splitUnipotent 0 := by
  rw [quartetElement_eq]
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    all_goals exact subset_closure ⟨_, _, ((rootBlocks .positive).roots (.inr (i, _))).property, rfl⟩
  · exact subset_closure ⟨_, _, ((rootBlocks .positive).roots (.inr (i, _))).property, rfl⟩

private theorem u_mem (i : Fin 8) : u i ∈ splitUnipotent 0 := by
  fin_cases i
  · exact quartet_mem 0
  · exact pair_mem 1
  · exact quartet_mem 3
  · exact pair_mem 3
  · exact quartet_mem 1
  · exact pair_mem 2
  · exact quartet_mem 2
  · exact pair_mem 0

private theorem positive_assignment_mem (i : ParrottGenerator) (h1 : i ≠ .r1) (h8 : i ≠ .r8) :
    assignment i ∈ splitUnipotent 0 := by
  cases i with
  | r1 => exact (h1 rfl).elim
  | r8 => exact (h8 rfl).elim
  | s1 | s3 | s5 => exact Subgroup.mul_mem _ (u_mem _) (u_mem _)
  | s2 | s4 | s6 | s8 => exact u_mem _
  | s7 => exact Subgroup.mul_mem _ (u_mem _) (Subgroup.inv_mem _ (u_mem _))

/-- The positive Atlas marking lies in the positive fixed matrix subgroup. -/
theorem atlasEmbedding_sylow_le : S ≤ FullRee.S.comap FullRee.atlasEmbedding := by
  rw [S, atlas1600SylowTwoSubgroup_eq]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    change toSplitGroup 0 (FullRee.atlasEmbedding _) ∈ splitUnipotent 0
    rw [FullRee.atlasEmbedding_generator_matrix]
    exact positive_assignment_mem _ (by decide) (by decide)

/-- The canonical Atlas embedding respects the marked second parabolic. -/
theorem atlasEmbedding_second_le : second ≤ FullRee.second.comap FullRee.atlasEmbedding := by
  apply sup_le
  · exact atlasEmbedding_sylow_le.trans (Subgroup.comap_mono FullRee.sylow_le_second)
  · apply (Subgroup.closure_le _).mpr
    rintro x (rfl : x = atlas1600ParrottAssignment .r8)
    change toSplitGroup 0 (FullRee.atlasEmbedding _) ∈ splitSeed 0 .linear
    rw [FullRee.atlasEmbedding_generator_matrix]
    have hw := Binary.FixedGeometry.weylLift_mem_seed 0 .linear
    change toSplitGroup 0 (Binary.FixedGeometry.weylLift 0 .linear) ∈ splitSeed 0 .linear at hw
    rw [Binary.FixedGeometry.toSplitGroup_weylLift] at hw
    exact hw

/-- Restriction of the marked embedding to the second parabolic. -/
def secondEmbedding : second →* FullRee.second :=
  (FullRee.atlasEmbedding.comp second.subtype).codRestrict FullRee.second
    (fun x => atlasEmbedding_second_le x.property)

@[simp] theorem secondEmbedding_coe (x : second) :
    (secondEmbedding x : Model 0) = FullRee.atlasEmbedding x := rfl

theorem secondEmbedding_injective : Function.Injective secondEmbedding := by
  intro x y h
  exact Subtype.ext (FullRee.atlasEmbedding_injective (congrArg Subtype.val h))

/-- The full-Ree projection restricted along the fixed marked embedding. -/
def secondProjection : second →* LargeLocalSeeds.LinearQuotient 0 :=
  FullRee.secondProjection.comp secondEmbedding

@[simp] theorem secondProjection_apply (x : second) :
    secondProjection x = FullRee.secondProjection (secondEmbedding x) := rfl

private theorem kernel_isPGroup : IsPGroup 2 secondProjection.ker := by
  have h : secondProjection.ker = (pCore 2 FullRee.second).comap secondEmbedding := by
    rw [← FullRee.secondProjection_ker]
    rfl
  rw [h]
  exact pCore_isPGroup.comap_of_injective secondEmbedding secondEmbedding_injective

private theorem core_card_le : Nat.card (pCore 2 second) ≤ 1024 := by
  have hle : pCore 2 second ≤ S.subgroupOf second := by
    rw [← secondSylowTwo_coe]
    exact pCore_isPGroup.le_sylow_of_normal secondSylowTwo
  have hne : pCore 2 second ≠ S.subgroupOf second := by
    intro he
    have hn : (S.subgroupOf second).Normal := he ▸ inferInstance
    have ht : S.subgroupOf second = ⊤ := by
      rw [← second_sylow_normalizer]
      exact Subgroup.normalizer_eq_top _
    have hi := second_sylow_index
    rw [ht, Subgroup.index_top] at hi
    contradiction
  have hi : 2 ≤ (pCore 2 second).relIndex (S.subgroupOf second) := by
    have hpos : (pCore 2 second).relIndex (S.subgroupOf second) ≠ 0 := by
      intro h
      exact (pCore 2 second).index_ne_zero_of_finite
        ((pCore 2 second).index_eq_zero_of_relIndex_eq_zero h)
    have hnot : (pCore 2 second).relIndex (S.subgroupOf second) ≠ 1 := by
      intro h
      exact hne (le_antisymm hle (Subgroup.relIndex_eq_one.mp h))
    omega
  have hidx := Subgroup.relIndex_mul_index hle
  rw [second_sylow_index] at hidx
  have hc := (pCore 2 second).card_mul_index
  rw [second_card, ← hidx] at hc
  nlinarith

private theorem target_card : Nat.card (LargeLocalSeeds.LinearQuotient 0) = 6 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := CoefficientField 0) 2
  rw [show Nat.card (CoefficientField 0) = 2 by simpa using field_card 0] at h
  norm_num [Fin.prod_univ_succ] at h
  exact h

/-- Surjectivity follows from the local core bound and the literal target order. -/
theorem secondProjection_surjective : Function.Surjective secondProjection := by
  have hle : secondProjection.ker ≤ pCore 2 second :=
    le_sSup ⟨inferInstance, kernel_isPGroup⟩
  have hk : Nat.card secondProjection.ker ≤ 1024 :=
    (Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)).trans core_card_le
  have hr : Nat.card secondProjection.range ≤ 6 := by
    rw [← target_card]
    exact Nat.card_le_card_of_injective _ secondProjection.range.subtype_injective
  have hm := secondProjection.ker.card_mul_index
  rw [Subgroup.index_ker, second_card] at hm
  have he : Nat.card secondProjection.range = Nat.card (LargeLocalSeeds.LinearQuotient 0) := by
    rw [target_card]
    nlinarith
  exact MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq _ he)

/-- The kernel is the intrinsic two-core of the Atlas second parabolic. -/
theorem secondProjection_ker : secondProjection.ker = pCore 2 second := by
  have h := secondProjection.comap_pCore_of_ker_isPGroup
    secondProjection_surjective kernel_isPGroup
  simpa only [Binary.linear_twoCore_eq_bot, MonoidHom.comap_bot] using h

/-- The second core has the source order 2^10. -/
theorem second_core_card : Nat.card (pCore 2 second) = 1024 := by
  have h := secondProjection.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr secondProjection_surjective,
    Subgroup.card_top, target_card, secondProjection_ker, second_card] at h
  omega

/-- The quotient is the genuine PSL₂ over the binary Ree field. -/
def secondCoreQuotientEquiv :
    (second ⧸ pCore 2 second) ≃* LargeLocalSeeds.LinearQuotient 0 :=
  (QuotientGroup.quotientMulEquivOfEq secondProjection_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective secondProjection secondProjection_surjective)

@[simp] theorem secondCoreQuotientEquiv_mk (x : second) :
    secondCoreQuotientEquiv (QuotientGroup.mk' (pCore 2 second) x) =
      FullRee.secondProjection (secondEmbedding x) := rfl

end Tits.ExceptionalParabolics
