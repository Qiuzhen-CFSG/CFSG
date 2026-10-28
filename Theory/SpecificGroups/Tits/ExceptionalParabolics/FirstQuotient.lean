module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.Embedding
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Orders
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.LongRoot

/-!
# The first Tits parabolic has two-core 512 and quotient Sz(2)

The canonical root-marked Atlas embedding sends the eight Sylow generators
into the positive fixed subgroup and `r1` to the Suzuki Weyl lift. It therefore
restricts to the actual first parabolic. Compose this restriction with the
full-Ree Suzuki projection, retaining both maps in the quotient formula.

Its kernel is a two-group because the embedding is injective and the full
projection has two-group kernel. The word `s5 = u₁ u₅` projects to the order-four
Levi element `u₁`: the other factor lies in the Suzuki radical. Thus four divides
the image order. Five also divides it, since the domain has order 10240 and the
kernel is a two-group. The target is the concrete Sz(2) carrier of order twenty,
so the projection is onto. Its target has trivial two-core, identifying its
kernel with the intrinsic O₂, whose order is consequently 512.

This proves the positive calculation for the full marked first Tits parabolic.
It retains the correction to the incompatible 1024/D₁₀ package printed in
Aschbacher--Smith F.1.12(I)(9), p.263 (PDF p.274). Compare 14.2.20--21,
pp.988--989, and Parrott, *A Characterization of the Tits' Simple Group* (1972),
p.672. The explicit root words use Parrott's §5 marking, p.683.
-/

@[expose] public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
open ReeF4.DerivedTits.Realization
open ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
open Subgroup
noncomputable section
namespace Tits.ExceptionalParabolics.FirstQuotient

private theorem pair_mem_positive (i : Fin 4) : pairElement i ∈ splitUnipotent 0 := by
  rw [pairElement_eq]
  apply mul_mem <;> exact subset_closure ⟨_, 1, ((rootBlocks .positive).roots _).property, rfl⟩

private theorem quartet_mem_positive (i : Fin 4) : quartetElement i ∈ splitUnipotent 0 := by
  rw [quartetElement_eq]
  apply mul_mem
  · apply mul_mem <;> exact subset_closure ⟨_, 1, ((rootBlocks .positive).roots _).property, rfl⟩
  · exact subset_closure ⟨_, 1, ((rootBlocks .positive).roots _).property, rfl⟩

private theorem u_mem_positive (i : Fin 8) : u i ∈ splitUnipotent 0 := by
  fin_cases i
  · exact quartet_mem_positive 0
  · exact pair_mem_positive 1
  · exact quartet_mem_positive 3
  · exact pair_mem_positive 3
  · exact quartet_mem_positive 1
  · exact pair_mem_positive 2
  · exact quartet_mem_positive 2
  · exact pair_mem_positive 0

/-- The canonical embedding preserves the positive Sylow marking. -/
theorem sylow_embedding_mem {x : Atlas1600Group} (hx : x ∈ S) :
    FullRee.atlasEmbedding x ∈ FullRee.S := by
  have h : S ≤ FullRee.S.comap FullRee.atlasEmbedding := by
    rw [S, atlas1600SylowTwoSubgroup_eq]
    apply (closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      change toSplitGroup 0 (FullRee.atlasEmbedding _) ∈ splitUnipotent 0
      rw [FullRee.atlasEmbedding_generator_matrix]
      simp only [assignment]
      first
      | exact u_mem_positive _
      | exact mul_mem (u_mem_positive _) (u_mem_positive _)
      | exact mul_mem (u_mem_positive _) (inv_mem (u_mem_positive _))
  exact h hx

/-- Every element of the Atlas first parabolic lies in the full first parabolic. -/
theorem embedding_mem {x : Atlas1600Group} (hx : x ∈ first) :
    FullRee.atlasEmbedding x ∈ FullRee.first := by
  have h : first ≤ FullRee.first.comap FullRee.atlasEmbedding := by
    apply sup_le
    · exact fun x hx => FullRee.sylow_le_first (sylow_embedding_mem hx)
    · apply (closure_le _).mpr
      rintro x (rfl : x = atlas1600ParrottAssignment .r1)
      have he : FullRee.atlasEmbedding (atlas1600ParrottAssignment .r1) =
          Binary.FixedGeometry.weylLift 0 .suzuki := by
        apply toSplitGroup_injective 0
        rw [FullRee.atlasEmbedding_generator_matrix, Binary.FixedGeometry.toSplitGroup_weylLift]
        rfl
      change FullRee.atlasEmbedding _ ∈ FullRee.first
      rw [he]
      exact Binary.FixedGeometry.weylLift_mem_seed 0 .suzuki
  exact h hx

/-- Restrict the canonical Atlas embedding to the two first parabolics. -/
def embedding : first →* FullRee.first :=
  (FullRee.atlasEmbedding.comp first.subtype).codRestrict FullRee.first
    (fun x => embedding_mem x.property)

@[simp] theorem embedding_coe (x : first) :
    (embedding x : Model 0) = FullRee.atlasEmbedding x := rfl

/-- The actual composite with the full-Ree Suzuki projection. -/
def projection : first →* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  FullRee.firstProjection.comp embedding

@[simp] theorem projection_apply (x : first) :
    projection x = FullRee.firstProjection (embedding x) := rfl

private theorem quartet_zero_not_radical (j : Fin 4) :
    ¬ IsRadicalRoot .suzuki (quartetRoots 0 j) := by
  rintro ⟨_, i, hi, hn⟩
  have hi' : i = 0 ∨ i = 3 := by
    fin_cases i <;> simp_all [leviNodes, Fin.ext_iff]
  apply hn
  change typeF4SimpleCoefficient (((rootBlocks .positive).roots (.inr ((0 : Fin 4), j))).val.val) i = 0
  rw [rootBlocks_roots_val]
  rcases hi' with rfl | rfl <;> fin_cases j <;>
    norm_num [RootPartition.index, RootPartition.quartetRow,
      RootPartition.table, typeF4SimpleCoefficient]

private theorem quartet_zero_mem_levi : quartetElement 0 ∈ BinarySuzuki.splitLevi := by
  have h (j : Fin 4) : rootGeneratorInGroup 0 (quartetRoots 0 j) 1 ∈ BinarySuzuki.splitLevi :=
    BinarySuzuki.rootGenerator_mem_splitLevi_of_pos_not_radical _ _
      ((rootBlocks .positive).roots (.inr ((0 : Fin 4), j))).property (quartet_zero_not_radical j)
  rw [quartetElement_eq]
  exact mul_mem (mul_mem (h 0) (h 1)) (h 3)

private theorem quartet_one_mem_radical : quartetElement 1 ∈ splitRadical 0 .suzuki := by
  have h (j : Fin 4) : IsRadicalRoot .suzuki (quartetRoots 1 j) := by
    have he : quartetRoots 1 j =
        ((rootBlocks (.radical .suzuki)).roots (.inr ((0 : Fin 3), j))).val := by
      apply Subtype.ext
      change (((rootBlocks .positive).roots (.inr ((1 : Fin 4), j))).val.val) = _
      simp only [rootBlocks_roots_val]
      rfl
    rw [he]
    exact ((rootBlocks (.radical .suzuki)).roots (.inr ((0 : Fin 3), j))).property
  rw [quartetElement_eq]
  apply mul_mem
  · apply mul_mem <;> exact subset_closure ⟨_, 1, h _, rfl⟩
  · exact subset_closure ⟨_, 1, h _, rfl⟩

private def rootElement : Model 0 :=
  ⟨quartetElement 0, (mem_fixedSubgroup 0 _).mpr (quartetElement_fixed 0)⟩

private theorem rootElement_mem_levi : rootElement ∈ BinarySuzuki.levi := by
  change toSplitGroup 0 rootElement ∈ BinarySuzuki.splitLevi
  rw [toSplitGroup_apply]
  exact quartet_zero_mem_levi

private def rootLevi : BinarySuzuki.leviInSeed :=
  ⟨⟨rootElement, BinarySuzuki.levi_le_seed rootElement_mem_levi⟩, rootElement_mem_levi⟩

private def radicalElement : FullRee.first :=
  ⟨⟨quartetElement 1, (mem_fixedSubgroup 0 _).mpr (quartetElement_fixed 1)⟩, by
    change toSplitGroup 0 _ ∈ splitSeed 0 .suzuki
    rw [toSplitGroup_apply]
    exact (splitRadical_le_unipotent 0 .suzuki).trans
      (splitUnipotent_le_splitSeed 0 .suzuki) quartet_one_mem_radical⟩

private def s5 : first := ⟨atlas1600ParrottAssignment .s5, sylow_le_first (by
  rw [S, atlas1600SylowTwoSubgroup_eq]
  exact subset_closure (by simp))⟩

private theorem embedding_s5 : embedding s5 = rootLevi.val * radicalElement := by
  apply Subtype.ext
  apply toSplitGroup_injective 0
  change toSplitGroup 0 (FullRee.atlasEmbedding (atlas1600ParrottAssignment .s5)) = _
  rw [FullRee.atlasEmbedding_generator_matrix, toSplitGroup_apply]
  rfl

private theorem projection_radical : FullRee.firstProjection radicalElement = 1 := by
  change radicalElement ∈ BinarySuzuki.projection.ker
  rw [BinarySuzuki.projection_ker]
  change toSplitGroup 0 radicalElement.val ∈ splitRadical 0 .suzuki
  rw [toSplitGroup_apply]
  exact quartet_one_mem_radical

private theorem projection_s5 : projection s5 = BinarySuzuki.leviMatrixEquiv rootLevi := by
  change FullRee.firstProjection (embedding s5) = _
  rw [embedding_s5, map_mul, projection_radical, mul_one]
  exact BinarySuzuki.projection_levi rootLevi

private theorem rootLevi_square :
    rootLevi.val.val ^ 2 = (InvolutionRootGeometry.longRoot : Model 0) := by
  apply toSplitGroup_injective 0
  rw [map_pow, toSplitGroup_apply, InvolutionRootGeometry.longRoot_matrix]
  rfl

private theorem rootLevi_order : orderOf rootLevi = 4 := by
  have horder : orderOf (rootLevi ^ 2) = 2 := by
    calc
      orderOf (rootLevi ^ 2) = orderOf (rootLevi ^ 2).val :=
        (Subgroup.orderOf_coe (rootLevi ^ 2)).symm
      _ = orderOf (rootLevi ^ 2).val.val :=
        (Subgroup.orderOf_coe (rootLevi ^ 2).val).symm
      _ = orderOf (InvolutionRootGeometry.longRoot : Model 0) :=
        congrArg orderOf rootLevi_square
      _ = orderOf InvolutionRootGeometry.longRoot := Subgroup.orderOf_coe _
      _ = 2 := InvolutionRootGeometry.longRoot_order
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · intro he
    change rootLevi ^ 2 = 1 at he
    rw [he, orderOf_one] at horder
    contradiction
  · have h := pow_orderOf_eq_one (rootLevi ^ 2)
    rw [horder] at h
    simpa only [← pow_mul, Nat.reduceAdd, Nat.reducePow, Nat.reduceMul] using h

private theorem s5_image_order : orderOf (projection s5) = 4 := by
  rw [projection_s5, MulEquiv.orderOf_eq]
  exact rootLevi_order

/-- The restriction remains faithful. -/
theorem embedding_injective : Function.Injective embedding := by
  intro x y h
  apply Subtype.ext
  apply FullRee.atlasEmbedding_injective
  exact congrArg Subtype.val h

private theorem ker_isPGroup : IsPGroup 2 projection.ker := by
  have he : projection.ker = FullRee.firstProjection.ker.comap embedding := rfl
  rw [he, FullRee.firstProjection_ker]
  exact pCore_isPGroup.comap_of_injective embedding embedding_injective

/-- The actual composite fills the concrete Suzuki carrier. -/
theorem projection_surjective : Function.Surjective projection := by
  have hm := projection.ker.card_mul_index
  rw [Subgroup.index_ker, first_card] at hm
  have h4 : 4 ∣ Nat.card projection.range := by
    simpa only [s5_image_order] using
      projection.range.orderOf_dvd_natCard (show projection s5 ∈ projection.range from ⟨s5, rfl⟩)
  obtain ⟨n, hn⟩ := ker_isPGroup.exists_card_eq
  have hk : Nat.Coprime 5 (Nat.card projection.ker) := by
    rw [hn]
    exact Nat.Coprime.pow_right n (by decide)
  have h5 : 5 ∣ Nat.card projection.range := hk.dvd_mul_left.mp (by rw [hm]; norm_num)
  have h20 : 20 ∣ Nat.card projection.range :=
    (by decide : Nat.Coprime 4 5).mul_dvd_of_dvd_of_dvd h4 h5
  apply MonoidHom.range_eq_top.mp
  apply Subgroup.eq_top_of_card_eq
  apply Nat.dvd_antisymm projection.range.card_subgroup_dvd_card
  simpa only [BenderSuzuki.MatrixGroups.suzukiZero_card] using h20

/-- The kernel is the intrinsic two-core of the Atlas first parabolic. -/
theorem projection_ker : projection.ker = pCore 2 first := by
  have h := projection.comap_pCore_of_ker_isPGroup projection_surjective ker_isPGroup
  simpa only [Binary.suzuki_twoCore_eq_bot, MonoidHom.comap_bot] using h

/-- The Atlas core is the inverse image of the full-Ree core under this restriction. -/
theorem core_eq_comap : pCore 2 first = (pCore 2 FullRee.first).comap embedding := by
  rw [← projection_ker, ← FullRee.firstProjection_ker]
  rfl

/-- The corrected core order, obtained from the actual surjection. -/
theorem core_card : Nat.card (pCore 2 first) = 512 := by
  have hm := projection.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr projection_surjective,
    Nat.card_congr (Subgroup.topEquiv).toEquiv,
    BenderSuzuki.MatrixGroups.suzukiZero_card, first_card, projection_ker] at hm
  omega

/-- The quotient equivalence uses the canonical embedding and full-Ree projection. -/
def coreQuotientEquiv : (first ⧸ pCore 2 first) ≃*
    BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  (QuotientGroup.quotientMulEquivOfEq projection_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective projection projection_surjective)

@[simp] theorem coreQuotientEquiv_mk (x : first) :
    coreQuotientEquiv (QuotientGroup.mk' (pCore 2 first) x) =
      FullRee.firstProjection (embedding x) := rfl
end Tits.ExceptionalParabolics.FirstQuotient
