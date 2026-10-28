module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Generators

/-!
# Descending the long-block lattice construction

A subgroup of the actual Leech isometry group supplies SL₃(4) after quotienting
by exactly its central signs. Surjective descent constructs a faithful block
map into the literal Conway quotient. An integral normalizer element then
supplies the prescribed graph relation. It lies outside the block because the
graph automorphism inverts a nonidentity element of the cubic scalar center.

`LatticeBlock` and `LatticeGraph` specify the two remaining concrete lattice
constructions. No inhabitants are asserted. In particular, the block is not
required to lift to an ordinary SL₃(4) subgroup of Co₀: its inverse image may
be a nonsplit central extension. `LatticeGraph.generatorData` applies these
constructions to every field of the original generator contract, using the
same quotient maps, scalar marking, and Peirce graph convention.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
construction of K₁ from 48.3 and 49.2. The concrete Leech lattice, central
projection, and scalar A₅ are the existing attributed ATLAS ports.
-/

@[expose] public section
open Matrix Atlas.Conway Atlas.Lattices
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long

variable {K : Type*} [Field K]

private theorem center_cube (A : SL(3,K)) (hA : A ∈ Subgroup.center SL(3,K)) : A ^ 3 = 1 := by
  obtain ⟨c, hc, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  apply Subtype.ext
  change A.val ^ 3 = 1
  rw [← he, ← map_pow]
  simpa using congrArg (Matrix.scalar (Fin 3)) hc

variable [CharP K 2]

/-- The permutation implementing the Peirce graph convention has square one. -/
theorem graphFlip_square : (graphFlip (K := K)) * graphFlip = 1 := by
  apply Subtype.ext
  change graphFlip.val * graphFlip.val = (1 : Matrix (Fin 3) (Fin 3) K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphFlip, Matrix.mul_apply, Fin.sum_univ_three]

/-- On central scalars, the precise Peirce graph automorphism is inversion. -/
theorem graphTwist_center (A : SL(3,K)) (hA : A ∈ Subgroup.center SL(3,K)) :
    graphTwist A = A⁻¹ := by
  have hi : A⁻¹ ∈ Subgroup.center SL(3,K) := (Subgroup.center _).inv_mem hA
  have ht : A⁻¹.transpose = A⁻¹ := by
    obtain ⟨c, _, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hi
    apply Subtype.ext
    change A⁻¹.val.transpose = A⁻¹.val
    simp [← he, Matrix.scalar_apply]
  rw [graphTwist, ht, Subgroup.mem_center_iff.mp hi graphFlip,
    mul_assoc, graphFlip_square, mul_one]

private theorem exists_nontrivial_cube : ∃ c : F, c ^ 3 = 1 ∧ c ≠ 1 := by
  refine ⟨scalarFieldEquiv.symm (⟨0,1⟩ : Atlas.Algebra.GoldenFour), ?_, ?_⟩
  · apply scalarFieldEquiv.injective
    simp only [map_pow, RingEquiv.apply_symm_apply, map_one]
    decide +kernel
  · intro h
    have he := congrArg scalarFieldEquiv h
    simp only [RingEquiv.apply_symm_apply, map_one] at he
    exact (by decide : (⟨0,1⟩ : Atlas.Algebra.GoldenFour) ≠ 1) he

/-- The graph automorphism inverts a nonidentity central cubic element. -/
theorem graphTwist_moves_center : ∃ A : SL(3,F),
    A ∈ Subgroup.center SL(3,F) ∧ graphTwist A ≠ A := by
  obtain ⟨c, hc, hne⟩ := exists_nontrivial_cube
  let A : SL(3,F) := ⟨Matrix.scalar (Fin 3) c, by simpa using hc⟩
  have hA : A ∈ Subgroup.center SL(3,F) :=
    Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨c, by simpa using hc, rfl⟩
  refine ⟨A, hA, ?_⟩
  rw [graphTwist_center A hA]
  intro h
  have h2 : A ^ 2 = 1 := by
    calc A ^ 2 = A⁻¹ * A := by rw [pow_two, h]
         _ = 1 := inv_mul_cancel _
  have h1 : A = 1 := by
    simpa only [pow_succ A 2, h2, one_mul] using center_cube A hA
  have he := congrArg (fun B : SL(3,F) => B.val 0 0) h1
  exact hne (by simpa [A] using he)

/-- An element inducing this graph automorphism cannot belong to the block image. -/
theorem graph_swap_not_mem_range {G : Type*} [Group G] (b : SL(3,F) →* G)
    (hb : Function.Injective b) (s : G)
    (hs : ∀ A, s * b A = b (graphTwist A) * s) : s ∉ b.range := by
  rintro ⟨B, rfl⟩
  obtain ⟨A, hA, hm⟩ := graphTwist_moves_center
  have he : B * A = graphTwist A * B := hb (by simpa only [map_mul] using hs A)
  have hc := Subgroup.mem_center_iff.mp hA B
  exact hm (mul_right_cancel (he.symm.trans hc))
/-- The integral inverse image of the SL₃(4) block, identified only after
quotienting by its actual central signs. No splitting in Co₀ is assumed. -/
structure LatticeBlock where
  marking : alternatingGroup fourPoints →* alternatingGroup (Fin 5)
  marking_injective : Function.Injective marking
  cover : Subgroup LeechIsometryGroup
  quotient : cover →* SL(3,F)
  surjective : Function.Surjective quotient
  kernel : quotient.ker = leechCentralSigns.comap cover.subtype
  commute : ∀ a (g : cover),
    Commute (scalarFive (marking a)) (leechCentralProjection g.val)

/-- The integral normalizer element in the source construction. Its square
may be either central sign, and its action is compared using the actual
quotient map of the block. -/
structure LatticeGraph (D : LatticeBlock) where
  swap : LeechIsometryGroup
  square : swap * swap ∈ leechCentralSigns
  normalizes : ∀ g : D.cover, swap * g.val * swap⁻¹ ∈ D.cover
  twist : ∀ g : D.cover,
    D.quotient ⟨swap * g.val * swap⁻¹, normalizes g⟩ = graphTwist (D.quotient g)
  commute : ∀ a, Commute (scalarFive (D.marking a)) (leechCentralProjection swap)

private theorem LatticeBlock.kernel_le (D : LatticeBlock) :
    D.quotient.ker ≤ (leechCentralProjection.comp D.cover.subtype).ker := by
  intro g hg
  have hs : g.val ∈ leechCentralSigns := by
    change g ∈ leechCentralSigns.comap D.cover.subtype
    rwa [← D.kernel]
  change leechCentralProjection g.val = 1
  apply MonoidHom.mem_ker.mp
  rwa [leechCentralProjection_kernel]

/-- Descend the integral block through precisely its central-sign kernel. -/
noncomputable def LatticeBlock.block (D : LatticeBlock) : SL(3,F) →* LeechCentralQuotient :=
  D.quotient.liftOfSurjective D.surjective
    ⟨leechCentralProjection.comp D.cover.subtype, by exact LatticeBlock.kernel_le D⟩

@[simp] theorem LatticeBlock.block_quotient (D : LatticeBlock) (g : D.cover) :
    D.block (D.quotient g) = leechCentralProjection g.val :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- Exactness of the sign kernel proves faithfulness in the Conway quotient. -/
theorem LatticeBlock.block_injective (D : LatticeBlock) : Function.Injective D.block := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro A hA
  change A = 1
  obtain ⟨g, rfl⟩ := D.surjective A
  have hg : leechCentralProjection g.val = 1 := by
    simpa only [MonoidHom.mem_ker, D.block_quotient] using hA
  apply MonoidHom.mem_ker.mp
  rw [D.kernel]
  change g.val ∈ leechCentralSigns
  rw [← leechCentralProjection_kernel]
  exact hg

theorem LatticeBlock.block_commute (D : LatticeBlock)
    (a : alternatingGroup fourPoints) (A : SL(3,F)) :
    Commute (scalarFive (D.marking a)) (D.block A) := by
  obtain ⟨g, rfl⟩ := D.surjective A
  rw [D.block_quotient]
  exact D.commute a g

/-- The integral conjugation comparison gives the required literal graph relation. -/
theorem LatticeGraph.swap_block {D : LatticeBlock} (S : LatticeGraph D) (A : SL(3,F)) :
    leechCentralProjection S.swap * D.block A =
      D.block (graphTwist A) * leechCentralProjection S.swap := by
  obtain ⟨g, rfl⟩ := D.surjective A
  rw [← S.twist g, D.block_quotient, D.block_quotient]
  rw [map_mul, map_mul, map_inv]
  group

/-- Integral block recognition and its normalizer action supply every field
of the original generator contract. The two lattice constructions remain
explicit inputs; this is not the unconditional source theorem. -/
noncomputable def LatticeGraph.generatorData {D : LatticeBlock} (S : LatticeGraph D) :
    GeneratorData where
  marking := D.marking
  marking_injective := D.marking_injective
  block := D.block
  block_injective := D.block_injective
  swap := leechCentralProjection S.swap
  swap_square := by
    rw [← map_mul]
    apply MonoidHom.mem_ker.mp
    rw [leechCentralProjection_kernel]
    exact S.square
  swap_not_block := graph_swap_not_mem_range D.block D.block_injective _ S.swap_block
  swap_block := S.swap_block
  block_commute := D.block_commute
  swap_commute := S.commute

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
