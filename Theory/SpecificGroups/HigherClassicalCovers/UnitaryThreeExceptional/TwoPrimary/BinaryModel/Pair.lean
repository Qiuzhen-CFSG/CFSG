module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary.BinaryModel.Plane
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.QuotientCore.Blocks

/-!
# The actual binary-tetrahedral pair in the PSU₄(3) involution centralizer

Each binary factor acts with determinant one on one coordinate plane.
The block-diagonal map into SU₄ followed by the defining projective map
lands in the full centralizer of `diag(-1,-1,1,1)`. Its kernel is exactly
the two diagonal signs, so its image has order 288.

Every lift of a centralizer element preserves or interchanges the two
planes. Conjugation by either unitary block preserves SU₂(3), proving
normality in the full projective centralizer. The index calculation is
provided separately by `BinaryModel.Order`.

Sources: GLS3, chapter 2, §2.7, and chapter 6, §6.1; local model input for
Aschbacher–Smith I.1.4(5), printed p.408 of `refs/quasithin.pdf`. The kernel
argument adapts `RepresentativeCore/Quaternion` and retains the full
SU₄-to-PSU₄ scalar quotient.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.QuotientCore.Blocks
@[expose] public section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary.BinaryModel

def pairMatrix : (B × B) →* Mat₄ where
  toFun q := block (binaryMatrix q.1) (binaryMatrix q.2)
  map_one' := by simp only [Prod.fst_one, Prod.snd_one, map_one, block_one]
  map_mul' x y := by
    change block (binaryMatrix (x.1 * y.1)) (binaryMatrix (x.2 * y.2)) = _
    rw [map_mul, map_mul]
    exact (block_mul _ _ _ _).symm

/-- The literal determinant-one coordinate blocks, before the scalar quotient. -/
noncomputable def pairSU : (B × B) →* (form 4).specialSubgroup :=
  pairMatrix.toHomUnits.codRestrict _ (by
    intro q
    rw [HermitianForm.mem_specialSubgroup_iff]
    constructor
    · change (block (binaryMatrix q.1) (binaryMatrix q.2)).conjTranspose * 1 *
        block (binaryMatrix q.1) (binaryMatrix q.2) = 1
      rw [mul_one, block_adj, block_mul, binaryMatrix_unitary, binaryMatrix_unitary, block_one]
    · apply Units.ext
      change (block (binaryMatrix q.1) (binaryMatrix q.2)).det = 1
      rw [block_det, binaryMatrix_det, binaryMatrix_det, one_mul])

theorem pairSU_val (q : B × B) :
    (pairSU q).val.val = block (binaryMatrix q.1) (binaryMatrix q.2) := rfl

/-- The binary pair in the full centralizer under the defining SU-to-PSU projection. -/
noncomputable def pair : (B × B) →* standardCentralizer :=
  ((project 4).comp pairSU).codRestrict _ (by
    intro q
    exact (project_mem_standardCentralizer_iff _).mpr
      (Or.inl (block_commutes_standard _ _)))

theorem pair_val (q : B × B) : (pair q).val = project 4 (pairSU q) := rfl

private theorem pair_scalar (q : B × B) (u : F)
    (h : block (binaryMatrix q.1) (binaryMatrix q.2) = Matrix.scalar (Fin 4) u) :
    q = 1 ∨ q = (binarySign, binarySign) := by
  have h₁ : binaryMatrix q.1 = Matrix.scalar (Fin 2) u := by
    apply Matrix.ext; intro i j
    have he := congrArg (fun M : Mat₄ => M (Fin.castAdd 2 i) (Fin.castAdd 2 j)) h
    fin_cases i <;> fin_cases j <;> exact he
  have h₂ : binaryMatrix q.2 = Matrix.scalar (Fin 2) u := by
    apply Matrix.ext; intro i j
    have he := congrArg (fun M : Mat₄ => M (Fin.natAdd 2 i) (Fin.natAdd 2 j)) h
    fin_cases i <;> fin_cases j <;> exact he
  have hne : (1 : F) ≠ -1 := by decide
  rcases binaryMatrix_scalar q.1 u h₁ with ⟨h₁, hu₁⟩ | ⟨h₁, hu₁⟩ <;>
    rcases binaryMatrix_scalar q.2 u h₂ with ⟨h₂, hu₂⟩ | ⟨h₂, hu₂⟩
  · exact Or.inl (Prod.ext h₁ h₂)
  · exact (hne (hu₁.symm.trans hu₂)).elim
  · exact (hne (hu₂.symm.trans hu₁)).elim
  · exact Or.inr (Prod.ext h₁ h₂)

/-- The kernel retains exactly the common central sign. -/
theorem pair_eq_one_iff (q : B × B) :
    pair q = 1 ↔ q = 1 ∨ q = (binarySign, binarySign) := by
  constructor
  · intro h
    have he : ProjGenLinGroup.mk (pairSU q).val = 1 :=
      congrArg (fun g : standardCentralizer => g.val.val) h
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at he
    obtain ⟨u, hu⟩ := he
    exact pair_scalar q u.val (congrArg Units.val hu).symm
  · rintro (rfl | rfl)
    · exact map_one _
    · apply Subtype.ext
      apply Subtype.ext
      change ProjGenLinGroup.mk (pairSU (binarySign, binarySign)).val = 1
      rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
      refine ⟨-1, ?_⟩
      apply Units.ext
      change Matrix.scalar (Fin 4) (-1 : F) =
        block (binaryMatrix binarySign) (binaryMatrix binarySign)
      decide

theorem pair_kernel_card : Nat.card pair.ker = 2 := by
  have e : pair.ker ≃ {q : B × B // q = 1 ∨ q = (binarySign, binarySign)} :=
    Equiv.subtypeEquivRight pair_eq_one_iff
  let : Fintype B := Fintype.ofEquiv
    (QuaternionGroup 2 × Multiplicative (ZMod 3)) SemidirectProduct.equivProd.symm
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

theorem pair_range_card : Nat.card pair.range = 288 := by
  have h := pair.ker.card_mul_index
  rw [Subgroup.index_ker, pair_kernel_card, Nat.card_prod,
    GLS3.Chapter5.SchurPresentation.binaryTetrahedral_card] at h
  omega

private theorem lift_normalizes (g : (form 4).specialSubgroup)
    (hg : project 4 g ∈ standardCentralizer) (q : B × B) :
    ∃ r : B × B, g * pairSU q = pairSU r * g := by
  obtain ⟨A, D, _, he | he⟩ := signed_exists g hg
  · obtain ⟨a, ha⟩ := unitary_normalizes_binary A q.1
    obtain ⟨b, hb⟩ := unitary_normalizes_binary D q.2
    refine ⟨(a,b), Subtype.ext (Units.ext ?_)⟩
    change g.val.val * (pairSU q).val.val = (pairSU (a,b)).val.val * g.val.val
    rw [pairSU_val, pairSU_val, he, block_mul, block_mul, ha, hb]
  · obtain ⟨a, ha⟩ := unitary_normalizes_binary A q.2
    obtain ⟨b, hb⟩ := unitary_normalizes_binary D q.1
    refine ⟨(a,b), Subtype.ext (Units.ext ?_)⟩
    change g.val.val * (pairSU q).val.val = (pairSU (a,b)).val.val * g.val.val
    rw [pairSU_val, pairSU_val, he, mul_assoc, swap_block,
      ← mul_assoc, block_mul, ha, hb, ← block_mul, mul_assoc]

/-- Normality is in the full projective centralizer, including block interchange. -/
theorem pair_range_normal : pair.range.Normal := by
  constructor
  rintro x ⟨q, rfl⟩ g
  obtain ⟨s, hs⟩ := project_surjective 4 g.val
  have hg : project 4 s ∈ standardCentralizer := by rw [hs]; exact g.property
  obtain ⟨r, hr⟩ := lift_normalizes s hg q
  refine ⟨r, ?_⟩
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Subtype.ext
  change project 4 (pairSU r) * g.val = g.val * project 4 (pairSU q)
  rw [← hs, ← map_mul, ← map_mul, hr]
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary.BinaryModel
