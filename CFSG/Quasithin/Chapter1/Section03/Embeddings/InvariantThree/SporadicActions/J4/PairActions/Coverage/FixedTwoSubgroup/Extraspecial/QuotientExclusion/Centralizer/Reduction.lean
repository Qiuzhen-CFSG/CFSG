module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.Conjugation
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.CharP.Algebra

/-!
# A common commutator and a binary flag for the J₄ centralizer bound

Let T be the specified order-2²¹ matrix subgroup, and put D = [T,[T,T]].
Two concrete inputs suffice for the large-centralizer problem: D is contained
in every T-normal subgroup of index at most 32, and the matrix commutant of D
preserves a complete flag over F₂. The definitions below specify these separate
certificate obligations; they do not supply their witnesses.

The flag implication is proved here. An invertible triangular binary matrix
has diagonal entries one. Cayley–Hamilton and the characteristic-two power
identity give exponent dividing 128 in degree 112. The faithful map from the
actual J₄ carrier to matrix units then makes C_Model(D) a two-group.

Source context: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher, *Overgroups of Sylow
subgroups in sporadic groups* (1986). This is a matrix-certificate route to
the kernel bound in `QuotientExclusion.Conjugation`, not an invocation of a
sporadic centralizer table or of the full order of J₄.
-/

@[expose] public section
open Subgroup
open Janko4.OuterReduction.OddIndex
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- The third lower-central subgroup of the specified two-subgroup. -/
noncomputable def fixedTwoThirdCommutator : Subgroup Janko4.Model :=
  ⁅twoSubgroup, ⁅twoSubgroup, twoSubgroup⁆⁆

theorem fixedTwoThirdCommutator_le : fixedTwoThirdCommutator ≤ twoSubgroup := by
  have h : ⁅twoSubgroup, twoSubgroup⁆ ≤ twoSubgroup :=
    (Subgroup.commutator_le_sup twoSubgroup twoSubgroup).trans
      (sup_idem _).le
  exact (Subgroup.commutator_le_sup twoSubgroup ⁅twoSubgroup, twoSubgroup⁆).trans (sup_le le_rfl h)

/-- Coverage obligation for the third lower-central subgroup. -/
def FixedTwoThirdCommutatorCoverage : Prop :=
  ∀ K : Subgroup Janko4.Model, K ≤ twoSubgroup →
    twoSubgroup ≤ normalizer (K : Set Janko4.Model) →
    K.relIndex twoSubgroup ≤ 32 → fixedTwoThirdCommutator ≤ K

/-- A flag in the actual 112-dimensional representation preserved by its commutant. -/
def FixedTwoThirdCommutantFlag : Prop :=
  ∃ B : Janko4.BinaryMatrixˣ, ∀ M : Janko4.BinaryMatrix,
    (∀ g ∈ fixedTwoThirdCommutator, Commute M (Janko4.toMatrix g)) →
    ((B : Janko4.BinaryMatrix) * M * (↑B⁻¹ : Janko4.BinaryMatrix)).IsLowerTriangular

private theorem binary_lower_triangular_unit_pow (u : Janko4.BinaryMatrixˣ)
    (ht : (u : Janko4.BinaryMatrix).IsLowerTriangular) : u ^ 128 = 1 := by
  let M : Janko4.BinaryMatrix := u
  have hd (i : Fin 112) : M i i = 1 := by
    have hdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp u.isUnit).ne_zero
    rw [Matrix.det_of_isLowerTriangular M ht] at hdet
    have hn := (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ _)
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hn
  have htM : M.IsLowerTriangular := ht
  have hut : M.transpose.IsUpperTriangular := by
    intro i j hij
    exact htM hij
  have hc : M.charpoly = (Polynomial.X - Polynomial.C 1) ^ 112 := by
    rw [← Matrix.charpoly_transpose M, Matrix.charpoly_of_isUpperTriangular _ hut]
    simp only [Matrix.transpose_apply, hd]
    simp
  have hn : (M - 1) ^ 112 = 0 := by
    have h := Matrix.aeval_self_charpoly M
    rw [hc] at h
    simpa using h
  have hn' : (M - 1) ^ (2 ^ 7) = 0 := pow_eq_zero_of_le (by decide) hn
  let : ExpChar Janko4.BinaryMatrix 2 :=
    expChar_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (ZMod 2) Janko4.BinaryMatrix) 2
  have h := add_pow_expChar_pow_of_commute 2 7 (Commute.one_left (M - 1))
  rw [show (1 : Janko4.BinaryMatrix) + (M - 1) = M by
    rw [add_comm, sub_add_cancel], one_pow, hn', add_zero] at h
  exact Units.ext h

/-- A commutant flag forces the actual ambient centralizer to be a two-group. -/
theorem fixedTwoThirdCommutator_centralizer_isPGroup_of_flag
    (hflag : FixedTwoThirdCommutantFlag) :
    IsPGroup 2 (centralizer (fixedTwoThirdCommutator : Set Janko4.Model)) := by
  obtain ⟨B, hB⟩ := hflag
  intro g
  refine ⟨7, ?_⟩
  have ht := hB (Janko4.toMatrix g) (by
    intro k hk
    have he := (mem_centralizer_iff.mp g.property) k hk
    change Janko4.toMatrix g * Janko4.toMatrix k =
      Janko4.toMatrix k * Janko4.toMatrix g
    simpa only [map_mul] using congrArg Janko4.toMatrix he.symm)
  have hp : (B * Janko4.toAmbient g * B⁻¹) ^ 128 = 1 :=
    binary_lower_triangular_unit_pow _ ht
  have hp' : Janko4.toAmbient (g : Janko4.Model) ^ 128 = 1 := by
    apply (MulAut.conj B).injective
    rw [map_one, map_pow]
    exact hp
  apply Subtype.ext
  apply Janko4.toAmbient_injective
  change Janko4.toAmbient ((g : Janko4.Model) ^ 128) = Janko4.toAmbient 1
  simpa only [map_pow, map_one] using hp'

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
