module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Embedding
public import Theory.SpecificGroups.SL2.PrimeToResidual

/-!
# Full orthogonal blocks and lifting the marked centralizer

These maps retain the published left determinant-space SL₂ and right block
conventions. The full complementary isometry group is kept separate from its
commutator subgroup, so the missing block-restriction calculation has a precise
interface. Negation is defined in the full orthogonal group only.

Projective centralization lifts to genuine centralization in odd characteristic.
The commutator error is a homomorphism from SL₂ into the central scalar kernel.
That kernel has exponent two, while transvections are killed by the odd field
characteristic. Elementary generation kills the error even for SL₂(3).

Source: Aschbacher–Smith, A.2.17, printed p.39; GLS3 §2.7 for the orthogonal
commutator/scalar-quotient conventions. No full centralizer decomposition or
complementary generation theorem is assumed by the lifting result.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer
open FourPlusMatrix TheoremDRootNormalizer.HigherRanks
variable {F : Type*} [Field F]

/-- The published projective block map, with codomain restricted to its literal centralizer. -/
def blockToCentralizer [Finite F] (r : ℕ) (hq : 2 < Nat.card F) :
    SpecialLinearGroup (Fin 2) F ×
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) →*
        fundamentalCentralizer r hq :=
  (projectiveBlockHom r hq).codRestrict _
    (fun g => projectiveBlockHom_le_centralizer r hq ⟨g, rfl⟩)

/-- The entire right SL₂ factor lies in the actual residual image, including over F₃. -/
theorem rightSL_mem_residual [Finite F] (p : ℕ) [CharP F p]
    (r : ℕ) (hq : 2 < Nat.card F) (a : SpecialLinearGroup (Fin 2) F) :
    projectiveBlockHom r hq (a, 1) ∈ centralizerResidualImage p r hq := by
  exact ⟨blockToCentralizer r hq (a, 1),
    Matrix.SL2.map_mem_primeToResidual p
      ((blockToCentralizer r hq).comp (MonoidHom.inl _ _)) a, rfl⟩

/-- The negative identity in the right determinant-space SL₂. -/
def negativeSL : SpecialLinearGroup (Fin 2) F :=
  ⟨-1, by simp [Matrix.det_neg]⟩

/-- Negation in the full complementary orthogonal group; Omega membership is not presumed. -/
def negativeComplement [Finite F] (r : ℕ) :
    Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) :=
  ⟨LinearEquiv.neg F, (mem_quadraticIsometrySubgroup _ _).mpr (by
    intro v
    exact QuadraticMap.map_neg _ v)⟩

private theorem sl2_map_eq_one_of_square (p : ℕ) [CharP F p] (ho : Odd p)
    {G : Type*} [Group G] (f : SpecialLinearGroup (Fin 2) F →* G)
    (hf : ∀ A, f A ^ 2 = 1) (A : SpecialLinearGroup (Fin 2) F) : f A = 1 := by
  apply Atlas.sl_elementary_induction (fun A => f A = 1) ?_ ?_ A
  · intro i j hij a
    have hpow (n : ℕ) : SpecialLinearGroup.transvection hij a ^ n =
        SpecialLinearGroup.transvection hij (n • a) := by
      induction n with
      | zero => simp [SpecialLinearGroup.transvection_coeff_zero]
      | succ n ih =>
        rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add, succ_nsmul]
    have hp : SpecialLinearGroup.transvection hij a ^ p = 1 := by
      simpa [nsmul_eq_mul, CharP.cast_eq_zero F p,
        SpecialLinearGroup.transvection_coeff_zero] using hpow p
    have ht : f (SpecialLinearGroup.transvection hij a) ^ p = 1 := by
      rw [← map_pow, hp, map_one]
    obtain ⟨k, hk⟩ := ho
    simpa only [hk, pow_add, pow_mul, hf, one_pow, pow_one, one_mul] using ht
  · intro A B hA hB
    rw [map_mul, hA, hB, mul_one]

open scoped commutatorElement in
private theorem sl2_centralizer_lifts (p : ℕ) [CharP F p] (ho : Odd p)
    {G H : Type*} [Group G] [Group H] (q : G →* H)
    (hq : q.ker ≤ Subgroup.center G) (hsq : ∀ x ∈ q.ker, x ^ 2 = 1)
    (f : SpecialLinearGroup (Fin 2) F →* G) (x : G)
    (hx : ∀ A, Commute (q (f A)) (q x)) (A : SpecialLinearGroup (Fin 2) F) :
    Commute (f A) x := by
  have hker (B : SpecialLinearGroup (Fin 2) F) : ⁅f B, x⁆ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, (hx B).commutator_eq]
  let c : SpecialLinearGroup (Fin 2) F →* G :=
    { toFun B := ⁅f B, x⁆
      map_one' := by simp
      map_mul' B D := by
        rw [map_mul, commutatorElement_mul_left_eq_conj_mul]
        rw [(Subgroup.mem_center_iff.mp (hq (hker D)) (f B)), mul_inv_cancel_right]
        exact (Subgroup.mem_center_iff.mp (hq (hker B)) ⁅f D, x⁆) }
  exact commutatorElement_eq_one_iff_commute.mp
    (sl2_map_eq_one_of_square p ho c (fun B => hsq _ (hker B)) A)

/-- A lift of a projective centralizer element already commutes with the covering left SL₂. -/
theorem projective_centralizer_lifts [Finite F] (p : ℕ) [CharP F p] (ho : Odd p)
    (r : ℕ) (hq : 2 < Nat.card F)
    (x : Minus.Omega F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3)))
    (hx : QuotientGroup.mk' (Minus.scalarSubgroup F _ _) x ∈ fundamentalCentralizer r hq)
    (A : SpecialLinearGroup (Fin 2) F) :
    Commute (splitOmegaHom r (Minus.parameter F) hq (fourLeft A)) x := by
  apply sl2_centralizer_lifts p ho (QuotientGroup.mk' (Minus.scalarSubgroup F _ _))
    (fun g hg => Minus.scalarSubgroup_le_center F _ _
      ((QuotientGroup.eq_one_iff g).mp hg))
    (fun g hg => omegaScalar_square (Minus.quadraticForm F (r + 3))
      ⟨(0, (1, 0)), by simp [Minus.quadraticForm, Minus.plane_apply]⟩ g
      ((QuotientGroup.eq_one_iff g).mp hg))
    ((splitOmegaHom r (Minus.parameter F) hq).comp fourLeft) x
  intro B
  exact Subgroup.mem_centralizer_iff.mp hx _ ⟨B, rfl⟩

/-- Right SL₂ and the full complementary isometry group acting on their literal blocks. -/
def fullBlockHom [Finite F] (r : ℕ) :
    SpecialLinearGroup (Fin 2) F ×
      Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) →*
        Minus.Orthogonal F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3)) :=
  (blockHom r (Minus.parameter F)).comp
    (((elementarySubgroup (formD 2 F)).subtype.comp fourRight).prodMap (MonoidHom.id _))

/-- The marked left SL₂, regarded in the full ambient orthogonal group. -/
def fullFundamentalHom [Finite F] (r : ℕ) :
    SpecialLinearGroup (Fin 2) F →*
      Minus.Orthogonal F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3)) :=
  ((blockHom r (Minus.parameter F)).comp (MonoidHom.inl _ _)).comp
    ((elementarySubgroup (formD 2 F)).subtype.comp fourLeft)

/-- Compatibility of the full isometry action with the published commutator lift. -/
theorem fullFundamentalHom_eq [Finite F] (r : ℕ) (hq : 2 < Nat.card F)
    (A : SpecialLinearGroup (Fin 2) F) :
    fullFundamentalHom r A = (splitOmegaHom r (Minus.parameter F) hq (fourLeft A)).val := rfl

/-- Compatibility with the published cover after restricting the complement to Omega. -/
theorem fullBlockHom_eq [Finite F] (r : ℕ) (hq : 2 < Nat.card F)
    (g : SpecialLinearGroup (Fin 2) F ×
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    fullBlockHom r (g.1, g.2.val) = (coverBlockHom r hq g).val := rfl


end ClassicalOrthogonal.Fundamental.MinusCentralizer
