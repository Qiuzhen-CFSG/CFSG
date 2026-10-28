module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.DiagonalCenter.KernelGeneration.ConcreteMovement
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.DiagonalCenter.KernelGeneration.LinearReduction
/-!
# Exhausting the cubic standard kernel actions

Transport the checked diagonal matrix from the concrete four-element field to
the canonical one. Entrywise field transport commutes with actual matrix
conjugation. Its determinant is a nonidentity element of the three-element
unit group. Therefore its two powers exhaust the nontrivial determinants;
correcting any linear matrix by the matching determinant leaves an inner
projective factor, which fixes the universal kernel.

The concrete movement calculation and the binary coinvariant argument are
assembled with this reduction in `KernelGeneration`. Source:
Aschbacher--Smith 15.3.38, printed p.1136, and GLS3 §2.7.
-/

@[expose] public section
open scoped MatrixGroups
open Subgroup PerfectCentralCovering
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.DiagonalCenter
open PSL3.ExceptionalFourCover
open KernelModel.DiagonalWords

noncomputable def diagonalOverCanonical : GL (Fin 3) F :=
  GeneralLinearGroup.map Representation.SL2FourNatural.fieldEquiv.toRingHom
    KernelModel.DiagonalWords.diagonal

private theorem fieldSL_toGL (x : KernelModel.SL) :
    SpecialLinearGroup.toGL
      (SpecialLinearGroup.map Representation.SL2FourNatural.fieldEquiv.toRingHom x) =
    GeneralLinearGroup.map Representation.SL2FourNatural.fieldEquiv.toRingHom
      (SpecialLinearGroup.toGL x) := Units.ext rfl

theorem actor_eq_linear : actor = PSL3.OuterSolvable.linearConj F diagonalOverCanonical := by
  ext y
  obtain ⟨t, rfl⟩ := (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv).surjective y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center KernelModel.SL) t
  change (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv)
    ((PSL3.OuterSolvable.linearConj KernelModel.F KernelModel.DiagonalWords.diagonal)
      ((Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv).symm
        ((Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv)
          (QuotientGroup.mk x)))) = _
  have hfield (t : KernelModel.SL) :
      (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv) (QuotientGroup.mk t) =
        QuotientGroup.mk ((Atlas.fieldEquivSL 3 Representation.SL2FourNatural.fieldEquiv) t) := by
    simpa only [QuotientGroup.mk'_apply] using
      Atlas.fieldEquivPSL_mk 3 Representation.SL2FourNatural.fieldEquiv t
  rw [MulEquiv.symm_apply_apply, PSL3.OuterSolvable.linearConj_mk, hfield]
  change QuotientGroup.mk
    ((Atlas.fieldEquivSL 3 Representation.SL2FourNatural.fieldEquiv)
      (PSL3.OuterSolvable.linearConjSL KernelModel.F KernelModel.DiagonalWords.diagonal x)) =
    PSL3.OuterSolvable.linearConj F diagonalOverCanonical
      ((Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv) (QuotientGroup.mk x))
  rw [hfield, PSL3.OuterSolvable.linearConj_mk]
  congr 1
  change SpecialLinearGroup.map Representation.SL2FourNatural.fieldEquiv.toRingHom
    (PSL3.OuterSolvable.linearConjSL KernelModel.F KernelModel.DiagonalWords.diagonal x) =
    PSL3.OuterSolvable.linearConjSL F diagonalOverCanonical
      (SpecialLinearGroup.map Representation.SL2FourNatural.fieldEquiv.toRingHom x)
  apply SpecialLinearGroup.toGL_injective
  rw [fieldSL_toGL, PSL3.OuterSolvable.linearConjSL_toGL, map_mul, map_mul, map_inv,
    PSL3.OuterSolvable.linearConjSL_toGL, fieldSL_toGL]
  rfl

theorem diagonalOverCanonical_cube : diagonalOverCanonical ^ 3 = 1 := by
  have hd : KernelModel.DiagonalWords.diagonal ^ 3 = 1 := by
    apply Units.ext
    decide +kernel
  change (GeneralLinearGroup.map Representation.SL2FourNatural.fieldEquiv.toRingHom KernelModel.DiagonalWords.diagonal) ^ 3 = 1
  rw [← map_pow, hd, map_one]

theorem actor_cube : actor ^ 3 = 1 := by
  rw [actor_eq_linear, ← map_pow, diagonalOverCanonical_cube, map_one]

theorem diagonalOverCanonical_det_ne_one : GeneralLinearGroup.det diagonalOverCanonical ≠ 1 := by
  intro h
  rw [diagonalOverCanonical, GeneralLinearGroup.map_det] at h
  have h' := congrArg Units.val h
  have hd : (GeneralLinearGroup.det KernelModel.DiagonalWords.diagonal : KernelModel.F) = KernelModel.z := by
    decide +kernel
  change Representation.SL2FourNatural.fieldEquiv (GeneralLinearGroup.det KernelModel.DiagonalWords.diagonal : KernelModel.F) = 1 at h'
  rw [hd] at h'
  have hz : KernelModel.z = 1 := Representation.SL2FourNatural.fieldEquiv.injective
    (h'.trans (map_one Representation.SL2FourNatural.fieldEquiv).symm)
  exact (by decide +kernel : KernelModel.z ≠ 1) hz

theorem units_three_cases (d : Fˣ) (hd : d ≠ 1) (u : Fˣ) :
    u = 1 ∨ u = d ∨ u = d ^ 2 := by
  classical
  have ho : orderOf d = 3 := orderOf_eq_prime (ProjectiveFixer.unit_cube d) hd
  have ht : zpowers d = ⊤ := (Subgroup.card_eq_iff_eq_top (zpowers d)).mp (by
    rw [Nat.card_zpowers, ho, Nat.card_units, card_F])
  have hf : IsOfFinOrder d := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨3, by decide, ProjectiveFixer.unit_cube d⟩
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp
    (hf.mem_zpowers_iff_mem_range_orderOf.mp (show u ∈ zpowers d by rw [ht]; trivial))
  have hn' : n < 3 := by simpa only [Finset.mem_range, ho] using hn
  interval_cases n
  · exact Or.inl (by simpa only [pow_zero] using he.symm)
  · exact Or.inr (Or.inl (by simpa only [pow_one] using he.symm))
  · exact Or.inr (Or.inr he.symm)

/-- The two powers of the concrete diagonal actor exhaust the non-inner cubic
standard kernel actions. -/
theorem kernel_generation_of_concrete_actor
    (hact : (universalProjection PSL).ker ≤ kernelSquaresAndDisplacements actor)
    (hact2 : (universalProjection PSL).ker ≤ kernelSquaresAndDisplacements (actor ^ 2))
    (β : MulAut PSL) (hβ : β ∈ PSL3.OuterSolvable.standard F) (h3 : β ^ 3 = 1)
    (hout : β ∉ MulAut.innerSubgroup PSL) :
    (universalProjection PSL).ker ≤ kernelSquaresAndDisplacements β := by
  obtain ⟨u, g, hu, rfl⟩ := cubic_standard_eq_diagonal_mul_inner β hβ h3 hout
  rw [kernelSquaresAndDisplacements_mul_inner]
  have ha := linearConj_eq_diagonal_mul_inner diagonalOverCanonical
  have ha2 := linearConj_eq_diagonal_mul_inner (diagonalOverCanonical ^ 2)
  obtain ⟨a, ha⟩ := ha
  obtain ⟨a2, ha2⟩ := ha2
  rw [← actor_eq_linear] at ha
  rw [map_pow, ← actor_eq_linear, map_pow] at ha2
  rcases units_three_cases (GeneralLinearGroup.det diagonalOverCanonical)
    diagonalOverCanonical_det_ne_one u with h | h | h
  · exact (hu h).elim
  · subst u
    rwa [ha, kernelSquaresAndDisplacements_mul_inner] at hact
  · subst u
    rwa [ha2, kernelSquaresAndDisplacements_mul_inner] at hact2
end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.DiagonalCenter
