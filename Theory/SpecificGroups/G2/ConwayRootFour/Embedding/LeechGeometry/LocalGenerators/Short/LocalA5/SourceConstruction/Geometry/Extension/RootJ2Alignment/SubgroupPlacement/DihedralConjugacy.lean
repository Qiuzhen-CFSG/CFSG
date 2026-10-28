module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.Transport
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.DihedralConjugacy.Normalizer
public import Theory.GroupTheory.DihedralSylowConjugacy
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Conjugacy of marked D₁₀ subgroups in SL₃(4)

The exact block model of `Transport` is faithful, and the order of GL₃(4)
shows that its order-five subgroup is Sylow in SL₃(4). Its normalizer has
order thirty by `DihedralConjugacy.Normalizer`, so the reflection subgroups
are Sylow two-subgroups there. Two successive Sylow conjugations therefore
conjugate every faithful D₁₀ subgroup to the marked model.

The conjugacy theorem requires only injectivity of the given dihedral map.
Its final application uses the literal pullback and quotient maps from
`Transport`, discharging the matrix-conjugacy input of subgroup placement.
The ambient cubic geometry and simultaneous placement remain with their owners.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 49.5, pp.283–284,
local placement using 48.3, 49.2 and 48.8. The field comparison and marked
matrices are exactly those of `SourceConstruction.Placement`.
-/

open Matrix Atlas.Conway
open scoped MatrixGroups
set_option backward.isDefEq.respectTransparency false
public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction

/-- The marked block model is faithful before choosing any long frame. -/
theorem rootJ2LongDihedralModel_injective : Function.Injective rootJ2LongDihedralModel := by
  have hb : Function.Injective block := by
    intro a b h
    apply Subtype.ext
    ext i j
    have he := congrArg (fun M : SL(3,F) => M.val i.succ j.succ) h
    fin_cases i <;> fin_cases j <;> simpa [block, blockMatrix] using he
  exact hb.comp (slEquiv.injective.comp dihedralModel_injective)

/-- The GL₃(4) order formula makes the marked five-subgroups Sylow in SL₃(4). -/
theorem rootJ2Long_five_sq_not_dvd : ¬ 5 ^ 2 ∣ Nat.card SL(3,F) := by
  let := Fintype.ofFinite F
  have hF : Nat.card F = 4 := GaloisField.card 2 2 (by decide)
  have hGL : Nat.card (GL (Fin 3) F) = 181440 := by
    rw [Matrix.card_GL_field]
    simp only [← Nat.card_eq_fintype_card, hF, Fin.prod_univ_three]
    norm_num
  intro h
  have hd := h.trans (Subgroup.card_dvd_of_injective
    (Matrix.SpecialLinearGroup.toGL : SL(3,F) →* GL (Fin 3) F)
    Matrix.SpecialLinearGroup.toGL_injective)
  rw [hGL] at hd
  norm_num at hd

/-- Matrix subgroup conjugacy reduced to the two-part of the concrete
five-normalizer. The marked model satisfies this premise unconditionally. -/
theorem rootJ2LongDihedral_conjugacy_of_normalizer_twoPart
    (hN : ¬ 4 ∣ Nat.card (Subgroup.normalizer
      (Subgroup.zpowers (rootJ2LongDihedralModel (.r 1)) : Set SL(3,F))))
    (j : DihedralGroup 5 →* SL(3,F)) (hj : Function.Injective j) :
    ∃ A : SL(3,F), j.range.map (MulAut.conj A).toMonoidHom =
      rootJ2LongDihedralModel.range :=
  DihedralSylowConjugacy.ranges_conjugate (by decide) rootJ2Long_five_sq_not_dvd
    rootJ2LongDihedralModel j rootJ2LongDihedralModel_injective hj hN

/-- Every faithful D₁₀ subgroup of SL₃(4) is conjugate to the original marked
block model. The equality concerns subgroups, without fixing their generators. -/
theorem rootJ2LongDihedral_conjugacy
    (j : DihedralGroup 5 →* SL(3,F)) (hj : Function.Injective j) :
    ∃ A : SL(3,F), j.range.map (MulAut.conj A).toMonoidHom =
      rootJ2LongDihedralModel.range :=
  rootJ2LongDihedral_conjugacy_of_normalizer_twoPart
    rootJ2LongFiveNormalizer_four_not_dvd j hj

/-- Apply the matrix reduction to the literal pulled-back root J₂ subgroup.
This supplies the dihedral mark used in simultaneous placement, conditional
on the five-normalizer bound and containment in the long subgroup. -/
theorem exists_rootJ2DihedralMark_of_long_range_and_normalizer_twoPart
    (hN : ¬ 4 ∣ Nat.card (Subgroup.normalizer
      (Subgroup.zpowers (rootJ2LongDihedralModel (.r 1)) : Set SL(3,F))))
    (L : LongFrame)
    (f : Sporadic.LeechRelated.J2.Carrier →* LeechCentralQuotient)
    (hf : Function.Injective f)
    (hB : Sporadic.LeechRelated.J2.RecognitionGeometry.B.map f ≤ L.long.range) :
    ∃ A : SL(3,F), (dihedralLift L).range ≤
      Sporadic.LeechRelated.J2.RecognitionGeometry.B.map
        ((MulAut.conj (L.long A)).toMonoidHom.comp f) := by
  let j := rootJ2DihedralPullback L f hB
  obtain ⟨A, hA⟩ := rootJ2LongDihedral_conjugacy_of_normalizer_twoPart hN j
    (rootJ2DihedralPullback_injective L f hf hB)
  refine ⟨A, ?_⟩
  rintro c ⟨d, rfl⟩
  have hd : rootJ2LongDihedralModel d ∈ j.range.map (MulAut.conj A).toMonoidHom := by
    rw [hA]
    exact ⟨d, rfl⟩
  obtain ⟨a, ⟨b, rfl⟩, hab⟩ := hd
  refine ⟨Sporadic.LeechRelated.J2.RecognitionGeometry.dihedralHom b, ?_, ?_⟩
  · rw [← Sporadic.LeechRelated.J2.RecognitionGeometry.dihedralHom_range]
    exact ⟨b, rfl⟩
  · have hh := congrArg L.long hab
    change L.long (A * j b * A⁻¹) = L.long (rootJ2LongDihedralModel d) at hh
    change L.long A * f (Sporadic.LeechRelated.J2.RecognitionGeometry.dihedralHom b) *
      (L.long A)⁻¹ = dihedralLift L d
    simpa only [map_mul, map_inv, j, rootJ2DihedralPullback_spec,
      rootJ2LongDihedralModel_apply] using hh

/-- Align the literal root J₂ dihedral image inside the long subgroup.
The matrix-normalizer premise is discharged; only the ambient containment
needed to form the pullback remains. -/
theorem exists_rootJ2DihedralMark_of_long_range
    (L : LongFrame)
    (f : Sporadic.LeechRelated.J2.Carrier →* LeechCentralQuotient)
    (hf : Function.Injective f)
    (hB : Sporadic.LeechRelated.J2.RecognitionGeometry.B.map f ≤ L.long.range) :
    ∃ A : SL(3,F), (dihedralLift L).range ≤
      Sporadic.LeechRelated.J2.RecognitionGeometry.B.map
        ((MulAut.conj (L.long A)).toMonoidHom.comp f) :=
  exists_rootJ2DihedralMark_of_long_range_and_normalizer_twoPart
    rootJ2LongFiveNormalizer_four_not_dvd L f hf hB

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
