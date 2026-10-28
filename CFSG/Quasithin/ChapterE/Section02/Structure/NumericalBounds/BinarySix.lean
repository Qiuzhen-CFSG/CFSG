module
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.BinaryExtension
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Classical
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Original binary derived symplectic generation bounds

A core-free minimal parabolic with normal simple binary symplectic component
has that component as its generalized Fitting subgroup. The complete
field-of-nine generation theorem applies to every actual outer extension.
For the original H, its simple component image in the literal star quotient
inherits this structure. The actual maximal core J is solvable, so rank-one
E-generation lifts through the whole kernel, including any odd central part.

Thus the derived PSp₄(2) row has n(H) ≤ 1 and is absent when n(H)>1.
No natural S₆ action or parameter equality across J is assumed. The numerical
argument needs no extra SQTK or earlier-classification hypothesis after the
actual binary model has been selected.

Source: Aschbacher–Smith E.1.10–14 and E.2.2, printed pp.212–216.
-/

public section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds
universe u
variable {H : Type u} [Group H] [Finite H]

/-- The actual core-free minimal source, with its original normal simple K. -/
theorem binary_six_corefree_isEGenerated
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hcore : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (e : K ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) :
    IsEGenerated 1 H := by
  let e' : K ≃* commutator (Sp (ZMod 2)) :=
    (e.trans Binary.projectiveDerivedEquivAlternatingSix).trans
      (Binary.derivedEquivAlternatingSix (F := ZMod 2) (by simp)).symm
  have ha := ValuesOdd.PSLTwoGeneration.nonabelian_of_model K (by decide)
    (ValuesEvenClassical.RankTwoUpper.SymplecticFour.isPSL_nine_of_binary_model
      (by simp : Nat.card (ZMod 2) = 2) e')
  have hF := (Sporadic.faithful_normal_structure T hP hcore K ha hgen).1
  let : IsSimpleGroup (generalizedFitting H) := by rw [hF]; infer_instance
  apply ValuesEvenClassical.RankTwoUpper.SymplecticFour.isEGenerated_binary_projective
    ((MulEquiv.subgroupCongr hF).trans e) T
  rwa [hF]

/-- Rank-one generation on the original component image in H/J. -/
theorem normal_binary_six_star_isEGenerated
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : Nonempty ((K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≃*
      commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    IsEGenerated 1 (H ⧸ ChapterB.minimalParabolicCore T hP) := by
  let J := ChapterB.minimalParabolicCore T hP
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let L := K.map (QuotientGroup.mk' J)
  obtain ⟨hLs,_,hLn,hLT⟩ := source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup L := hLs
  let : L.Normal := hLn
  have hstar := source_star_minimal_core_free T hP
  obtain ⟨e⟩ := hm
  exact binary_six_corefree_isEGenerated S hstar.1 hstar.2 L hLT e

/-- Generation lifts through the full original solvable maximal core. -/
theorem normal_binary_six_isEGenerated
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : Nonempty ((K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≃*
      commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    IsEGenerated 1 H := by
  let J := ChapterB.minimalParabolicCore T hP
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  exact IsEGenerated.of_normal_solvable_subgroup (by decide) J
    (normal_binary_six_star_isEGenerated T hP hs K hK hgen hm)

/-- The binary row cannot occur when the original parameter exceeds one. -/
theorem normal_binary_six_upper
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : Nonempty ((K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≃*
      commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    generationParameter H ≤ 1 :=
  generationParameter_le (by decide)
    (normal_binary_six_isEGenerated T hP hs K hK hgen hm)

end CFSG.Quasithin.ChapterE.Structure.NumericalBounds
