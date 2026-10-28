module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairCore
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.ResidualAction
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
-- Internal continuation of the same relative joint-action construction.
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourProduct
import all CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.Kernel

/-!
# The degree-two pair's joint section action

The exact R-kernel on B/U extends across its original I-conjugate because
the two factors generate O₂(I). The two component images commute; I/O₂(I)
is the concrete centerless PSL₂(4), so the images intersect trivially.
The resulting action on the literal P/U has kernel O₂(RI)=P O₂(R), and
its quotient product is marked on the original representatives r i.

The private implementation import reuses the relative-normality and
quotient transport proof already shared by the Hermitian branch. No
Hermitian representation assumption enters this theorem. Its row-specific
B/U premise is discharged in NonFFSourceMathieuM24Section by the native
trio marking. Final classification remains with qt-d-1222-nonff-mathieu.
Source: Aschbacher--Smith E.2.14 and 8.2.8(4), printed pp.228,718,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
open ChapterE Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer.SmallOvergroups
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- The two original quotient actions commute and have the exact product
kernel on P/U. The only row-specific input is the earlier kernel on B/U. -/
theorem selected_two_joint_section {H T M V I : Subgroup G}
    [IsElementaryAbelian 2 V] {i : I} {S : Sylow 2 I}
    (s : Selected H T M V I 2 i S) (R U : Subgroup G)
    (hUZ : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hRI : R ≤ normalizer (I : Set G)) (hRU : R ≤ normalizer (U : Set G))
    (hIC : I ≤ centralizer (U : Set G)) (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2)
    (hB : ∀ r : R, (∀ b : ↥(V ⊓ I.pCoreIn 2), ⁅(r : G),(b : G)⁆ ∈ U) ↔
      r ∈ pCore 2 R) :
    let Y := R ⊔ I
    ∃ hYP : Y ≤ normalizer (I.pCoreIn 2 : Set G),
      ∃ hYU : Y ≤ normalizer (U : Set G),
        ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
          let f := sectionAction Y (I.pCoreIn 2) U hYP hYU
          f.ker = pCore 2 Y ∧ Y.pCoreIn 2 = I.pCoreIn 2 ⊔ R.pCoreIn 2 ∧
          (f.comp (inclusion le_sup_left)).ker = pCore 2 R ∧
          (f.comp (inclusion le_sup_right)).ker = pCore 2 I ∧
          ∃ e : (Y ⧸ pCore 2 Y) ≃* (R ⧸ pCore 2 R) × (I ⧸ pCore 2 I),
            ∀ (r : R) (a : I), e (QuotientGroup.mk' (pCore 2 Y)
              (inclusion le_sup_left r * inclusion le_sup_right a)) =
              (QuotientGroup.mk' (pCore 2 R) r, QuotientGroup.mk' (pCore 2 I) a) := by
  obtain ⟨hUN,hI⟩ := selected_two_section_kernel s hUZ
  obtain ⟨e⟩ := selected_two_quotient s
  have hz : center (I ⧸ pCore 2 I) = ⊥ :=
    Chapter8.Section02.Normalizer.TensorRecognition.centerless_of_equiv e.symm
      (Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot (F := BinaryGaloisField 2))
  have hIP : I ≤ normalizer (I.pCoreIn 2 : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hPi : (I.pCoreIn 2).map (MulAut.conj i.val⁻¹).toMonoidHom = I.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (hIP (I.inv_mem i.property))
  have hP : (V ⊓ I.pCoreIn 2) ⊔ (V ⊓ I.pCoreIn 2).map
      (MulAut.conj i.val⁻¹).toMonoidHom = I.pCoreIn 2 := by
    rw [map_inf _ _ _ (MulAut.conj i.val⁻¹).injective,hPi]
    exact (selected_two_core_product s).symm
  exact Chapter8.Section02.HermitianSource.pair_join_action R I V U hRI hRU hIC hcomm i hP hB hUN hI hz

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
