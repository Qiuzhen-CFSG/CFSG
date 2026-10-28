module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reference.ColumnDuality
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reference.PairQuintet.Action
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reference.PairQuintet.Geometry
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.Spaces

/-!
# The reference pair stabilizer is the native marked quintet

The actual degree-24 complement embedding sends degree-22 labels {4,9} to
{2,14}, the part of the source tetrad left after deleting {0,9}. The action
comparison and sextet recovery identify its full setwise stabilizer with
the marked quintet group. Native two-transitivity then transports the
reference pair {11,19} to {4,9}. The resulting multiplicative equivalence
retains the outer extension and discharges the pair-to-quintet input of the
reference-vector centralizer assembly.

Source: Aschbacher--Smith, H.14 setup and H.14.3, printed pp.396--397;
H.12.1, printed pp.393--394; and 14.4.12, printed pp.1011--1012
(1 March 2004 manuscript).
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu MathieuCode
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native

/-- The degree-22 labels of the two remaining points of the marked tetrad. -/
def pairQuintetLabels : Finset (Fin 22) := {4, 9}

private theorem labels_coordinates : pairQuintetLabels.map m22Coordinates = pairQuintetRemaining := by
  decide +kernel

/-- Transport every finite set by the actual moving-coordinate embedding. -/
theorem pairQuintetDesignEquiv_finset (g : MathieuCode.m22PairStabilizer) (B : Finset (Fin 22)) :
    (pairQuintetDesignEquiv g • B).map m22Coordinates = g.val • B.map m22Coordinates := by
  simp only [Finset.smul_finset_def, Finset.map_eq_image, Finset.image_image]
  congr 1
  funext a
  exact pairQuintetDesignEquiv_coordinates g a

/-- The source quintet is exactly the pair stabilizer in the compared action. -/
theorem pairQuintet_mem_iff_design (g : MathieuCode.m22PairStabilizer) :
    g ∈ M22Quintet.Q ↔ pairQuintetDesignEquiv g ∈ referencePairStabilizer pairQuintetLabels := by
  rw [pairQuintet_mem_iff_remaining]
  change _ ↔ pairQuintetDesignEquiv g • pairQuintetLabels = pairQuintetLabels
  rw [← (Finset.map_injective m22Coordinates).eq_iff, pairQuintetDesignEquiv_finset,
    labels_coordinates]

/-- Restrict the actual ambient comparison to the marked pair and quintet. -/
def pairQuintetMarkedEquiv : referencePairStabilizer pairQuintetLabels ≃* M22Quintet.Q where
  toFun g := ⟨pairQuintetDesignEquiv.symm g.val, (pairQuintet_mem_iff_design _).mpr (by
    simpa only [MulEquiv.apply_symm_apply] using g.property)⟩
  invFun g := ⟨pairQuintetDesignEquiv g.val, (pairQuintet_mem_iff_design _).mp g.property⟩
  left_inv g := Subtype.ext (pairQuintetDesignEquiv.apply_symm_apply g.val)
  right_inv g := Subtype.ext (pairQuintetDesignEquiv.symm_apply_apply g.val)
  map_mul' g h := Subtype.ext (map_mul pairQuintetDesignEquiv.symm g.val h.val)

/-- Native two-transitivity supplies an actual transporter from the reference
pair to the labels of the marked tetrad's remaining pair. -/
theorem referencePairQuintet_exists_transport :
    ∃ g : m22DesignAut, g • referencePair = pairQuintetLabels := by
  obtain ⟨g, hg11, hg19⟩ :=
    (MulAction.is_two_pretransitive_iff.mp m22_isTwoPretransitive)
      (by decide : (11 : Fin 22) ≠ 19) (by decide : (4 : Fin 22) ≠ 9)
  refine ⟨⟨g.val, M22_le_m22DesignAut g.property⟩, ?_⟩
  change g • referencePair = pairQuintetLabels
  simp only [referencePair, pairQuintetLabels, Finset.smul_finset_insert,
    Finset.smul_finset_singleton, hg11, hg19]

/-- Actual geometric equivalence of the reference pair stabilizer with the
full outer marked-quintet stabilizer. -/
def referencePairQuintetEquiv : referencePairStabilizer referencePair ≃* M22Quintet.Q :=
  (MulAction.stabilizerEquivStabilizer
    (Classical.choose_spec referencePairQuintet_exists_transport).symm).trans
    pairQuintetMarkedEquiv

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native

