module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Actions

/-!
# Applying G.2.5(1–3) to the literal recognition sections

The structural theorem supplies L≤I, normalization of all three marked
U-groups, their ordered core product, and the star comparison used by the
independent recognition branch. Thus the literal upper quotient is elementary
abelian and the two-core centralizes the lower quotient. The actual quotient
actions then require only the independent I-invariance of S₃ in addition to
the two permitted earlier G.2.2 outputs. No comparison or structural premise
is assumed in these applications.

The I-invariance premise belongs to the projective recognition argument;
these applications do not assert G.2.5(6–7). The final assembly owner is
`qt-g02-linear-three`, with G.2.2 supplied by `qt-g02-central-closure` under
`qt-g-02`.

Source: Aschbacher–Smith, G.2.5, printed pp.335–336 / PDF pp.346–347.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree
open Setup
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G]
  {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)

include d

/-- Construct the recognition branch's comparison using the original star map. -/
noncomputable def sourceStarComparison (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    Recognition.StarComparison D g h (d.L_le_I hUT hf) where
  equivalence := (d.sourceCoreQuotientEquiv hUT hf).trans d.model.symm
  agrees l := by
    change d.model.symm (d.sourceCoreQuotientEquiv hUT hf
      (QuotientGroup.mk' (pCore 2 (I D g h)) (inclusion (d.L_le_I hUT hf) l))) = _
    rw [d.sourceCoreQuotientEquiv_on_L, d.model.symm_apply_apply]

/-- The recognition projection is the restriction of the literal star projection. -/
theorem sourceStarComparison_projection_apply (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (i : I D g h) :
    (d.sourceStarComparison hUT hf).projection i =
      d.IStarProjection hUT (d.star_I_eq_star_L hUT hf) i := by
  change d.model.symm (d.sourceCoreQuotientEquiv hUT hf
    (QuotientGroup.mk' (pCore 2 (I D g h)) i)) = _
  rw [d.sourceCoreQuotientEquiv_mk, d.model.symm_apply_apply]

/-- Relative normality of the actual third layer inside S. -/
theorem S₃_normal_in_S (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    ((S₃ D g h).subgroupOf (S D g h)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (Recognition.Hypothesis.core_normalizes_third d (d.L_le_I hUT hf)
      (d.S_normalizes_U hUT hf) (d.S_normalizes_marked hUT hf g d.g_mem)
      (d.S_normalizes_marked hUT hf h d.h_mem))

/-- Apply the proved ordered core product to the elementary upper-section theorem. -/
theorem upper_elementary_of_source (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    letI := d.S₃_normal_in_S hUT hf
    IsElementaryAbelian 2 (UpperQuotient D g h) := by
  let := d.S₃_normal_in_S hUT hf
  exact Recognition.Hypothesis.upper_elementary d hUT hf (d.L_le_I hUT hf)
    (d.S_normalizes_U hUT hf) (d.S_normalizes_marked hUT hf g d.g_mem)
    (d.S_normalizes_marked hUT hf h d.h_mem) (d.S_eq_product hUT hf)

/-- Apply the proved three-factor generation to the lower-section kernel bound. -/
theorem core_centralizes_lower_of_source (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    ⁅S D g h, S₃ D g h⁆ ≤ S₂ D g h :=
  Recognition.Hypothesis.core_centralizes_lower d hUT hf (d.L_le_I hUT hf)
    (d.S_normalizes_U hUT hf) (d.S_normalizes_marked hUT hf g d.g_mem)
    (d.S_normalizes_marked hUT hf h d.h_mem) (d.S_eq_WProduct hUT hf)

/-- The lower action now needs only the independently proved I-invariance of S₃.
Its projection and its coordinates are the original quotient maps. -/
theorem lower_action_of_source (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hN : I D g h ≤ normalizer (S₃ D g h : Set G)) :
    letI := Recognition.Hypothesis.lower_normal d hUT hf (d.L_le_I hUT hf)
    letI := Recognition.Hypothesis.lower_elementary d hUT hf (d.L_le_I hUT hf)
    ∃ (σ : Representation (ZMod 2) (D.star D.L) (Additive (LowerQuotient D g h)))
      (s : Representation.BinaryConjugationSection (I D g h) (S₃ D g h) (S₂ D g h)
        (σ.comp (d.sourceStarComparison hUT hf).projection)),
      ∀ a : S₃ D g h, (s.coordinates a).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) a) :=
  Recognition.Hypothesis.lower_action d hUT hf (d.L_le_I hUT hf)
    (d.S_normalizes_U hUT hf) (d.S_normalizes_marked hUT hf g d.g_mem)
    (d.S_normalizes_marked hUT hf h d.h_mem) (d.S_eq_WProduct hUT hf) hN
    (d.sourceStarComparison hUT hf)

/-- The upper action uses the same constructed star comparison and literal
quotient coordinates, with no structural input left for recognition to prove. -/
theorem upper_action_of_source (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hN : I D g h ≤ normalizer (S₃ D g h : Set G)) :
    letI := d.S₃_normal_in_S hUT hf
    letI := d.upper_elementary_of_source hUT hf
    ∃ (σ : Representation (ZMod 2) (D.star D.L) (Additive (UpperQuotient D g h)))
      (s : Representation.BinaryConjugationSection (I D g h) (S D g h) (S₃ D g h)
        (σ.comp (d.sourceStarComparison hUT hf).projection)),
      ∀ a : S D g h, (s.coordinates a).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) a) := by
  let := d.S₃_normal_in_S hUT hf
  let := d.upper_elementary_of_source hUT hf
  exact Recognition.Hypothesis.upper_action d hUT hf (d.L_le_I hUT hf)
    (d.S_normalizes_U hUT hf) (d.S_normalizes_marked hUT hf g d.g_mem)
    (d.S_normalizes_marked hUT hf h d.h_mem) (d.S_eq_product hUT hf) hN
    (d.sourceStarComparison hUT hf)

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree
