module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.CentralKernel.Quotient
public import Theory.GroupTheory.PResidual.CentralSplitSylow

/-!
# Local inputs for the G.2.5 central-kernel argument

The rank-three Sylow lift needs the point radical and one additional
root group. `HasRootLift` records their actual positions and images in
I/P; it does not assume their join is Sylow or that the kernel vanishes.
Transfer proves those consequences once I/P is two-perfect. The latter
follows from O²(L)=L when the point-stabilizer action puts U⁺ inside L⁺.

The two source inputs remain explicit here. Their construction is a
separate obligation, and this conditional result is not G.2.5(3).
Source: Aschbacher–Smith, printed pp.333–336, G.2.3 and G.2.5.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel
open Setup

variable {G : Type*} [Group G] [Finite G]
  {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)
  [((WProduct D g h).subgroupOf (I D g h)).Normal]

/-- A root factor complementary to the marked point radical in a Sylow
image. Every containment is in the actual quotient I/P. -/
def HasRootLift (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) : Prop :=
  ∃ R : Sylow 2 (Quotient D g h), ∃ B : Subgroup (Quotient D g h),
    image D g h D.U ≤ R ∧ B ≤ R ∧
    B ≤ normalizer (image D g h D.U : Set (Quotient D g h)) ∧
    Disjoint B (starMap d hUT hstar).ker ∧
    Disjoint ((image D g h D.U).map (starMap d hUT hstar))
      (B.map (starMap d hUT hstar)) ∧
    (R : Subgroup (Quotient D g h)).map (starMap d hUT hstar) ≤
      (image D g h D.U).map (starMap d hUT hstar) ⊔ B.map (starMap d hUT hstar)

/-- Transfer removes the exact central kernel once the local constructions
have been supplied. No assertion about the full center of SL₃(F) is needed. -/
theorem starMap_ker_eq_bot_of_rootLift (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (hres : IsPPerfect 2 (Quotient D g h))
    (hroot : HasRootLift d hUT hstar) : (starMap d hUT hstar).ker = ⊥ := by
  obtain ⟨R, B, hAR, hBR, hBA, hB, hAB, hcover⟩ := hroot
  exact ker_eq_bot_of_split_sylow_of_isPPerfect hres (starMap d hUT hstar)
    (starMap_ker_le_center d hUT hstar) (starMap_ker_isPGroup d hUT hstar)
    R (image D g h D.U) B hAR hBR hBA
    (image_U_disjoint_ker d hUT hstar) hB hAB hcover

/-- The actual source consumer of the two local constructions. The
point-stabilizer argument supplies hUL and the flag calculation supplies hroot. -/
theorem core_eq_product_of_local_inputs (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (hUL : image D g h D.U ≤ image D g h D.L)
    (hroot : HasRootLift d hUT hstar) : S D g h = WProduct D g h :=
  core_eq_product_of_ker_eq_bot d hUT hstar
    (starMap_ker_eq_bot_of_rootLift d hUT hstar
      (isPPerfect_of_image_U_le_image_L d hstar hUL) hroot)

/-- The ordered product retains the original g and h after the central
kernel has been removed. -/
theorem core_eq_ordered_product_of_local_inputs (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (hUL : image D g h D.U ≤ image D g h D.L)
    (hroot : HasRootLift d hUT hstar) :
    (S D g h : Set G) = (W D g h : Set G) * (conjugate (W D g h) g : Set G) *
      (conjugate (W D g h) h : Set G) := by
  rw [core_eq_product_of_local_inputs d hUT hstar hUL hroot]
  exact d.WProduct_eq_product hUT hstar.ge

end CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel
