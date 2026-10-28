module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Marking.Basic
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Center.LineRadical

/-!
# The line residual centralizes the common Sylow center

The full line radical is the image of the canonical two-core of the left
residual. Normality puts it inside the marked Sylow, using the exact residual
and parabolic subtype maps. An element of the Sylow center therefore centralizes
this radical and belongs to the left residual. The faithful radical–SU₃
calculation then makes it central in that residual: its Levi coordinate is
trivial and its radical vector coordinate is zero, while SU₃ fixes its scalar.

This proves the centralization convention for the actual line-side residual
and the actual embedded center of the common Sylow, with no additional premise.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, F.1.12(I),
case (7) and its labeling convention, printed pp.262--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Theory.SpecificGroups.UnitaryFive
variable (M : Model 4)

/-- The whole line radical lies in the concrete common Sylow, in the common carrier. -/
theorem lineUnipotent_carrier_le_flagTwoSubgroup :
    M.lineUnipotent.map M.leftParabolic.subtype ≤ M.flagTwoSubgroup := by
  rw [← M.map_leftCore_subtype, Subgroup.map_map, ← M.leftLocalSylow_carrier_map]
  exact Subgroup.map_mono (pCore_isPGroup.le_sylow_of_normal M.leftLocalSylow)

/-- F.1.12(I): the actual line residual has the centralizing label `L₁`. -/
theorem leftLocalImage_le_centralizer_flagCenter :
    M.leftLocalImage ≤ Subgroup.centralizer (M.flagCenter : Set M.Carrier) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  let zP : M.leftParabolic := ⟨z.val, (M.flagTwoSubgroup_le_overlap z.property).1⟩
  have hzL : zP ∈ M.lineRadicalLeviSubgroup := by
    rw [← M.leftLocal_eq_lineRadicalLeviSubgroup]
    exact M.flagLeft_le_leftLocal z.property
  have hgL : g ∈ M.lineRadicalLeviSubgroup := by
    rwa [← M.leftLocal_eq_lineRadicalLeviSubgroup]
  have hzC : zP ∈ Subgroup.centralizer (M.lineUnipotent : Set M.leftParabolic) := by
    intro u hu
    apply Subtype.ext
    exact congrArg (fun t : M.flagTwoSubgroup => (t : M.Carrier))
      (Subgroup.mem_center_iff.mp hz
        ⟨u.val, M.lineUnipotent_carrier_le_flagTwoSubgroup ⟨u, hu, rfl⟩⟩)
  obtain ⟨c, hc⟩ := M.exists_lineTraceOne
  have h := Flag.Center.commute_of_centralizes_projectiveUnipotent M.form c hc M.matrix
    hzL hgL hzC
  exact (congrArg (fun a : M.leftParabolic => (a : M.Carrier)) h).symm

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
