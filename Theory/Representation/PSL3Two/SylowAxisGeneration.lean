module
public import Theory.Representation.PSL3Two.NaturalPlaneStabilizer
public import Theory.SpecificGroups.PSL3Two.Parabolics.NaturalPointResidual
public import Theory.Representation.BinaryOffender.PermutedSupports

/-!
# Sylow fixed-space and common-axis generation in SL₃(2)

A Sylow two-subgroup fixes a nonzero natural vector. The corresponding
point radical lies in that Sylow subgroup and fixes only this nonzero
vector, so the whole point parabolic fixes the Sylow fixed space. The
common-axis plane parabolic contains a cubic moving this vector. Maximality
of the point parabolic therefore gives generation by the pointwise fixer
and the normalizer of the same common-axis four-group.

Source: Aschbacher--Smith 13.1.9, printed p.871, final parabolic generation.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinearThree
open Matrix.PSL3Two

private theorem point_coatom (v : Vector) (hv : v ≠ 0) :
    IsCoatom (naturalPoint v) := by
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three ![1,0,0] v (by decide) hv
  have he : naturalPoint ![1,0,0] = pointParabolicSL := by
    rw [← Fano.stabilizer_flagPoint_SL]
    ext a
    change a • (![1,0,0] : Vector) = ![1,0,0] ↔ a • flagPoint = flagPoint
    exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
  change W g ![1,0,0] = v at hg
  rw [←hg,naturalPoint_action,he]
  exact ((MulAut.conj g).mapSubgroup.isCoatom_iff pointParabolicSL).mpr isCoatom_pointParabolicSL

/-- The pointwise fixer of the Sylow fixed space and the normalizer of its
common-axis four-group generate the full natural SL₃(2). -/
theorem sylow_fixed_axis_generation (P : Sylow 2 Group) (A : Subgroup Group)
    (hAP : A ≤ (P : Subgroup Group))
    (hdim : Module.finrank (ZMod 2) (fixedSpace W A) = 2)
    (haxis : A = (NaturalPlaneStabilizer.stabilizer (fixedSpace W A)).pCoreIn 2) :
    subspaceKernel W (fixedSpace W (P : Subgroup Group)) ⊤ ⊔
      normalizer (A : Set Group) = ⊤ := by
  obtain ⟨v,_,hv,hfix⟩ := PermutedSupports.exists_nonzero_fixed W
    (P : Subgroup Group) P.isPGroup' ⊤ top_ne_bot
    (by apply le_subspaceStabilizer; intros; trivial)
  have hPN : (P : Subgroup Group) ≤ naturalPoint v := fun p hp => hfix ⟨p,hp⟩
  have hcore : (naturalPoint v).pCoreIn 2 ≤ (P : Subgroup Group) := by
    have hh := pCoreIn_le_sylow (naturalPoint v) (P.subtype hPN)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hPN] using hh
  have hpoint : naturalPoint v ≤ subspaceKernel W (fixedSpace W (P : Subgroup Group)) ⊤ := by
    intro g hg
    refine ⟨mem_top _,fun w hw => ?_⟩
    by_cases hz : w = 0
    · simp only [hz,map_zero]
    · have he := naturalPoint_core_fixed_unique v w hv hz (fun a ha => hw ⟨a,hcore ha⟩)
      rw [he]
      exact hg
  have hvA : v ∈ fixedSpace W A := fun a => hfix ⟨a,hAP a.property⟩
  obtain ⟨a,_,hamove⟩ := NaturalPlaneStabilizer.exists_cubic_moving
    (fixedSpace W A) hdim v hvA hv
  have hnorm : (a : Group) ∈ normalizer (A : Set Group) := by
    apply (congrArg (fun B : Subgroup Group => normalizer (B : Set Group)) haxis).ge
    exact (NaturalPlaneStabilizer.stabilizer (fixedSpace W A)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)) a.property
  have hlt : naturalPoint v < subspaceKernel W (fixedSpace W (P : Subgroup Group)) ⊤ ⊔
      normalizer (A : Set Group) := by
    apply lt_of_le_of_ne (hpoint.trans le_sup_left)
    intro he
    have ha := he.ge (mem_sup_right hnorm)
    exact hamove ha
  exact (point_coatom v hv).2 _ hlt
end BinaryLinearThree
