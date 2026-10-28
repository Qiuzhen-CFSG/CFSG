module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.Residuals

/-!
# Comparing the two terminal actors

The source commutator X_E = [X_E,J(T_E)] survives in the quotient and
shows that the Thompson image is nonabelian. It is a normal subgroup of
the offender actor. A nonabelian subgroup of S₃ is the whole group, and a
nonabelian normal subgroup of a quasisimple group is the whole group.
These facts identify the actual subgroups in those B.5.6 branches;
they do not identify the offender actor with the full ambient quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the final
proof of 15.3.1, printed p.1155, and B.5.6, printed pp.104–105.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection

private theorem subgroupOf_commutator_ne_bot {D : Type*} [Group D]
    {A B : Subgroup D} (hle : A ≤ B) (hc : ⁅A,A⁆ ≠ ⊥) :
    ⁅A.subgroupOf B, A.subgroupOf B⁆ ≠ ⊥ := by
  intro hz
  apply hc
  have h := congrArg (Subgroup.map B.subtype) hz
  simpa only [map_commutator, map_subgroupOf_eq_of_le hle, Subgroup.map_bot] using h

private theorem eq_of_subgroupOf_eq_top {D : Type*} [Group D]
    {A B : Subgroup D} (hle : A ≤ B) (ht : A.subgroupOf B = ⊤) : A = B := by
  have h := congrArg (Subgroup.map B.subtype) ht
  simpa only [map_subgroupOf_eq_of_le hle, ← MonoidHom.range_eq_map, range_subtype] using h

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H} (d : SourceInput V)
include d

namespace SourceInput

/-- The nontrivial source commutator lies in the derived group of the
Thompson image. This is stronger than mere nontriviality of that image. -/
theorem thompson_image_commutator_ne_bot :
    ⁅(thompsonGroup H).map coreProjection, (thompsonGroup H).map coreProjection⁆ ≠ ⊥ := by
  intro hz
  rw [← map_commutator] at hz
  apply d.second_escape
  calc
    d.XE = ⁅d.XE, Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup H)⁆ := d.second_commutator
    _ ≤ ⁅thompsonGroup H, thompsonGroup H⁆ :=
      commutator_mono d.second_le_thompson (Stellmacher.elementaryAbelianMaxJ_sylow_le_top d.T)
    _ ≤ (coreProjection (H := H)).ker := (Subgroup.map_eq_bot_iff _).mp hz
    _ = pCore 2 H := QuotientGroup.ker_mk' _

/-- The strict source inequality excludes F.6.18(1), in either ordering
of the two generators, since that row has both local cores trivial. -/
theorem first_quotient_core_ne_bot : pCore 2 (d.G1.map coreProjection) ≠ ⊥ := by
  intro hz
  have h := d.local_core_strict
  have he : (d.G1.map coreProjection).pCoreIn 2 = ⊥ := by
    rw [pCoreIn, hz, Subgroup.map_bot]
  rw [he] at h
  exact (not_lt_bot h)

omit [Finite H] in
/-- Relative normality of the Sylow Thompson group is preserved under the
same quotient map as both local embeddings. -/
theorem sylow_thompson_image_normalized : d.G1.map coreProjection ≤
    normalizer ((Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup H)).map coreProjection :
      Set (coreQuotient H)) :=
  (map_mono d.thompson_normalized).trans (le_normalizer_map _)

/-- The embedded residual of the marked first local image is the image of Y_F. -/
theorem first_image_residual :
    (pResidual 2 (d.G1.map coreProjection)).map (d.G1.map coreProjection).subtype =
      d.YF.map coreProjection := by
  rw [← map_embedded_pResidual, d.first_residual]

variable [IsElementaryAbelian 2 (moduleClosure V)]

/-- In the S₃ offender case the source commutator identifies the Thompson
image with that actor as an actual subgroup of the quotient. -/
theorem thompson_image_eq_symmetricThree_offender
    (e : d.offenderGroup ≃* Equiv.Perm (Fin 3)) :
    (thompsonGroup H).map coreProjection = d.offenderGroup := by
  let A := ((thompsonGroup H).map coreProjection).subgroupOf d.offenderGroup
  have hn : ⁅A,A⁆ ≠ ⊥ :=
    subgroupOf_commutator_ne_bot d.thompson_image_le_offender d.thompson_image_commutator_ne_bot
  have hm : ⁅A.map e.toMonoidHom, A.map e.toMonoidHom⁆ ≠ ⊥ := by
    rw [← map_commutator]
    exact fun h => hn ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h)
  have ht : A.map e.toMonoidHom = ⊤ := by
    simpa only [sup_idem] using sup_eq_top_of_symmetricThree_commutator_ne_bot _ _ hm
  have hA : A = ⊤ := map_injective (f := e.toMonoidHom) e.injective (by
    rw [map_top_of_surjective e.toMonoidHom e.surjective]; exact ht)
  exact eq_of_subgroupOf_eq_top d.thompson_image_le_offender hA

/-- The S₃ equivalence is now on the correct actor for `symmetricThree_branch`. -/
noncomputable def thompsonEquivSymmetricThree
    (e : d.offenderGroup ≃* Equiv.Perm (Fin 3)) :
    (thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3) :=
  (MulEquiv.subgroupCongr (d.thompson_image_eq_symmetricThree_offender e)).trans e

/-- A quasisimple offender actor has no proper nonabelian normal subgroup,
so in this branch it too is exactly the Thompson image. -/
theorem thompson_image_eq_quasisimple_offender (hq : IsQuasisimple d.offenderGroup) :
    (thompsonGroup H).map coreProjection = d.offenderGroup := by
  let A := ((thompsonGroup H).map coreProjection).subgroupOf d.offenderGroup
  let _ : IsQuasisimple d.offenderGroup := hq
  have hn : ⁅A,A⁆ ≠ ⊥ :=
    subgroupOf_commutator_ne_bot d.thompson_image_le_offender d.thompson_image_commutator_ne_bot
  rcases IsQuasisimple.normal_le_center_or_eq_top A with hc | ht
  · exact (hn (commutator_eq_bot_iff_le_centralizer.mpr
      (hc.trans (center_le_centralizer _)))).elim
  · exact eq_of_subgroupOf_eq_top d.thompson_image_le_offender ht

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
