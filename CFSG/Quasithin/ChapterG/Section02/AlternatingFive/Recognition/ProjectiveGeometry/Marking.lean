module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry.Standard
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.Action
public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.ProjectiveOrbit.Geometry
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# Marking the literal Sylow subgroup in the SL₂(4) model

Compose the source A₅ isomorphism with the genuine exceptional isomorphism
SL₂(4) ≃ A₅, and use Sylow conjugacy to send U* to the standard root group.
The original g moves the marked field point: a point stabilizer normalizes
its root, whereas the supplied Borel equality and the star kernel in T
would lift such normalization to normalization of the original V₁.

The Borel equality is the earlier output of `qt-g024-starred-borel`; the
source assembly owner retains its discharge. No recognition theorem or
assumed projective-map witness is used.

Source: Aschbacher–Smith, G.1.5(1,3), printed p.328, and G.2.4(1,6),
printed p.334, with the original g ∈ L − N_L(V₁).
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup Recognition Recognition.ProjectiveGeometry
open RankOneHigherFields.QuotientAction.Projective
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}
  (d : Hypothesis D g)
include d

omit d [Finite G] in
/-- The literal Sylow marking places U* inside L*. -/
theorem upper_star_U_le
    (hSylow : ∃ P : Sylow 2 (D.star D.L),
      (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U) :
    D.star D.U ≤ D.star D.L := by
  obtain ⟨P, hP⟩ := hSylow
  rw [← hP]
  exact map_subtype_le _

/-- An actual SL₂(4) model sending the original U* to the standard root. -/
theorem exists_upper_marked_model
    (hSylow : ∃ P : Sylow 2 (D.star D.L),
      (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U) :
    ∃ e : D.star D.L ≃* SL(2, F4),
      ((D.star D.U).subgroupOf (D.star D.L)).map e.toMonoidHom =
        RootGroup F4 standardPoint.val := by
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    field_card
  let e₀ : D.star D.L ≃* SL(2, F4) :=
    (d.model.trans eA.symm).trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F4)).symm
  obtain ⟨P, hP⟩ := hSylow
  have hP' : (P : Subgroup (D.star D.L)) = (D.star D.U).subgroupOf (D.star D.L) := by
    ext x
    constructor
    · intro hx
      change (x : D.Star) ∈ D.star D.U
      rw [← hP]
      exact ⟨x, hx, rfl⟩
    · intro hx
      change (x : D.Star) ∈ D.star D.U at hx
      rw [← hP] at hx
      obtain ⟨y, hy, he⟩ := hx
      exact (show y = x from Subtype.ext he) ▸ hy
  let R : Sylow 2 SL(2, F4) := P.mapSurjective (f := e₀.toMonoidHom) e₀.surjective
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq SL(2, F4) R
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F4 2)
  refine ⟨e₀.trans (MulAut.conj a), ?_⟩
  rw [root_standardPoint]
  have h := congrArg (fun Q : Sylow 2 SL(2, F4) => (Q : Subgroup SL(2, F4))) ha
  change ((P : Subgroup (D.star D.L)).map e₀.toMonoidHom).map
    (MulAut.conj a).toMonoidHom = Matrix.SpecialLinearGroup.upperUnipotent F4 at h
  rw [hP', map_map] at h
  exact h

private theorem upper_star_g_not_normalizer
    (hB : (D.star D.L₁).subgroupOf (D.star D.L) =
      normalizer (((D.star D.U).subgroupOf (D.star D.L)) : Set (D.star D.L))) :
    starProjection D (⟨g, d.g_mem⟩ : D.L) ∉
      normalizer (((D.star D.U).subgroupOf (D.star D.L)) : Set (D.star D.L)) := by
  intro hg
  rw [← hB] at hg
  obtain ⟨l, hl, he⟩ := hg
  have hlG : (l : G) ∈ D.G₁ := by
    obtain ⟨y, _, hyl⟩ := hl
    change (y : G) = (l : G) at hyl
    rw [← hyl]
    exact y.property.2
  obtain ⟨P, hP⟩ := d.setup.sylow_LT
  have hcore : D.LT.pCoreIn 2 ≤ D.G₁ :=
    (hP ▸ pCoreIn_le_sylow D.LT P).trans d.setup.T_normalizes_point
  have hdiff : (l : G)⁻¹ * g ∈ D.G₁ := by
    apply hcore
    refine ⟨l⁻¹ * ⟨g, (show D.L ≤ D.LT from le_sup_left) d.g_mem⟩, ?_, rfl⟩
    exact QuotientGroup.eq.mp he
  apply d.g_not_normalizes
  simpa only [mul_inv_cancel_left] using D.G₁.mul_mem hlG hdiff

/-- The original right conjugator moves the marked field point. -/
theorem upper_marked_point_ne
    (hB : (D.star D.L₁).subgroupOf (D.star D.L) =
      normalizer (((D.star D.U).subgroupOf (D.star D.L)) : Set (D.star D.L)))
    {F : Type*} [Field F] (e : D.star D.L ≃* SL(2, F)) (A : ProjectivePoint F)
    (hroot : ((D.star D.U).subgroupOf (D.star D.L)).map e.toMonoidHom = RootGroup F A.val) :
    A.val ≠ A.val.map (Representation.specialLinearNatural 2
      (e (starProjection D (⟨g, d.g_mem⟩ : D.L))⁻¹)) := by
  intro he
  have hn := mem_root_normalizer_of_map_eq A.val
    (e (starProjection D (⟨g, d.g_mem⟩ : D.L))⁻¹) he.symm
  change _ ∈ normalizer (RootGroup F A.val : Set SL(2, F)) at hn
  rw [← hroot, ← map_normalizer_eq_of_bijective _ e.bijective] at hn
  have hh := mem_map_equiv.mp hn
  simp only [map_inv, MulEquiv.symm_apply_apply] at hh
  exact d.upper_star_g_not_normalizer hB
    (by simpa only [inv_inv] using (normalizer
      (((D.star D.U).subgroupOf (D.star D.L)) : Set (D.star D.L))).inv_mem hh)

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
