module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.FixedResidualSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverInvolutions.FusionModels
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.OrbitConstruction.CoordinateFusion
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws

/-!
# Involution fusion in the actual marked four-cover

Changing only field coefficients preserves the original highest-root plane
in the projective marking. The four-cover root theorem therefore conjugates
every component involution into the original natural four-space. Its two
coordinate orbits fuse it either to the selected central-plane representative
or to a chosen nonidentity Sylow-fixed vector.

This discharges the inside-component fusion premise in the field transfer
step of Aschbacher–Smith 15.3.38, printed pp.1136–1137. The original component,
covering map, planes, Sylow subgroup and representative remain unchanged.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open FusionCore

open Matrix.PSL3Even.UnipotentGeometry
open scoped MatrixGroups

private theorem fieldEquiv_projective_root {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K) (t : F) :
    Atlas.fieldEquivPSL 3 e (projective F ⟨0, 0, t⟩) =
      projective K ⟨0, 0, e t⟩ := by
  change Atlas.fieldEquivPSL 3 e (QuotientGroup.mk' _ (specialLinear F ⟨0, 0, t⟩)) =
    QuotientGroup.mk' _ (specialLinear K ⟨0, 0, e t⟩)
  rw [Atlas.fieldEquivPSL_mk]
  congr 1
  ext i j
  change e (matrix F ⟨0, 0, t⟩ i j) = matrix K ⟨0, 0, e t⟩ i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

open LocalCover LocalCover.SourceBorel
variable {G : Type*} [Group G] [Finite G]
variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}

/-- The original highest-root plane is still the root plane after changing only
field coefficients in the supplied projective marking. -/
private theorem root_in_fourCover (h : Setup d I L) (r : LocalResult d I L)
    (f : r.marking.F ≃+* Matrix.PSL3Four.F) :
    ∃ g : Matrix.PSL3Four.PSL,
      (projectiveCenter Matrix.PSL3Four.F).map (MulAut.conj g).toMonoidHom ≤
        (r.cover.borel.W₂.subgroupOf L).map
          (r.fourCover h (Atlas.fieldEquivPSL 3 f)).toMonoidHom := by
  let e := Atlas.fieldEquivPSL 3 f
  obtain ⟨g, hg⟩ := r.cover.borel.root
  refine ⟨e g, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨t, rfl⟩ := (mem_projectiveCenter _ y).mp hy
  obtain ⟨a, rfl⟩ := f.surjective t
  have hm : projective r.marking.F ⟨0, 0, a⟩ ∈ projectiveCenter r.marking.F :=
    (mem_projectiveCenter _ _).mpr ⟨a, rfl⟩
  obtain ⟨l, hl, he⟩ := hg (mem_map_of_mem (MulAut.conj g).toMonoidHom hm)
  refine ⟨l, hl, ?_⟩
  rw [LocalResult.fourCover_apply, he]
  change e (g * projective r.marking.F ⟨0, 0, a⟩ * g⁻¹) =
    e g * projective Matrix.PSL3Four.F ⟨0, 0, f a⟩ * (e g)⁻¹
  rw [map_mul, map_mul, map_inv, fieldEquiv_projective_root]

/-- The actual marked component's involutions fuse to the given central-plane
representative or a nonidentity vector fixed by the original Sylow subgroup. -/
theorem Reduction.involution_fusion (r : Reduction d I L) (h : Setup d I L)
    (z : G) (hz : z ∈ d.Z) (hz1 : z ≠ 1)
    (x : G) (hxL : x ∈ L) (hx : orderOf x = 2) :
    IsConj x r.representative.v ∨ IsConj x z := by
  let r₀ := r.coverData
  let : Fintype r₀.marking.F := Fintype.ofFinite _
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let f : r₀.marking.F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      r₀.marking.card, Matrix.PSL3Four.card_F])
  let c := r₀.fourCover h (Atlas.fieldEquivPSL 3 f)
  obtain ⟨g, hg⟩ := root_in_fourCover h r₀ f
  have hplanes : r₀.cover.borel.W₁ ⊔ r₀.cover.borel.W₂ ≤ d.V := by
    rcases r₀.cover.borel.planes with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂]
      exact sup_le (d.action.plane_le _) (d.action.plane_le _)
    · rw [h₁, h₂]
      exact sup_le (d.action.plane_le _) (d.action.plane_le _)
  apply cover_involution_fusion L d.V r₀.cover.borel.W₁ r₀.cover.borel.W₂ c
    hplanes r₀.cover.center_plane g hg r.representative.v z ?_ x hxL hx
  intro y hy hyo
  obtain ⟨i, hi⟩ := r₀.plane
  have hv : r.representative.v ∈ d.action.plane i := by
    rw [← hi]
    exact (r.representative.generator ▸ mem_zpowers r.representative.v).2
  have hzfixed : z ∈ fixedPlane d.V d.T := by
    rw [← NaturalOrthogonalAction.centralInvolutions_eq_fixedPlane d.T d.sylow_le d.action]
    exact hz
  exact coordinate_involution_fusion d.action d.T d.sylow_le i r.representative.v z hv
    r.representative.ne_one hzfixed hz1 y hy (by intro h; simp [h] at hyo)


end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
