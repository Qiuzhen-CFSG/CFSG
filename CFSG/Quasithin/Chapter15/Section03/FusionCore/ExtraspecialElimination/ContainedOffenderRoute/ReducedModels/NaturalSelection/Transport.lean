module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.NaturalSelection.Models

/-!
# Natural coordinates and offenders on the classified moved section

Restriction to an overgroup preserves the actual component commutator.
The identity on its vectors identifies its central quotient with the source
section; natural coordinates therefore return to the original ambient action.
Fixed codimension decreases on this section. In a ratio-one branch every
original best offender remains best, so offender generation passes as well.

Source: Aschbacher–Smith, B.1.5(8), B.5.1(1), pp.69–70 and 99, and the proof
of 15.3.49, printed p.1144 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open Representation.SL2CubicFixedSection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.NaturalSelection
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {J P : Subgroup D}

/-- Restriction to an overgroup retains the literal component moved space. -/
theorem moved_subgroupOf (hJP : J ≤ P) :
    moved (ρ.comp P.subtype) (J.subgroupOf P) = moved ρ J := by
  unfold moved subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    exact ⟨x.val, hx, w, hw, rfl⟩
  · rintro ⟨x, hx, w, hw, rfl⟩
    exact ⟨⟨x, hJP hx⟩, hx, w, hw, rfl⟩

/-- Lift the natural coordinates from the restricted actor, using the
identity on the actual moved space and its fixed-space quotient. -/
noncomputable def section_of_restriction
    {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
    (hJP : J ≤ P) (s : MovedSection (ρ.comp P.subtype) (J.subgroupOf P))
    (U : Submodule (ZMod 2) W) (hU : U = moved ρ J)
    (b : ActionEquiv (s.action.comp (J.subgroupOf P).subtype)
      (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 2))) :
    NaturalComponentSection (F := F) ρ J U := by
  let E := LinearEquiv.ofEq U s.space.toSubmodule
    (hU.trans ((moved_subgroupOf hJP).symm.trans s.space_eq.symm))
  let j : J ≃* J.subgroupOf P := (subgroupOfEquivOfLe hJP).symm
  have hmap : Submodule.map (E : U →ₗ[ZMod 2] s.space.toSubmodule)
      ((fixedSpace ρ J).comap U.subtype) = s.central.toSubmodule := by
    rw [s.central_eq]
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩ x
      exact Subtype.ext (hw ⟨x.val.val, x.property⟩)
    · intro hv
      refine ⟨E.symm v, ?_, E.apply_symm_apply v⟩
      intro x
      exact congrArg Subtype.val (hv (j x))
  let q := Submodule.Quotient.equiv _ _ E hmap
  have hinv (x : J) (v : U) : ρ x v ∈ U := by
    have h := s.space.apply_mem_toSubmodule (j x).val (E v).property
    have he : U = s.space.toSubmodule :=
      hU.trans ((moved_subgroupOf hJP).symm.trans s.space_eq.symm)
    exact he.symm ▸ h
  refine { model := j.trans b.groupEquiv
           invariant := hinv
           coordinates := q.trans b.linearEquiv
           equivariant := ?_ }
  intro x v
  exact b.intertwines (j x) (q (Submodule.Quotient.mk v))

/-- Fixed codimension cannot increase on the classified central quotient. -/
theorem movedSection_codim_le [FiniteDimensional (ZMod 2) W]
    (s : MovedSection ρ J) (A : Subgroup D) :
    fixedCodim s.action A ≤ fixedCodim ρ A := by
  have h₁ := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A
  have h₂ := fixedCodim_subrepresentation_le ρ s.space A
  exact (Nat.le_add_right _ _).trans (h₁.trans h₂)

/-- In the ratio-one row the same best offender survives on the section. -/
theorem best_on_movedSection [Finite D] [FiniteDimensional (ZMod 2) W]
    (s : MovedSection ρ J) (hq : quadraticRatio s.action = 1)
    {A : Subgroup D} (hA : IsBestOffender ρ A) : IsBestOffender s.action A := by
  have ho := hA.isOffender ρ
  have hs : IsOffender s.action A := ⟨ho.1, (movedSection_codim_le s A).trans ho.2⟩
  exact (hs.best_and_codim_eq_of_quadraticRatio_eq_one s.action hq).1

/-- Generation by all original offenders passes to the ratio-one section. -/
theorem movedSection_generated [Finite D] [FiniteDimensional (ZMod 2) W]
    (s : MovedSection ρ J) (hq : quadraticRatio s.action = 1)
    (hgen : offenderSubgroup ρ = ⊤) : offenderSubgroup s.action = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply iSup_le
  intro A
  apply iSup_le
  rintro ⟨hA, _⟩
  exact le_iSup_of_le A (le_iSup_of_le ⟨best_on_movedSection s hq hA, le_top⟩ le_rfl)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.NaturalSelection
