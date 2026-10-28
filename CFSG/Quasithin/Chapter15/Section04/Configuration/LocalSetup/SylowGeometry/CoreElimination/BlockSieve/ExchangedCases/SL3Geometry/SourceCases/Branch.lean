module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Alternatives
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.Setup

/-! # The complete SL₃ branch of C.2.7(3)(g)
The star is D/C_D(Ω₁(Z(O₂(D)))), with D=LR. The component and M∩L
are mapped into this quotient before the maximal-parabolic condition is
stated. The MS-pair is intrinsic to D and retains both MS2 alternatives.
Source: C.2.7(1)–(3), printed pp.145–147.
-/

@[expose] public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
universe u

/-- The stabilizer of an actual subspace in the natural special-linear action. -/
def subspaceStabilizer (F : Type) [Field F] (W : Submodule F (Fin 3 → F)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) where
  carrier := {g | ∀ v, v ∈ W ↔ specialLinearNatural 3 g v ∈ W}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro g h hg hh v
    simpa only [map_mul, Module.End.mul_apply] using (hh v).trans (hg (specialLinearNatural 3 h v))
  inv_mem' := by
    intro g hg v
    have he := (hg (specialLinearNatural 3 g⁻¹ v)).symm
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] using he

/-- In SL₃ the maximal parabolics are the line and plane stabilizers. -/
def SL3MaximalParabolic (F : Type) [Field F]
    (P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) : Prop :=
  ∃ W : Submodule F (Fin 3 → F), (Module.finrank F W = 1 ∨ Module.finrank F W = 2) ∧
    P = subspaceStabilizer F W

variable {A : Type u} [Group A]

abbrev localGroup (L R : Subgroup A) := (L ⊔ R : Subgroup A)

/-- The actual kernel in the star convention of C.2.7. -/
noncomputable def starKernel (L R : Subgroup A) : Subgroup (localGroup L R) :=
  centralizer (omegaCoreModule (localGroup L R) : Set (localGroup L R))

instance starKernel_normal (L R : Subgroup A) : (starKernel L R).Normal := by
  unfold starKernel
  infer_instance

abbrev Star (L R : Subgroup A) := localGroup L R ⧸ starKernel L R

noncomputable def starComponent (L R : Subgroup A) : Subgroup (Star L R) :=
  (L.subgroupOf (L ⊔ R)).map (QuotientGroup.mk' (starKernel L R))

noncomputable def starIntersection (L R M : Subgroup A) : Subgroup (Star L R) :=
  ((M ⊓ L).subgroupOf (L ⊔ R)).map (QuotientGroup.mk' (starKernel L R))

/-- The complete (g) branch, without assuming the C.1.34 alternatives. -/
def SL3Branch (κ : GroupClass.{u}) (L R M : Subgroup A) : Prop :=
  MSPair κ (localGroup L R) (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (n : ℕ), 0 < n ∧ Nat.card F = 2 ^ n ∧
      ∃ e : starComponent L R ≃* Matrix.SpecialLinearGroup (Fin 3) F,
        SL3MaximalParabolic F (((starIntersection L R M).subgroupOf
          (starComponent L R)).map e.toMonoidHom)

/-- The maximal-parabolic subgroup really is contained in the starred component. -/
theorem starIntersection_le (L R M : Subgroup A) : starIntersection L R M ≤ starComponent L R :=
  map_mono (fun _ hx => hx.2)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
