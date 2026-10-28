module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.Generation
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.PlaneCover

/-!
# The actual marked symplectic flag and its two residuals

For the precise defining field in the nonbinary source input, the marked
natural module has a unique invariant flag. Uniqueness already holds under
the inner Sylow T intersect L, so the original Cartan normalizes the flag.
The two literal normalizer residuals generate L and their literal two-core
quotients are PSL2 over this same field.

Plane-orbit geometry and the original nonsplit plane action are separate
obligations; this endpoint does not assert source 11.1.3 or 11.1.4.

Source: Aschbacher--Smith, 11.0.2 and opening section 11.1, pp.759--761.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

/-- Both uniqueness assertions for the original nonbinary source field. -/
theorem source_flag_unique : (flag m S).IsUnique ∧ (flag m S).IsInnerUnique :=
  ⟨flag_unique m S, flag_inner_unique m S⟩

/-- The original residual quotient, with the source's nonbinary premise discharged. -/
def source_Li_quotientEquiv (i : Fin 2) :
    ((flag m S).Li i ⧸ pCore 2 ((flag m S).Li i)) ≃* PSL(2,S.field.Carrier) :=
  flag_Li_quotientEquiv m S S.nonbinary i

/-- Generation uses the original ambient residuals, rather than their model tags. -/
theorem source_Li_sup : L = (flag m S).Li 0 ⊔ (flag m S).Li 1 :=
  (flag_Li_sup m S S.nonbinary).symm

/-- The flag simultaneously admits the original source Cartan and its local quotients. -/
theorem exists_flag_and_cartan :
    ∃ (f : InvariantFlag (Coordinates.sp4 m)) (X : Subgroup G),
      f.IsUnique ∧ f.IsInnerUnique ∧ IsCartan T L X ∧
      (∀ i, X ≤ normalizer (f.Vi i : Set G)) ∧
      (∀ i, Nonempty ((f.Li i ⧸ pCore 2 (f.Li i)) ≃* PSL(2,S.field.Carrier))) ∧
      L = f.Li 0 ⊔ f.Li 1 := by
  obtain ⟨X,hX,hXF⟩ := exists_normalizing_cartan m S
  exact ⟨flag m S, X, flag_unique m S, flag_inner_unique m S, hX, hXF,
    fun i => ⟨source_Li_quotientEquiv S m i⟩, source_Li_sup S m⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4
