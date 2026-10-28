module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Flag
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Quotients
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Natural

/-!
# The marked SL₃ flag and its original quotient maps

The actual Sylow intersection supplies the unique field flag, and its
intrinsic fixed-space characterization proves invariance under the whole
ambient Sylow. The original normalizer residuals have PSL₂ two-core
quotients. Vanishing of the original central kernel identifies V itself
with the natural three-space; no complement to a central kernel is assumed.
Inner uniqueness discharges the independent source Cartan normalization
premise. Plane actions, local generation and radical identities are separate
local calculations, not conclusions asserted by this partial assembly.

Source: Aschbacher--Smith, 11.0.3(3), the opening of §11.1 and the Cartan
normalization preceding 11.1.2, printed pp.760--761.
-/

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Simultaneous flag, literal local quotients and flag-normalizing source Cartan. -/
theorem exists_flag_and_cartan (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    ∃ f : InvariantFlag (.sl3 m), f.IsUnique ∧ f.IsInnerUnique ∧ f.Vi 2 = V ∧
      (∀ i : Fin 2, Nonempty ((f.Li i ⧸ pCore 2 (f.Li i)) ≃*
        PSL(2,S.field.Carrier))) ∧
      ∃ X : Subgroup G, IsCartan T L X ∧ ∀ i, X ≤ normalizer (f.Vi i : Set G) := by
  refine ⟨flag D S m, flag_unique D S m, flag_inner_unique D S m, flag_top D S m,
    fun i => ⟨flagLocalCoreEquiv S m (flag D S m) i⟩, ?_⟩
  exact (flag D S m).exists_normalizing_cartan (flag_inner_unique D S m)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3
