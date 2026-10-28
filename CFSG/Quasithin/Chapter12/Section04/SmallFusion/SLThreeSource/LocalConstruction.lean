module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.Assembly
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.LocalConstructionFixedPlane

/-!
# Local geometry from the original chosen L₃ module

The plane, its nonfixed point, its fixed-space equality, its index and the
literal local Sylow witness are constructed from the original marked module.
The remaining supplement identity concerns the larger reduced module of LT,
so it is kept as an independent source input. This theorem does not complete
LocalCalculations until that identity is proved and supplied.

The structural and marked-module implications of 12.2.2 remain universal
earlier inputs. The independent reduced-module calculation must be supplied
before applying the source fusion assembly.
Source: Aschbacher–Smith, 12.4.5–6, printed pp.813–814.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u

/-- The larger reduced-module calculation of 12.4.5(2). The product contains
all of V. This is the sole remaining input to the local geometry constructor. -/
def FixedSupplementCalculation : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G),
    Hypothesis1223 KnownSimple.IsKnownSimple T L → (D : ChosenModule T L V) →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) =
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊔ V

/-- Construct the actual plane and local Sylow witness. Only the independent
12.4.5 supplement calculation and the permitted earlier 12.2 implications remain. -/
theorem localCalculations_of_fixedSupplement
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (supplement : FixedSupplementCalculation.{u}) : LocalCalculations.{u} := by
  intro G _ _ T L V h D hmodel hne
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  have hTL := (structural G T L h).1
  have hTV := ((structural G T L h).2.2 V D).1
  have hMV := ((structural G T L h).2.2 V D).2.2.2.resolve_right hne
  obtain ⟨E, hEV, hEc, hTE⟩ := exists_invariant_plane ext hne hTV
  obtain ⟨v, hvE, hvF, hi, hSyl⟩ :=
    invariant_plane_local_sylow ext hne hTL hMV E hEV hEc hTE
  exact ⟨⟨E, hEV, hEc, v, hvE, hvF, supplement G T L V h D hmodel hne,
    invariant_plane_fixed_space ext hne hTL E hEV hEc hi, hi, hSyl⟩⟩
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
