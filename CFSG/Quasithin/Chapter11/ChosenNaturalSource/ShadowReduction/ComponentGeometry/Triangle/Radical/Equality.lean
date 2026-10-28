module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Flag
public import Theory.GroupTheory.SolvableRadical

/-!
# The equal-component branch of 11.4.1(3)

When the containing component is the first flag residual itself, the
first radical is literally the two-core of KT. It is normal and nilpotent,
hence lies in the solvable radical. The preceding Cartan normalization of
R₁ puts its commutator with X in that same two-core.

The application retains the original chosen module and field flag. The
normalization premise is the earlier source fact X ≤ N_G(R₁), not either
of the bounds being proved.
Source: Aschbacher--Smith, 11.4.1(3), printed pp.775--776.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The equality branch needs no automorphism-group recognition. -/
theorem equality_bounds (E : Closure.Geometry D) (K : Subgroup G)
    (he : E.L₁ = K) (hX : E.X ≤ normalizer (E.R₁ : Set G)) :
    E.R₁ ≤ (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
        (K ⊔ (T : Subgroup G)).subtype ∧
      ⁅E.R₁, E.X⁆ ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hR : E.R₁ = (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
    change (E.L₁ ⊔ (T : Subgroup G)).pCoreIn 2 = _
    rw [he]
  refine ⟨?_, (le_normalizer_iff_commutator_le_left.mp hX).trans_eq hR⟩
  rw [hR]
  apply map_mono
  let : Group.IsNilpotent (pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) :=
    pCore_isPGroup.isNilpotent
  exact le_solvableRadical _ inferInstance inferInstance

/-- Application to the literal source flag, with L₁ = N_L(V₁)^∞. -/
theorem ofFlag_equality_bounds (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (he : f.Li 0 = K) (hX : X ≤ normalizer (f.Ri 0 : Set G)) :
    (ofFlag S f X z H).R₁ ≤
        (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
          (K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z H).R₁, X⁆ ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 :=
  equality_bounds (ofFlag S f X z H) K he hX

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
