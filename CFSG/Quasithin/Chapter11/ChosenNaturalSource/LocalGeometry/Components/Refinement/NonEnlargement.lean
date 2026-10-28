module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.NonEnlargement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Radical
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.CentralCover

/-!
# Both-index refinement in the non-enlarging carrier families

The Bender, even SU₃ and small alternating quotient models force equality
at either original flag normalizer. At the second index this supplies
actual relative C-component membership. The full-radical action argument
then makes every other component centralize the entire V₂, including
C_V(L), while the natural quotient shows that L₂ does not centralize it.
The field-four consumer also applies the central-kernel argument, without
assuming irreducibility of the full central cover.

The natural maps and radical actions are preceding flag inputs, supplied
by qt-d-1222-natural-flag-cartan and discharged in
qt-d-1222-natural-local-geometry. The relative-components owner retains
the other carriers and the field-four triangle.
Source: Aschbacher--Smith 11.1.1--11.1.3, printed pp.761--765,
combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter12.Section02
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The original refinement at both indices, with the actual carrier premise
discharging the equality branch. -/
theorem refinement_of_nonEnlarging_carrier (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K X : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) (hmodel : NonEnlargingCarrier (K ⧸ pCore 2 K)) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X i S.field.degree := by
  have he := flag_eq_of_nonEnlarging_carrier D S f i hm hK hLK hmodel
  apply RefinementAlternative.equal
  fin_cases i <;> simpa using he

/-- The unrestricted-degree uniqueness consumer keeps the full original plane.
No component-equality or refinement premise remains in these carrier rows. -/
theorem uniqueNoncentral_second_of_nonEnlarging_carrier
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 ≤ K) (hmodel : NonEnlargingCarrier (K ⧸ pCore 2 K))
    (hR : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G))
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v)) :
    Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) := by
  apply uniqueNoncentral_second_of_radical_and_natural_action S f _ hm hR π hπ p hp hact
  rw [flag_eq_of_nonEnlarging_carrier D S f 1 hm hK hLK hmodel]
  exact hK

/-- At field four the original central-kernel action proof supplies actual
uniqueness, retaining the fixed summand in the plane. -/
theorem uniqueNoncentral_second_fieldFour_of_nonEnlarging_carrier
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2)
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 ≤ K) (hmodel : NonEnlargingCarrier (K ⧸ pCore 2 K))
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G))
    (hcore : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G)) :
    Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) := by
  apply uniqueNoncentral_second_fieldFour_of_natural_cover S f hfour _ π hπ p hp hact hk hcore
  rw [flag_eq_of_nonEnlarging_carrier D S f 1 hm hK hLK hmodel]
  exact hK

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
