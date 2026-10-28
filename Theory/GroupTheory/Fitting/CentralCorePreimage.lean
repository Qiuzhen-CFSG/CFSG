module
public import Theory.GroupTheory.Fitting.TwoCoreMonotonicity
public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# Central core preimages in the ambient Fitting preimage

For a normal subgroup X, the preimage of Z(X/O₂(X)) lies in the preimage
of F(X/O₂(X)). Normal-inclusion functoriality then puts its embedded image
in the preimage of F(G/O₂(G)). All maps are the original quotient maps
and subgroup inclusions.

Source: standard Fitting functoriality, applied to the C.2.6 containment
in Aschbacher--Smith 15.2.23, printed pp.145,1116.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A normal subgroup's central core preimage lies in the ambient Fitting preimage. -/
theorem centralPreimage_twoCore_map_le_twoFittingCore (X : Subgroup G) [X.Normal] :
    (centralPreimage (pCore 2 X)).map X.subtype ≤ twoFittingCore G := by
  have hz : center (X ⧸ pCore 2 X) ≤ fittingSubgroup (X ⧸ pCore 2 X) := by
    let : CommGroup (center (X ⧸ pCore 2 X)) := IsMulCommutative.instCommGroup
    exact le_sSup ⟨inferInstance, inferInstance⟩
  exact (map_mono (comap_mono hz)).trans (twoFittingCore_map_subtype_le_of_normal X)
end Theory.GroupTheory

