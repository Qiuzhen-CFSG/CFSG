module

public import Theory.GroupTheory.Fitting.Core
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The Fitting subgroup inside an ambient group

`fittingSubgroupOf H` is the image of the actual Fitting subgroup of `H`
under its inclusion in the ambient group. If `H` is normal, this image is
normal because the Fitting subgroup is characteristic. For finite ambient
groups the image is nilpotent, by transport along the injective inclusion.

These declarations are extracted unchanged from
`FeitThompson/ChiefFactors/Core.lean` and `Proposition12.lean`. They supply the
subgroup step in solvable Fitting self-centralization without importing the
chief-factor development. The exposed image definition preserves the existing
definitional interface and historical global names.
-/

/-- The Fitting subgroup of a subgroup `H`, viewed as a subgroup of the ambient group `G`.
This is the image of `fittingSubgroup H` under the inclusion `H ↪ G`. -/
@[expose]
public def fittingSubgroupOf {G : Type*} [Group G] (H : Subgroup G) : Subgroup G :=
  (fittingSubgroup (↥H)).map H.subtype

variable {G : Type*} [Group G]

/-- The Fitting subgroup of a normal subgroup `H` is normal in the ambient group. -/
public theorem fittingSubgroupOf_normal (H : Subgroup G) (hH : H.Normal) :
    (fittingSubgroupOf (G := G) H).Normal := by
  classical
  -- `fittingSubgroup (↥H)` is characteristic in `H`, hence its image in `G` is normal.
  let K : Subgroup (↥H) := fittingSubgroup (↥H)
  have hK_char : K.Characteristic :=
    (show (fittingSubgroup (↥H)).Characteristic from inferInstance)
  have hKmap_normal : (K.map H.subtype).Normal :=
    @ConjAct.normal_of_characteristic_of_normal G (inferInstance : Group G) H hH K hK_char
  simpa [fittingSubgroupOf, K] using hKmap_normal

variable [Finite G]

/-- The Fitting subgroup of a subgroup `H` is nilpotent. -/
public lemma fittingSubgroupOf_isNilpotent (H : Subgroup G) :
    Group.IsNilpotent (fittingSubgroupOf (G := G) H) := by
  classical
  have : Group.IsNilpotent (fittingSubgroup (↥H)) := by infer_instance
  change Group.IsNilpotent ((fittingSubgroup (↥H)).map H.subtype)
  let e : fittingSubgroup (↥H) ≃* (fittingSubgroup (↥H)).map H.subtype :=
    Subgroup.equivMapOfInjective (f := H.subtype) (fittingSubgroup (↥H)) H.subtype_injective
  exact Group.nilpotent_of_mulEquiv e

