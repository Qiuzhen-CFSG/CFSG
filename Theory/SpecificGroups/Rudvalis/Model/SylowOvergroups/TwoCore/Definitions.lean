module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.CoverageReduction

/-!
# Local groups for a Rudvalis two-core calculation

For a Sylow two-subgroup S of the concrete ATLAS subgroup max4, let P be
its image in Ru. Let U be the ambient image of O₂(max4), and let V be the
ambient image of Z(P). Both are subgroups of P normalized by P.

The missing generation calculation asks that adjoining to P an element
outside N(U) and N(V) gives the whole concrete group. Combined with
O₂(max4) ≠ 1, this implies nontrivial intrinsic two-cores in every proper
odd-index subgroup. The generation statement is an explicit obligation;
this module neither supplies it nor asserts exhaustive maximal coverage.

Source application: Aschbacher--Smith, proof of Proposition 1.3.4, printed
p.511 (PDF p.528), citing [Asc86b]. The subgroup max4 is the actual ATLAS
word subgroup from SylowOvergroups.Definitions, not a group-family label.
-/

namespace Rudvalis.SylowOvergroups.TwoCore

open Subgroup

/-- The ambient image of a Sylow two-subgroup of max4. -/
@[expose] public def sylowImage (S : Sylow 2 max4) : Subgroup Model :=
  (S : Subgroup max4).map max4.subtype

/-- The intrinsic two-core of max4, transported into the ambient model. -/
@[expose] public def coreImage : Subgroup Model :=
  (pCore 2 max4).map max4.subtype

/-- The center of the chosen two-subgroup, transported into the model. -/
@[expose] public def centerImage (S : Sylow 2 max4) : Subgroup Model :=
  (center (sylowImage S)).map (sylowImage S).subtype

public theorem sylowImage_isPGroup (S : Sylow 2 max4) :
    IsPGroup 2 (sylowImage S) :=
  S.isPGroup'.map max4.subtype

public theorem coreImage_le (S : Sylow 2 max4) : coreImage ≤ sylowImage S :=
  map_mono (pCore_isPGroup.le_sylow_of_normal S)

public theorem centerImage_le (S : Sylow 2 max4) : centerImage S ≤ sylowImage S :=
  map_subtype_le _

/-- The normalization here is relative to P, not normality in Ru. -/
public theorem sylowImage_le_normalizer_coreImage (S : Sylow 2 max4) :
    sylowImage S ≤ normalizer (coreImage : Set Model) := by
  have hm : max4 ≤ normalizer (coreImage : Set Model) := by
    simpa only [coreImage, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 max4).le_normalizer_map max4.subtype
  exact (map_subtype_le _).trans hm

public theorem sylowImage_le_normalizer_centerImage (S : Sylow 2 max4) :
    sylowImage S ≤ normalizer (centerImage S : Set Model) := by
  simpa only [centerImage, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    (center (sylowImage S)).le_normalizer_map (sylowImage S).subtype

/-- A concrete one-element generation obligation. A proof may choose the
Sylow subgroup most convenient for its word or double-coset certificates. -/
@[expose] public def GeneratorRecovery : Prop :=
  ∃ S : Sylow 2 max4, ∀ g : Model,
    g ∉ normalizer (coreImage : Set Model) →
    g ∉ normalizer (centerImage S : Set Model) →
    closure (insert g (sylowImage S : Set Model)) = ⊤

end Rudvalis.SylowOvergroups.TwoCore
