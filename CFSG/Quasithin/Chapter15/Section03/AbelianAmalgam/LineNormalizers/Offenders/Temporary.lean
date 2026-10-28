module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Definitions
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Elementary inheritance under the temporary normalizer

The two-core of `N_{G_E}(C_T(V_E/E))` is defined separately from the original
`Q_E`. The quotient centralizer is a normal two-subgroup of this new group,
so lies in its core. The original abelian span remains normal and lies in
that core. The original `I₀ = I ∩ N_{G_E}(C_T(V_E/E))` remains normal as well.

These are the immediate inheritance steps in the temporary replacement.
The reverse core containment, preservation of the marked action and Sylow
structure, and comparison with the Thompson subgroup of the smaller
centralizer still require proof. No such comparison is built into the definitions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of 15.3.67,
printed p.1153, PDF p.1170.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders
variable {G : Type*} [Group G]

/-- The two-core of the temporary normalizer, kept separate from `lineQ E`. -/
noncomputable def temporaryCore (T V E : Subgroup G) : Subgroup G :=
  Stellmacher.twoCoreAmbient (temporaryLineNormalizer T V E)

/-- The centralizer inside the temporary group; this does not redefine the original `I`. -/
def temporaryCentralizer (T V E : Subgroup G) : Subgroup G :=
  temporaryLineNormalizer T V E ⊓ centralizer (E : Set G)

/-- The temporary core is a subgroup of the temporary normalizer. -/
theorem temporaryCore_le (T V E : Subgroup G) :
    temporaryCore T V E ≤ temporaryLineNormalizer T V E := map_subtype_le _

/-- Normality of the temporary core is relative to the temporary group. -/
theorem temporaryCore_normal (T V E : Subgroup G) :
    ((temporaryCore T V E).subgroupOf (temporaryLineNormalizer T V E)).Normal := by
  change (((pCore 2 (temporaryLineNormalizer T V E)).map
    (temporaryLineNormalizer T V E).subtype).comap (temporaryLineNormalizer T V E).subtype).Normal
  rw [comap_map_eq_self_of_injective (temporaryLineNormalizer T V E).subtype_injective]
  infer_instance

/-- The temporary core is a two-group. -/
theorem temporaryCore_isPGroup (T V E : Subgroup G) :
    IsPGroup 2 (temporaryCore T V E) :=
  pCore_isPGroup.map (temporaryLineNormalizer T V E).subtype

/-- The quotient centralizer lies in its relative normalizer. -/
theorem quotientCentralizer_le_temporary (T V E : Subgroup G) :
    lineQuotientCentralizer T V E ≤ temporaryLineNormalizer T V E :=
  le_inf ((lineQuotientCentralizer_le_lineT T V E).trans inf_le_right)
    (lineQuotientCentralizer T V E).le_normalizer

/-- The group being normalized is normal in the temporary group. -/
theorem quotientCentralizer_normal_in_temporary (T V E : Subgroup G) :
    ((lineQuotientCentralizer T V E).subgroupOf (temporaryLineNormalizer T V E)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (quotientCentralizer_le_temporary T V E)).mpr inf_le_right

/-- Thus `C_T(V_E/E)` is contained in the temporary core. The reverse inclusion is separate. -/
theorem quotientCentralizer_le_temporaryCore (T V E : Subgroup G) (hT : IsPGroup 2 T) :
    lineQuotientCentralizer T V E ≤ temporaryCore T V E :=
  le_pCoreIn_of_normalizes
    (hT.to_le ((lineQuotientCentralizer_le_lineT T V E).trans inf_le_left))
    (quotientCentralizer_le_temporary T V E) inf_le_right

/-- The source `D = C_A(V_E)` lies in `C_T(V_E/E)` whenever `A ≤ T_E`.
This requires no containment of the entire centralizer in a two-core. -/
theorem centralizer_intersection_le_quotientCentralizer (T V E A : Subgroup G)
    (hU : lineV V E ≤ lineNormalizer E) (hA : A ≤ lineT T E) :
    A ⊓ centralizer (lineV V E : Set G) ≤ lineQuotientCentralizer T V E := by
  intro x hx
  apply (mem_lineQuotientCentralizer_iff T V E hU x).mpr
  refine ⟨hA hx.1, fun v hv => ?_⟩
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 v hv)]
  exact E.one_mem

/-- An abelian line span in `T_E` centralizes its own quotient. -/
theorem lineV_le_quotientCentralizer (T V E : Subgroup G)
    [IsMulCommutative (lineV V E)] (hUT : lineV V E ≤ lineT T E) :
    lineV V E ≤ lineQuotientCentralizer T V E := by
  intro x hx
  apply (mem_lineQuotientCentralizer_iff T V E (hUT.trans inf_le_right) x).mpr
  refine ⟨hUT hx, fun v hv => ?_⟩
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (setLike_mul_comm hv hx)]
  exact E.one_mem

/-- The original line span remains in the temporary two-core. -/
theorem lineV_le_temporaryCore (T V E : Subgroup G)
    [IsMulCommutative (lineV V E)] (hUT : lineV V E ≤ lineT T E) (hT : IsPGroup 2 T) :
    lineV V E ≤ temporaryCore T V E :=
  (lineV_le_quotientCentralizer T V E hUT).trans (quotientCentralizer_le_temporaryCore T V E hT)

/-- The original conjugate span remains relatively normal after replacement. -/
theorem lineV_normal_in_temporary (T V E : Subgroup G)
    [IsMulCommutative (lineV V E)] (hUT : lineV V E ≤ lineT T E) :
    ((lineV V E).subgroupOf (temporaryLineNormalizer T V E)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    ((lineV_le_quotientCentralizer T V E hUT).trans (quotientCentralizer_le_temporary T V E))).mpr
  exact inf_le_left.trans (le_normalizer_conjugateSpanBy V (lineNormalizer E))

/-- The original `I₀` lies in the temporary centralizer. -/
theorem lineI0_le_temporaryCentralizer (T V E : Subgroup G) :
    lineI0 T V E ≤ temporaryCentralizer T V E := by
  rw [lineI0_eq_inf_temporary]
  exact le_inf inf_le_right (inf_le_left.trans (lineI_le_centralizer E))

/-- Intersecting the original normal `I` with the temporary group preserves normality. -/
theorem lineI0_normal_in_temporary (T V E : Subgroup G) :
    ((lineI0 T V E).subgroupOf (temporaryLineNormalizer T V E)).Normal := by
  have hI := (normal_subgroupOf_iff_le_normalizer (lineI_le_lineNormalizer E)).mp
    (lineI_normal_in_lineNormalizer E)
  have hN : temporaryLineNormalizer T V E ≤
      normalizer (lineI E ⊓ temporaryLineNormalizer T V E : Set G) :=
    (le_inf (inf_le_left.trans hI) (temporaryLineNormalizer T V E).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  apply (normal_subgroupOf_iff_le_normalizer
    ((lineI0_le_temporaryCentralizer T V E).trans inf_le_left)).mpr
  rw [lineI0_eq_inf_temporary]
  exact hN

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders
