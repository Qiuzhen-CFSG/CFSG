module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.Triality
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstExceptionalLie

/-!
# First-normalizer refinement for every binary triality carrier

The actual parabolic quotient first matches the independent triality field
with either the original field or its cubic subfield. The existing Cartan
rank argument excludes both strict embeddings, including ³D₄(2). Thus the
first containing component equals the original residual, without an
exhaustive embedding-list premise.

The original quotient, Cartan size and faithfulness premises are preceding
flag facts, produced by qt-d-1222-natural-flag-cartan and discharged by
qt-d-1222-natural-local-geometry. The relative-components owner retains the
remaining carriers, second-normalizer equality, and the field-four triangle.
Source: Aschbacher--Smith 11.1.1--11.1.2, printed pp.761--762,
combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The triality carrier gives equality in the first normalizer, with no
assumption matching its field to the original flag. -/
theorem first_eq_of_triality
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hmodel : Triality.IsQTKETrialityModel (K ⧸ pCore 2 K)) : f.Li 0 = K := by
  by_contra he
  obtain ⟨m,hmpos,hmodel⟩ := (Triality.isQTKETrialityModel_iff_fieldOrder _).mp hmodel
  have hT : (T : Subgroup G) ≤ normalizer (f.Vi 0 : Set G) := f.invariant 0
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G) (normalizer (f.Vi 0 : Set G)) :=
    ⟨T.subtype hT,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hT]⟩
  have hXN : X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤
      normalizer (f.Vi 0 : Set G) := inf_le_left.trans (f.cartan_normalizes hu hX 0)
  rcases relative_triality_parameters hs (flag_mem_local_of_model D S f 0 hm) hK.1
    (lt_of_le_of_ne hLK he) S.field.degree_pos hmpos hm hmodel with hnm | hnm
  · exact first_component_not_triality D S f hm hfix hK hLK hXN hXcard hfaith (hnm.symm ▸ hmodel)
  · exact first_component_not_trialityCube D S f hm hfix hK hLK hXN hXcard hfaith
      (by omega) hnm hmodel

/-- The literal triality-carrier application to the first-index refinement. -/
theorem first_reduction_of_triality
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hmodel : Triality.IsQTKETrialityModel (K ⧸ pCore 2 K)) :
    RefinementReduction L (f.Li 0) (f.Li 1) K X 0 S.field.degree := by
  exact .equal (by simpa using first_eq_of_triality D S f hu hm hfix hX hK hLK hXcard hfaith hmodel)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
