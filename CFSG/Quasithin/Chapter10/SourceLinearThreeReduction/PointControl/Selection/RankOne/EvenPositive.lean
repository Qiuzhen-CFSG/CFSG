module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.Direct
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.EvenReduction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Remaining
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.RankOneExclusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.ScalarNaturals

/-!
# The remaining rank-one fixed-layer contract

The direct Baumann argument controls the Sylow centralizer of each original
opposite point, including component-fixed points. The quasisimple and
constrained containing-component exclusions then prove point-centralizer
containment for this same full module, using the supplied half-Sylow uniqueness.
The independent generation bound constructs an actual minimum offender of
corank at most two. The rank-one small-offender theorem excludes its original
natural section, with the full moved kernel and normalizer action retained.

Consequently the even positive-kernel configuration in EvenPositiveFixedLayerAt
cannot occur. This proves that separate contract, as well as the old whole
fixed-layer and point-geometry interfaces. No claim that natural coordinates
alone fix the central kernel is needed. The argument first establishes point
control by Direct, which has no fixed-layer premise; it then follows source
10.2.3, 10.2.9 and 10.2.12 before taking the fixed-layer corollary. The imported
source proofs do not depend on this corollary or on ModuleChoice.Source.

Source: Aschbacher--Smith, 10.2.3, 10.2.9 and 10.2.12, printed pp.745--747,
750--755. ModuleChoice.Source applies the result to the original selection
consumer, retaining the independently owned stabilizer-normalizer input.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Direct rank-one point control and both containing-component exclusions
control every nonidentity original moved point, including its fixed kernel. -/
theorem element_centralizers_of_halfSylowUnique
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodel : RankOneNatural D) (hhalf : HalfSylowUnique D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hpoint := pointSylowControl_direct D hna hmodel ht htn hcross
  apply source_a5_moved_point_control_of_partner_saturated D hn ht htn
  intro v hv hvne hsM
  by_contra hout
  obtain ⟨I,c⟩ := escapingComponent_of_local_sylow D ht htn hcross hhalf hpoint
    hv hvne hsM hout
  by_cases hI : IsQuasisimple I
  · let := hI
    exact Quasisimple.quasisimple_impossible D c hna
  · have hvV := partner_le_fullModule D ht hv
    have hCW := (Subgroup.centralizer_le_normalizer _).trans c.moved_normalizer
    let ctx : Constrained.Context D t v I := ⟨hmany,hmin,hna,c,hI,
      source_a5_point_component_characteristicTwo D hvV hvne (hcross hv) hCW I
        c.le_centralizer c.component hI,
      source_a5_point_component_reduced_module D hvV hvne (hcross hv) hCW I c.strict.le
        c.le_centralizer c.component c.normalizes hI c.sylow⟩
    exact ctx.no_rankOneNatural hmodel

/-- The same original rank-one section is incompatible with the attained
small offender supplied by the independent generation theorem. -/
theorem no_rankOneNatural_of_halfSylowUnique
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hhalf : HalfSylowUnique D) : ¬ RankOneNatural D := by
  intro hmodel
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hn
  have hcross : ∀ s ∈ (T : Subgroup G), s ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj s).toMonoidHom ≤ centralizer (L : Set G) :=
    fun _ hs hsn => SmallOffender.Recognition.rank_one_crossed_of_marking D hmodel hs hsn
  have hcent := element_centralizers_of_halfSylowUnique D hmany hmin hna hmodel
    hhalf ht htn (hcross t ht htn)
  have hbound := source_nonnormalGenerationBound hmany L D hn hna
  have hw := source_fullModule_globalW_le_two_of_generation_bound D hmany hcent hbound
  obtain ⟨g,hg,hcomm,hwg,hsmall⟩ := source_fullModule_small_offender D hw
  let c : SmallOffender.Configuration T D g :=
    ⟨hmany,hmin,hn,hna,hcent,hg,hcomm,hwg,hsmall⟩
  exact SmallOffender.Recognition.no_rank_one_natural_of_small_offender D c hmodel hcross
    (component_normalizer_le_of_halfSylowUnique D hn hhalf)

omit D in
/-- The distinct even-degree positive-fixed-kernel obligation is discharged
with its original HalfSylowUnique premise and both literal moved kernels. -/
theorem evenPositiveFixedLayerAt : EvenPositiveFixedLayerAt (G := G) T := by
  intro hmany L D hmin _hfull hna n hn _he e c _hpositive _hJ t ht htn _hcross hhalf
  exact (no_rankOneNatural_of_halfSylowUnique D hmany hmin
    (fun h => htn (h ht)) hna hhalf ⟨n,by omega,e,⟨c⟩⟩).elim

omit D in
/-- Both original fixed kernels, and therefore the whole fixed layer, are
centralized under the original fixed-layer contract in every field degree. -/
theorem fixedLayerAt : FixedLayerAt (G := G) T :=
  fixedLayerAt_of_even_positive evenPositiveFixedLayerAt

omit D in
/-- All three rank-one point-geometry clauses now follow from the original
source hypotheses, retaining the supplied half-Sylow uniqueness. -/
theorem rankOneGeometryAt : RankOneGeometryAt (G := G) T :=
  rankOneGeometryAt_of_even_positive evenPositiveFixedLayerAt

end CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
