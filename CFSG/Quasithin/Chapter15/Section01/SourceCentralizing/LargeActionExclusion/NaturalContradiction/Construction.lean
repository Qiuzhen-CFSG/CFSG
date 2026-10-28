module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.Flag
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.LocalGeometry.Sylow
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.LocalGeometry.Geometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.LocalGeometry.EndResidual
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.LocalGeometry.EndOrbit
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.RankTwo
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.Nonblock
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.SourceApplication

/-!
# Shared construction of the natural parabolic triple

The common natural flag constructs the actual preimages of the first end
node, its neighbor, and the other end node in LS. Its point and plane markings
identify the source's selected end node. The first core, adjacent supplement,
and adjacent/remote Sylow distinction are proved on that triple, together
with perfection and the literal generation product. The actual end-node
residual is identified with the global centralizer residual and is normalized
by T. Covers and solvability identify the end-node orbit in its Sylow
extension, completing the geometry and T-normalization of Y₂ and Q₂.
The actual rank-two quotient, index-seven parabolic, relative C-component,
and characteristic-two structure are proved on the same flag. The full
omega-center is the exchanged pair of marked lines, giving the required
centralizer-core identity. The two distinct moved layers exclude a linear
block, completing every local construction premise. The final contradiction
retains only the independent C.1.34 classification.

Source: Aschbacher--Smith, 15.1.29, printed pp.1103--1104.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.Section05To06
open CFSG.Quasithin.Chapter15.Section03
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The first source construction, before the Thompson placement and rank-two
arguments. Every conclusion concerns one actual preimage triple. -/
theorem exists_marked_natural_parabolics {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) :
    ∃ a : NaturalFlag d t,
      (a.parabolics.P0 ≤ d.L ⊔ d.S ∧ a.parabolics.P2 ≤ d.L ⊔ d.S ∧
        a.parabolics.P3 ≤ d.L ⊔ d.S) ∧
      (d.S ≤ a.parabolics.P0 ∧ d.S ≤ a.parabolics.P2 ∧ d.S ≤ a.parabolics.P3) ∧
      a.parabolics.P2 = a.parabolics.Y2 ⊔ d.S ∧
      a.parabolics.P0 ≤ normalizer (d.nineMovingPlane : Set G) ∧
      ¬ a.parabolics.P0 ≤ d.ML ⊔ d.S := by
  obtain ⟨a⟩ := exists_naturalFlag hG hM hu h hs t ht htS hnat
  exact ⟨a,a.parabolics_le,a.sylow_le,a.second_supplement hs.1,
    a.first_normalizes_movingPlane hG hM hu h hs ht htS hnat,
    a.first_not_le_markedParabolic hnat⟩

/-- The source placement and movement are established on the same marked
triple. This does not yet assert the end-node orbit or the rank-two input. -/
theorem exists_placed_natural_parabolics {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) :
    ∃ a : NaturalFlag d t,
      a.parabolics.P0 ≤ M ∧
      a.parabolics.P0.pCoreIn 2 = d.S ⊓ centralizer (d.nineMovingPlane : Set G) ∧
      ⁅d.nineMovingPlane,a.parabolics.Y0⁆ = d.nineMovingPlane ∧
      a.parabolics.Y0 ≤ d.nineResidual := by
  obtain ⟨a,_⟩ := exists_marked_natural_parabolics hG hM hu h hs t ht htS hnat
  have hP := a.first_le_selected hG hM hJ hu h hfull hs ht htS hnat
  let s := hs.1.nineSource_of_natural_moved_module hM hu h t ht htS hnat
  obtain ⟨n,hn,⟨e⟩⟩ := hs.2.2
  let hf := facts_of_small_binary_model (small_binary_model_of_marking hn e)
  refine ⟨a,hP,a.first_core_eq_sylow_plane_centralizer hs.1 d.nineMovingPlane
    (d.nineMovingPlane_le_UL s hG h hf t ht htS)
    (a.movingPlane_cut hG hM hu h hs ht htS hnat),
    a.first_moves_movingPlane hG hM hu h hs ht htS hnat,?_⟩
  exact embedded_pResidual_mono 2 (le_inf hP
    (a.parabolics_le.1.trans (sup_le d.L_component.1 d.S_le_G1)))

/-- The core, supplement, and both Sylow clauses of 15.1.29 hold on the
original marked triple. The later geometry theorem also supplies its orbit
and generation; the rank-two input remains a source obligation. -/
theorem exists_core_natural_parabolics {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) :
    ∃ a : NaturalFlag d t,
      a.parabolics.P0 ≤ M ∧
      a.parabolics.P0.pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      a.parabolics.P2 = ((T : Subgroup G) ⊓ centralizer (V : Set G)) ⊔ a.parabolics.Y2 ∧
      ¬ Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (V : Set G)) a.parabolics.P2 ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (V : Set G))
        (((T : Subgroup G) ⊓ centralizer (V : Set G)) ⊔ a.parabolics.Y3) ∧
      ⁅d.nineMovingPlane,a.parabolics.Y0⁆ = d.nineMovingPlane ∧
      a.parabolics.Y0 ≤ d.nineResidual := by
  obtain ⟨a,hP,_,hmoving,hY⟩ :=
    exists_placed_natural_parabolics hG hM hJ hu h hfull hs t ht htS hnat
  let s := hs.1.nineSource_of_natural_moved_module hM hu h t ht htS hnat
  exact ⟨a,hP,a.first_core hG hM hu h hs ht htS hnat,
    a.second_join hG hM hu h hs ht htS hnat,a.adjacent_not_sylow s hM h,
    a.remote_sylow hG hM hu h hs ht htS hnat,hmoving,hY⟩

/-- The natural flag now discharges generation, perfection, placement, and
both Sylow clauses in the actual source consumer. The end-node orbit,
rank-two input, and earlier C.1.34 are still explicit source obligations. -/
theorem false_of_naturalFlag {d : CaseIComponentData T M Mc V} {t : G}
    (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t)
    (horbit : ∀ x ∈ (T : Subgroup G),
      a.parabolics.Y2.map (MulAut.conj x).toMonoidHom = a.parabolics.Y2 ∨
        a.parabolics.Y2.map (MulAut.conj x).toMonoidHom = a.parabolics.Y3)
    (b : NaturalRankTwoInput a.parabolics)
    (hMS : NaturalParabolicMSClassification G) : False := by
  exact h.source_natural_parabolic_contradiction hG T hempty hM hu hfull d hs
    t ht htS hnat ⟨a.parabolics,
      a.geometry_of_end_orbit hG hM hJ hu h hfull hs ht htS hnat horbit,b⟩ hMS

/-- The source construction now identifies the actual L₀ globally and
places both chosen ends in its T-invariant Sylow extension. This supplies
the ambient group for the remaining end-node orbit argument. -/
theorem exists_normalized_natural_end_residual {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ a : NaturalFlag d t,
      d.naturalEndResidual = (primeToResidual 3 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ∧
      (T : Subgroup G) ≤ normalizer (d.naturalEndResidual : Set G) ∧
      (T : Subgroup G) ≤ normalizer ((d.naturalEndResidual ⊔ d.S : Subgroup G) : Set G) ∧
      a.parabolics.Y2 ≤ d.naturalEndResidual ∧
      a.parabolics.Y3 ≤ d.naturalEndResidual ∧
      a.parabolics.P2 ≤ d.naturalEndResidual ⊔ d.S ∧
      a.parabolics.P3 ≤ d.naturalEndResidual ⊔ d.S := by
  obtain ⟨a⟩ := exists_naturalFlag hG hM hu h hs t ht htS hnat
  exact ⟨a,d.naturalEndResidual_eq_global hG hM hu h hfull hs t ht htS hres,
    d.normalizes_naturalEndResidual hG h hs,d.normalizes_naturalEndResidual_sup_sylow hG h hs,
    a.end_nodes_in_residual_extension hG h hs hu hnat⟩


/-- The source hypotheses construct a single marked triple with complete
geometry. Only the rank-two input remains in the local construction. -/
theorem exists_natural_parabolic_geometry {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) :
    ∃ a : NaturalFlag d t, NaturalParabolicGeometry a.parabolics ∧
      (T : Subgroup G) ≤ normalizer (a.parabolics.Y2 : Set G) ∧
      (T : Subgroup G) ≤ normalizer (a.parabolics.Q2 : Set G) := by
  obtain ⟨a⟩ := exists_naturalFlag hG hM hu h hs t ht htS hnat
  exact ⟨a,a.geometry hG hM hJ hu h hfull hs ht htS hnat,
    a.normalizes_second hG hM hJ hu h hfull hs ht htS hnat⟩

/-- The source contradiction now needs only the rank-two input on the
same flag and the independent C.1.34 classification. All geometry is proved. -/
theorem false_of_naturalFlag_rankTwo {d : CaseIComponentData T M Mc V} {t : G}
    (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t)
    (b : NaturalRankTwoInput a.parabolics)
    (hMS : NaturalParabolicMSClassification G) : False := by
  exact h.source_natural_parabolic_contradiction hG T hempty hM hu hfull d hs
    t ht htS hnat ⟨a.parabolics,a.geometry hG hM hJ hu h hfull hs ht htS hnat,b⟩ hMS

/-- All rank-two clauses except the omega-center marking and the two-layer
nonblock assertion are constructed on the same original flag. -/
theorem hasNaturalParabolicData_of_centralizer_nonblock
    {d : CaseIComponentData T M Mc V} {t : G} (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t)
    (hcentral : a.parabolics.Q2 =
      ((a.parabolics.K ⊔ a.parabolics.Q2) ⊓ centralizer
        (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn d.S : Set G)).pCoreIn 2)
    (hblock : ¬ ChapterC.IsSL3EvenBlock a.parabolics.K 1) :
    d.HasNaturalParabolicData := by
  exact ⟨a.parabolics,a.geometry hG hM hJ hu h hfull hs ht htS hnat,
    a.rankTwoInput_of_centralizer_nonblock hG h hs hcentral hblock⟩

/-- Literal application of the rank-two construction to the source contradiction.
The omega-center identity, nonblock assertion, and C.1.34 still require discharge. -/
theorem false_of_naturalFlag_centralizer_nonblock
    {d : CaseIComponentData T M Mc V} {t : G} (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t)
    (hcentral : a.parabolics.Q2 =
      ((a.parabolics.K ⊔ a.parabolics.Q2) ⊓ centralizer
        (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn d.S : Set G)).pCoreIn 2)
    (hblock : ¬ ChapterC.IsSL3EvenBlock a.parabolics.K 1)
    (hMS : NaturalParabolicMSClassification G) : False := by
  exact h.source_natural_parabolic_contradiction hG T hempty hM hu hfull d hs
    t ht htS hnat
    (hasNaturalParabolicData_of_centralizer_nonblock a hG hM hJ hu h hfull hs ht htS
      hnat hcentral hblock) hMS


namespace NaturalFlag
variable {d : CaseIComponentData T M Mc V} {t : G}

/-- All twelve rank-two clauses are proved on the original natural flag. -/
theorem rankTwoInput (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) : NaturalRankTwoInput a.parabolics :=
  a.rankTwoInput_of_centralizer_nonblock hG h hs
    (a.second_core_eq_omegaCenter_core hG hM hu h hfull hs ht htS hnat)
    (a.pair_not_linear_block hG hM hu h hs ht htS hnat)
end NaturalFlag

/-- The original natural-module marking constructs both the full geometry
and rank-two input on one triple. No local construction premise remains. -/
theorem hasNaturalParabolicData_of_natural_moved_module
    {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) : d.HasNaturalParabolicData := by
  obtain ⟨a⟩ := exists_naturalFlag hG hM hu h hs t ht htS hnat
  exact ⟨a.parabolics,a.geometry hG hM hJ hu h hfull hs ht htS hnat,
    a.rankTwoInput hG hM hu h hfull hs ht htS hnat⟩

/-- Original 15.1.29 with every local construction discharged. Only the
independently owned C.1.34 classification remains an explicit premise. -/
theorem false_of_natural_moved_module
    {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t)
    (hMS : NaturalParabolicMSClassification G) : False := by
  exact h.source_natural_parabolic_contradiction hG T hempty hM hu hfull d hs t ht htS hnat
    (hasNaturalParabolicData_of_natural_moved_module hG hM hJ hu h hfull hs t ht htS hnat) hMS

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
