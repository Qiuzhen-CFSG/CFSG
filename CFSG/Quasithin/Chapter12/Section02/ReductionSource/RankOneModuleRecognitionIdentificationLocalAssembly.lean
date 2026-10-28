module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalOmegaLine
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalPairResidual
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalNoncyclic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalPlanes
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalResidual
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalUniqueness

/-!
# Assembly of the common local analysis with two remaining source inputs

The original omega-centralizer escape gives the central omega line. All
normalizer, fusion, quaternion-pair and closure conclusions are supplied by
the completed local theorem families. The order-eight intersection supplies
the literal action kernel and residual centralization through 6.2.12.

The earlier 6.1.5 premise is owned by
qt-d-1222-rankone-recognition-natural. The numerical premise from 6.2.8--11
and its final discharge remain with qt-d-1222-recognition-local-analysis.
This conditional constructor does not assert either missing source theorem.
The final identification consumer is qt-d-1222-rankone-recognition-identification.

Source: Aschbacher--Smith, 6.2.1--12, printed pp.680--686, applied to
[R₂(LT),L] in 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- Every common-analysis field on the original subgroups, retaining exactly
the earlier omega escape and the still-unproved 6.2.11 numerical input. -/
theorem source_local_analysis_of_omega_escape_and_core_card
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hescape : ¬ centralizer (centralOmega (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G))
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (commutatorLayer T L ⊓
      (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 8) :
    LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z := by
  obtain ⟨hnplane, hnlayer⟩ := source_local_layer_normalizers D h h611 hnatural
  obtain ⟨hln, hpn, hfit, hcl, hcc, hlc⟩ :=
    source_local_centralizer_geometry D h h611 hnatural hz ho hT
  obtain ⟨_, hres, hker⟩ :=
    source_local_action_geometry_of_core_card D h h611 hnatural hz ho hT hcard
  exact {
    central_omega := source_local_centralOmega_eq_zpowers_of_escape h611 hnatural
      hescape hz ho hT
    normalizer_plane := hnplane
    normalizer_layer := hnlayer
    plane_unique := source_local_plane_unique D h h611 hnatural
    hyperplane_unique := source_local_hyperplane_unique D h h611 hnatural
    commuting_normalized := source_local_commuting_normalized D h h611 hnatural
    commuting_noncyclic := source_local_commuting_noncyclic D h h611 hnatural
    non_two_pair := source_local_non_two_pair D h h611 hnatural
    layer_normalizer := hln
    plane_normalizer := hpn
    fitting_core := hfit
    closure_le_core := hcl
    closure_core_commutator := hcc
    action_kernel := hker
    layer_core_card := hcard
    layer_closure_commutator := hlc
    residual_centralizes := hres }

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
