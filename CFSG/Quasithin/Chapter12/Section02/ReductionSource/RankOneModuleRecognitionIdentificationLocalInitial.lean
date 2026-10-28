module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalNormalizers
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalClosure
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFusionNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedWeakClosure

/-!
# Initial common local analysis on the whole Chapter 12 layer

The original chosen module supplies uniqueness over LT and central-line
normalizer control. This discharges the E.6.1 and factorization inputs in
source 6.2.1 and 6.2.3. For the constructed central involution, source
6.2.9 gives the two local normalizer identities. Even characteristic and
the order-two quotient of the plane give F*(H)=O₂(H), U≤O₂(H),
[U,O₂(H)]≤⟨z⟩ and [V,U]≤V∩U on the literal normal closure.

These applications prove the indicated fields, not the complete
LocalAnalysis record. Its central-omega, fusion, non-two pair, converse
kernel, order-eight intersection and residual-centralization obligations
remain with qt-d-1222-recognition-local-analysis. Final identification is
owned by qt-d-1222-rankone-recognition-identification.

Source: Aschbacher--Smith, 6.2.1, 6.2.3, 6.2.9--10, pp.680, 685,
applied to R₂(LT) in 12.2.2(3d), p.795.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Source 6.2.1 on the original R₂(LT) layer; all normalizer inputs are discharged. -/
theorem source_local_layer_normalizers
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n) :
    normalizer (ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (commutatorLayer T L : Set G) ∧
    normalizer (commutatorLayer T L : Set G) ≤ normalizer (L : Set G) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  exact ⟨local_normalizer_plane h611 hnatural hE
    (source_central_line_normalizer_factorization D h.toHypothesis1221 h611 hnatural.2.2.2.1),
    hE.normalizer_le⟩

/-- Source 6.2.3 for every mutually normalizing pair of actual conjugates. -/
theorem source_local_commuting_normalized
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hleft : commutatorLayer T L ≤
      normalizer ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hright : (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      normalizer (commutatorLayer T L : Set G)) :
    ⁅commutatorLayer T L, (commutatorLayer T L).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  exact local_commuting_normalized h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    (source_central_line_normalizer_factorization D h.toHypothesis1221 h611 hnatural.2.2.2.1)
    g hleft hright

/-- Source 6.2.9 and the closure clauses of 6.2.10 on the literal centralizer. -/
theorem source_local_centralizer_geometry
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    {z : G} (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let H := centralizer ({z} : Set G)
    let U := sourceClosure (T : Subgroup G) L (wholeReduced T L) z
    (H ⊓ normalizer (commutatorLayer T L : Set G) = H ⊓ normalizer (L : Set G)) ∧
    (H ⊓ normalizer (ZS (T : Subgroup G) L (wholeReduced T L) : Set G) =
      H ⊓ normalizer (L : Set G)) ∧
    generalizedFitting H = pCore 2 H ∧ U ≤ H.pCoreIn 2 ∧
    ⁅U, H.pCoreIn 2⁆ ≤ zpowers z ∧
    ⁅commutatorLayer T L, U⁆ ≤ commutatorLayer T L ⊓ U := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hplane := (source_local_layer_normalizers D h h611 hnatural).1
  obtain ⟨hU, hc⟩ := local_closure_core h611 hnatural hz ho hT
  exact ⟨local_layer_normalizer hE hz ho, local_plane_normalizer h611 hnatural hE hz ho hplane,
    local_involution_fitting_core h611 ho hT, hU, hc,
    local_layer_closure_commutator h611 hnatural hz ho hT hplane⟩

/-- Construct a witness carrying all the initial local-centralizer conclusions.
The remaining fields of LocalAnalysis are not claimed by this theorem. -/
theorem exists_reduced_initial_local_analysis
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n) :
    ∃ z ∈ ZS (T : Subgroup G) L (wholeReduced T L), orderOf z = 2 ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      centralizer ({z} : Set G) ≠ ⊤ ∧
      (let H := centralizer ({z} : Set G)
       let U := sourceClosure (T : Subgroup G) L (wholeReduced T L) z
       (H ⊓ normalizer (commutatorLayer T L : Set G) = H ⊓ normalizer (L : Set G)) ∧
       (H ⊓ normalizer (ZS (T : Subgroup G) L (wholeReduced T L) : Set G) =
         H ⊓ normalizer (L : Set G)) ∧
       generalizedFitting H = pCore 2 H ∧ U ≤ H.pCoreIn 2 ∧
       ⁅U, H.pCoreIn 2⁆ ≤ zpowers z ∧
       ⁅commutatorLayer T L, U⁆ ≤ commutatorLayer T L ⊓ U) := by
  obtain ⟨z, hz, ho, hT⟩ := exists_central_involution_in_ZS h611
  exact ⟨z, hz, ho, hT, involution_centralizer_ne_top h611 hnatural hz ho,
    source_local_centralizer_geometry D h h611 hnatural hz ho hT⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
