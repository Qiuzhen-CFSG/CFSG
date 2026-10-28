module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalResidual
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalInitial

/-!
# The final local action clauses from the order-eight intersection

On the original whole reduced layer, the chosen module supplies the local
normalizer identities and uniqueness over LT. The order-eight intersection
from source 6.2.11 gives the invariant flag and hence both conclusions of
6.2.12: residual centralization and the literal kernel of the action on
U/⟨z⟩. The same cardinality forces C_G(z) outside M.

Only the order-eight assertion remains explicit in this application. Its
proof, and the other earlier LocalAnalysis fields, remain with
qt-d-1222-recognition-local-analysis. Final identification is owned by
qt-d-1222-rankone-recognition-identification. No LocalAnalysis record or
recognition conclusion is used to prove these two clauses.

Source: Aschbacher--Smith, 6.2.9--12, printed pp.685--686, applied to
[R₂(LT),L] in 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- Both source 6.2.12 clauses on the literal centralizer and quotient action.
All uniqueness and normalizer hypotheses are discharged by the chosen setup. -/
theorem source_local_action_geometry_of_core_card
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (commutatorLayer T L ⊓
      (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 8) :
    (¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G)) ∧
    (pResidual 2 (centralizer ({z} : Set G) ⊓ normalizer (L : Set G) : Subgroup G)).map
      (centralizer ({z} : Set G) ⊓ normalizer (L : Set G)).subtype ≤
        centralizer (commutatorLayer T L : Set G) ∧
    (∀ x ∈ centralizer ({z} : Set G),
      (∀ u ∈ sourceClosure (T : Subgroup G) L (wholeReduced T L) z, ⁅x, u⁆ ∈ zpowers z) ↔
        x ∈ (centralizer ({z} : Set G)).pCoreIn 2) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hplane := (source_local_layer_normalizers D h h611 hnatural).1
  have hu := (Chapter4.Section03.RankOneUniqueness.unique_sylow_join D h.toHypothesis1221).2.2
  exact ⟨local_centralizer_not_le_of_core_card h611 hnatural hE hz ho hcard,
    local_residual_centralizes_of_core_card h611 hnatural hE hz ho hT hplane hcard,
    local_action_kernel_of_core_card h611 hnatural hE hu hz ho hT hplane hcard⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
