module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalSymmetric
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalAlternating

/-!
# The original escaping S₅ preimage

The chosen-module normalizers position the five-letter subgroup inside the
already constructed A₇ image. Its full preimage contains the original T,
has index 21 in L₀, and escapes M. Its literal two-core quotient is S₅,
with O₂(Y) = C_Y(U). The same hypotheses identify M intersected with L₀
as the stabilizer of the original plane Z_S.

Source: Aschbacher--Smith, 6.2.11, printed p.686. The index-five
intersection with M, H-star minimality and generation parameter two still
need proof; these statements do not assert the order-four contradiction.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- The source's M₀ is exactly the stabilizer of the original four-plane. -/
theorem source_local_four_intersection_maximal_stabilizer
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 4) :
    normalizer (L : Set G) ⊓ LocalQuotientAction.fourOvergroup (T : Subgroup G) L z =
      normalizer (ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ⊓
        LocalQuotientAction.fourOvergroup (T : Subgroup G) L z := by
  obtain ⟨hp,hNL⟩ := source_local_layer_normalizers D h h611 hnatural
  apply le_antisymm
  · exact le_inf (LocalQuotientAction.four_maximal_intersection_normalizes_plane
      h611 hnatural hz ho hT hp hNL hcard) inf_le_right
  · exact inf_le_inf_right _ (hp.trans hNL)

/-- The original local subgroup escapes M and has actual two-core quotient S₅. -/
theorem source_local_four_intersection_symmetric_core_quotient
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 4) :
    ∃ Y : Subgroup G, (T : Subgroup G) ≤ Y ∧
      Y ≤ LocalQuotientAction.fourOvergroup (T : Subgroup G) L z ∧
      Y.relIndex (LocalQuotientAction.fourOvergroup (T : Subgroup G) L z) = 21 ∧
      Y ∈ Chapter1.HOver G (T : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* Equiv.Perm (Fin 5)) ∧
      Y.pCoreIn 2 = Y ⊓ centralizer (sourceClosure (T : Subgroup G) L (wholeReduced T L) z : Set G) := by
  obtain ⟨hp,hNL⟩ := source_local_layer_normalizers D h h611 hnatural
  exact LocalQuotientAction.four_exists_escaping_symmetric_core_quotient
    h611 hnatural hz ho hT hp hNL hcard

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
