module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalMinimal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalSymmetric

/-!
# Source consumer for the actual order-four H-star subgroup

The Chapter 6 construction is applied to the literal chosen-module setup.
It supplies the index-five intersection and H-star minimality before the
generation-parameter contradiction is assembled in LocalFourExclusion.

Source: Aschbacher--Smith, 6.2.11, printed p.686.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- An actual H-star subgroup in the contrary order-four branch has
index-five intersection with the original maximal two-local subgroup. -/
theorem source_local_four_intersection_hstar_index_five
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 4) :
    ∃ Y : Subgroup G, Y ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      Y ≤ LocalQuotientAction.fourOvergroup (T : Subgroup G) L z ∧
      (Y ⊓ normalizer (L : Set G)).relIndex Y = 5 := by
  obtain ⟨hp,hNL⟩ := source_local_layer_normalizers D h h611 hnatural
  obtain ⟨Y,hY,hYX,hi,_⟩ :=
    LocalQuotientAction.four_exists_hstar_index_five_seed
      h611 hnatural hz ho hT hp hNL le_rfl hcard
  exact ⟨Y,hY,hYX,hi⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
