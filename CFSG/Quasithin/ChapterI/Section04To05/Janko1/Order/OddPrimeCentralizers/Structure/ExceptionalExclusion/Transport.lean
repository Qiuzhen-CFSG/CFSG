module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.AlternativesData
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.FourCentralizers

/-!
# Transport of the exceptional normalizer

Transport the elementary subgroup, its order, and both normalizer factors
through an actual ambient automorphism. This permits the same local
calculation at the conjugate subgroup B in Bender (4.1), printed p.225.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G]
/-- The exceptional normalizer configuration is preserved by an actual
ambient automorphism, in particular by conjugation. -/
public theorem ExceptionalOddNormalizer.map {A : Subgroup G} (e : ExceptionalOddNormalizer A) (f : G ≃* G) :
    ExceptionalOddNormalizer (A.map f.toMonoidHom) := by
  let _ := e.elementary
  refine ⟨IsElementaryAbelian.map f.toMonoidHom, ?_, ?_⟩
  · rw [card_map_of_injective f.injective, e.card]
  obtain ⟨V, X, hV, hVcard, hXcard, hXV, hN⟩ := e.normalizer_decomposition
  let _ := hV
  refine ⟨V.map f.toMonoidHom, X.map f.toMonoidHom,
    IsElementaryAbelian.map f.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [card_map_of_injective f.injective, hVcard]
  · rw [card_map_of_injective f.injective, hXcard]
  · rw [← map_equiv_normalizer_eq]
    exact map_mono hXV
  · rw [← map_equiv_normalizer_eq, hN, Subgroup.map_sup, Subgroup.map_sup]
end CFSG.Quasithin.Janko1CentralizerData
