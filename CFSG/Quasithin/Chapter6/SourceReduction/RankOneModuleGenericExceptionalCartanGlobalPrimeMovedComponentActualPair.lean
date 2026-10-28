module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityActualPairSource
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeMovedComponentObstruction
/-!
# Moved-component maximality in the actual changed-Sylow branch

The LocalData residual identity supplies movement of the original right
factor. Source 1.2.8(3) now puts that same factor in LStar(G,T), discharging
the maximality premise of the existing changed-Sylow theorem. The actual
Sylow, quotient convention, original non-PSL₂(4) assumption and complete
KnownSimple predicate remain unchanged.

Source: Aschbacher--Smith, 1.2.8(3), p.507, applied in 5.2.2, pp.648--649.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The original LocalData movement and non-A₅ quotient now give the actual
maximal local component required by the changed-Sylow argument. -/
theorem LocalData.right_mem_LStar_of_nonA5
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hR : R ∈ Chapter1.L G (T : Subgroup G))
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    R ∈ Chapter1.LStar G (T : Subgroup G) := by
  apply Chapter1.Section02.MovedMaximality.moved_local_mem_LStar h.qtke T hR _ hnot
  rw [←d.residual_eq_conjugateSpan]
  exact d.right_lt_residual hH.1.1.2 c hd hz

/-- The literal changed Sylow is the original normalizing Sylow, using the
proved source 1.2.8 maximality rather than an additional maximality premise. -/
theorem LocalData.changedSylow_eq_of_nonA5
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hR : R ∈ Chapter1.L G (T : Subgroup G))
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype) :
    (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype =
      normalizingSylow T R :=
  d.changedSylow_eq_of_right_maximal h hH c hd hz
    (d.right_mem_LStar_of_nonA5 h hH c hd hz hR hnot) P hTP
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
