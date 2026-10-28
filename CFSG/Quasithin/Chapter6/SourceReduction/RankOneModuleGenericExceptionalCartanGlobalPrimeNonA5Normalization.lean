module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeMovedComponentActualPair

/-!
# Non-A₅ normalization of the changed Sylow

The source 1.2.8(3) maximality argument applies to the actual selected
right factor whenever its intrinsic quotient is not PSL₂(4).  The factor is
in the original full-Sylow local family, and its movement is the literal
residual identity already proved for `LocalData`.  Consequently the changed
Sylow in the nonzero-core extension is exactly the original normalizing
Sylow.  This extension deliberately keeps the A₅ and parabolic branches
separate; it does not identify a selected parabolic with an ambient
component or assert the final residual equality.

Source: Aschbacher--Smith 1.2.8(3) and 5.2.2, printed pp.506--507 and
648--649 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- Every changed Sylow supplied by the nonzero-core extension is the
normalizing Sylow when the selected right factor is non-A₅. -/
theorem LocalData.nonA5_changedSylow_eq_normalizingSylow
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hR : R ∈ Chapter1.L G (T : Subgroup G))
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map
        (extension T L H B D R).subtype) :
    (P : Subgroup (extension T L H B D R)).map
        (extension T L H B D R).subtype = normalizingSylow T R := by
  apply d.changedSylow_eq_of_nonA5 h hH c hd hz
    hR hnot P hTP

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
