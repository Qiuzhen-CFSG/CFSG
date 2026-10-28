module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalEnlargement
public import Theory.GroupTheory.PCoreQuotientInnerJoin

/-!
# The literal quotient action of the Chapter 6 enlargement

Conjugation on the original starred two-core quotient has kernel equal to
the enlargement's actual two-core when the starred quotient is centerless.
The resulting equivalence to the action image preserves representatives
and restricts to the original inner action on the starred group. If the
whole action is inner, the unchanged embedded core forces the enlargement
to be exactly the original starred group.

This supplies the quotient mechanism for the dihedral and other centerless
branches of DGS, *Groups and Graphs* (1985), 6.1, pp.118--119.
Only the original local data are used; the completion can be infinite.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P B : Subgroup G}

private theorem core_normalizes_star (d : LocalRankOneData P B) :
    B.pCoreIn 2 ≤ normalizer (d.Pstar : Set G) :=
  ((pCoreIn_le 2 B).trans (le_sup_right.trans d.supplement.le)).trans
    ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal)

/-- Conjugation by the actual full-Borel-core enlargement on the original starred quotient. -/
def localStarCoreAction (d : LocalRankOneData P B) :
    localEnlargement d →* MulAut (d.Pstar ⧸ pCore 2 d.Pstar) :=
  pCoreJoinAction 2 (core_normalizes_star d)

/-- On representatives the action is the original ambient conjugation. -/
theorem localStarCoreAction_mk (d : LocalRankOneData P B)
    (g : localEnlargement d) (x : d.Pstar) :
    localStarCoreAction d g (QuotientGroup.mk' (pCore 2 d.Pstar) x) =
      QuotientGroup.mk' (pCore 2 d.Pstar)
        (d.Pstar.normalizerMonoidHom
          ⟨g, by exact (sup_le d.Pstar.le_normalizer (core_normalizes_star d)) g.property⟩ x) :=
  pCoreJoinAction_mk 2 (core_normalizes_star d) g x

/-- Restriction to the starred factor is its original inner action. -/
theorem localStarCoreAction_on_star (d : LocalRankOneData P B) (x : d.Pstar) :
    localStarCoreAction d (inclusion le_sup_left x) =
      MulAut.conj (QuotientGroup.mk' (pCore 2 d.Pstar) x) :=
  pCoreJoinAction_on_component 2 (core_normalizes_star d) x

/-- The kernel is the actual two-core, not the local permutation kernel. -/
theorem localStarCoreAction_kernel (d : LocalRankOneData P B)
    (hz : center (d.Pstar ⧸ pCore 2 d.Pstar) = ⊥) :
    (localStarCoreAction d).ker = pCore 2 (localEnlargement d) :=
  pCoreJoinAction_kernel 2 (core_normalizes_star d) (isPGroup_pCoreIn 2 B) hz

/-- The actual core quotient is the literal action image. -/
def localStarCoreQuotientEquiv (d : LocalRankOneData P B)
    (hz : center (d.Pstar ⧸ pCore 2 d.Pstar) = ⊥) :
    (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃*
      (localStarCoreAction d).range :=
  pCoreJoinQuotientEquivRange 2 (core_normalizes_star d) (isPGroup_pCoreIn 2 B) hz

/-- The quotient equivalence retains each enlargement representative. -/
theorem localStarCoreQuotientEquiv_mk (d : LocalRankOneData P B)
    (hz : center (d.Pstar ⧸ pCore 2 d.Pstar) = ⊥) (x : localEnlargement d) :
    (localStarCoreQuotientEquiv d hz (QuotientGroup.mk' _ x) :
      MulAut (d.Pstar ⧸ pCore 2 d.Pstar)) = localStarCoreAction d x := by rfl

/-- Inner action and the unchanged embedded core prevent any enlargement. -/
theorem localEnlargement_eq_star_of_inner (d : LocalRankOneData P B)
    (hz : center (d.Pstar ⧸ pCore 2 d.Pstar) = ⊥)
    (hi : (localStarCoreAction d).range ≤ MulAut.innerSubgroup (d.Pstar ⧸ pCore 2 d.Pstar)) :
    localEnlargement d = d.Pstar := by
  have hm := map_subgroupOf_pCoreJoin_eq_top_of_inner d.Pstar (B.pCoreIn 2)
    (core_normalizes_star d) (isPGroup_pCoreIn 2 B) hz
    (fun r => hi ⟨inclusion le_sup_right r,rfl⟩)
  have hc := congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 (d.Pstar ⊔ B.pCoreIn 2 : Subgroup G)))) hm
  rw [comap_map_eq,QuotientGroup.ker_mk',comap_top] at hc
  have hh := congrArg (Subgroup.map (d.Pstar ⊔ B.pCoreIn 2).subtype) hc
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show d.Pstar ≤ d.Pstar ⊔ B.pCoreIn 2 from le_sup_left),
    ←MonoidHom.range_eq_map,range_subtype] at hh
  change d.Pstar ⊔ (localEnlargement d).pCoreIn 2 = localEnlargement d at hh
  rw [localEnlargement_core d,sup_eq_left.mpr (source_core_le_star d)] at hh
  exact hh.symm

end CFSG.Quasithin.ChapterF.Source.DGS85
