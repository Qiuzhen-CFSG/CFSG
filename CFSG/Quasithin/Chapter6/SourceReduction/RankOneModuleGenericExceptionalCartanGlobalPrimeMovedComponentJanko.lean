module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityJanko
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeMovedComponent

/-!
# The remaining normalized overcomponent in the changed-Sylow argument

The new J₁ exclusion removes the last moved containing model from the
previous reduction. Movement is derived from the original LocalData
residual identity and strict residual containment in the nonzero-core
branch. A larger changed Sylow now forces a strict common overcomponent
normalized by the original full Sylow.

The source embedding restriction excluding that normalized overcomponent
remains necessary to discharge `changedSylow_eq_of_right_maximal`.

Source: Aschbacher--Smith, 1.2.8(2--3), printed pp.506--507, applied to
original 5.2.2, printed pp.648--649 of `refs/quasithin.pdf`.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- A larger changed Sylow forces a strict overcomponent normalized by the
original full Sylow. The J₁ alternative is excluded using the actual moved
right factor, its literal two-core quotient, and the concrete J₁ model. -/
theorem LocalData.changedSylow_normalized_overcomponent
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
    let X := normalizer (normalizingSylow T R : Set G) ⊔ H
    (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype =
        normalizingSylow T R ∨
      ∃ I : Subgroup G, R < I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
        (T : Subgroup G) ≤ normalizer (I : Set G) := by
  rcases (d.changedSylow_remaining_overcomponent h hH c hd hz hR hnot P hTP).2 with
    he | ⟨I,hRI,hIX,hI,hn⟩
  · exact Or.inl he
  · right
    refine ⟨I,hRI,hIX,hI,?_⟩
    rcases hn with hn | hj
    · exact hn
    · exfalso
      let X := normalizer (normalizingSylow T R : Set G) ⊔ H
      have hX := d.common_normal_overgroup h hH c hd hz
      have hTX : (T : Subgroup G) ≤ X :=
        (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_right
      have hIl : I ∈ Chapter1.L G (T : Subgroup G) :=
        Chapter1.mem_L_of_cComponent hX.1
          ⟨T.subtype hTX,map_subgroupOf_eq_of_le hTX⟩ hIX hI
      have hm : R < conjugateSpanBy R (T : Subgroup G) := by
        rw [←d.residual_eq_conjugateSpan]
        exact d.right_lt_residual hH.1.1.2 c hd hz
      exact hRI.ne (Chapter1.Section02.MovedMaximality.local_chain_eq_of_janko_quotient
        T hR hIl hRI.le (Chapter1.Section02.MovedMaximality.moved_local_model h.qtke T hR hm)
        hnot hj)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
