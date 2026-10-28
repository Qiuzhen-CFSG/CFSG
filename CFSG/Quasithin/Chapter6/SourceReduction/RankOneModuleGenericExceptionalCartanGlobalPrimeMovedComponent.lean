module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximality
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeChangedSylowMarking

/-!
# Remaining overcomponents for the changed Sylow in original 5.2.2

The original right factor is moved: its Sylow conjugate span is O²(H),
which strictly contains it in the nonzero generated-core branch. Thus the
source four-model theorem applies to its literal intrinsic two-core quotient.

For a non-PSL₂(4) right quotient, a larger changed Sylow forces a proper
common overcomponent. The proved rank-one embedding restrictions show
that this overcomponent is either normalized by the full original Sylow
or has intrinsic quotient J₁. Binary PSL₂, Suzuki, and odd-prime PSL₂
containing quotients have been excluded without an embedding callback.
The two remaining cases, and hence unconditional local maximality, are
not asserted here.

Source: Aschbacher--Smith, 1.2.8(1--3), printed pp.506--507,
and the changed-Sylow argument of 5.2.2, printed pp.648--649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The original nonzero-core branch supplies movement, so the actual
right quotient lies in the four source models of 1.2.1(3). -/
theorem LocalData.right_moved_component_model
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hR : R ∈ Chapter1.L G (T : Subgroup G)) :
    Chapter1.Section02.NonnormalCComponentModel (R ⧸ pCore 2 R) := by
  apply Chapter1.Section02.MovedMaximality.moved_local_model h.qtke T hR
  rw [←d.residual_eq_conjugateSpan]
  exact d.right_lt_residual hH.1.1.2 c hd hz

/-- A larger changed Sylow has a strictly larger common component in one
of the two remaining containing cases. Every relative component and quotient
refers to the original common overgroup and original right factor. -/
theorem LocalData.changedSylow_remaining_overcomponent
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
    Chapter1.Section02.NonnormalCComponentModel (R ⧸ pCore 2 R) ∧
      ((P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype =
          normalizingSylow T R ∨
        ∃ I : Subgroup G, R < I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
          ((T : Subgroup G) ≤ normalizer (I : Set G) ∨
            Nonempty ((I ⧸ pCore 2 I) ≃* Janko1.Model))) := by
  refine ⟨d.right_moved_component_model h hH c hd hz hR, ?_⟩
  have hcases := (two_group_over_index_two_sylow T (normalizingSylow T R)
    ((P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    inf_le_left (d.normalizingSylow_index hH.1.1.2 c hd hz) (P.isPGroup'.map _) hTP).2
  rcases hcases with he | ⟨U,hU⟩
  · exact Or.inl he
  · right
    let X := normalizer (normalizingSylow T R : Set G) ⊔ H
    have hX := d.common_normal_overgroup h hH c hd hz
    have hTX : (T : Subgroup G) ≤ X :=
      (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_right
    obtain ⟨I,hRI,hIX,hI,_⟩ := d.common_normal_component h hH c hd hz
    have hIl : I ∈ Chapter1.L G (T : Subgroup G) :=
      Chapter1.mem_L_of_cComponent hX.1
        ⟨T.subtype hTX,map_subgroupOf_eq_of_le hTX⟩ hIX hI
    have hne : R ≠ I := by
      intro he
      apply d.changedSylow_not_common_component h hH c hd hz P hTP hU
      simpa only [←he] using hI
    refine ⟨I,lt_of_le_of_ne hRI hne,hIX,hI,?_⟩
    exact (Chapter1.Section02.MovedMaximality.local_chain_eq_or_normalized_or_janko
      h.qtke T hR hIl hRI hnot).resolve_left hne

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
