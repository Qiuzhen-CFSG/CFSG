module
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.Contracts
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
/-!
# Source block selection for E.6.23

The full E.6.7 product at a characteristic-two hyperplane centralizer supplies
an escaping factor. The rank-one bound would give 1 < n ≤ 1, so that factor
is an A₃ or A₅ block. Its original relative subnormality and actual block
module are retained. This discharges the selection consequence of E.6.10
in the unchanged E.6.23 enlargement contract.
Source: Aschbacher–Smith, E.6.7, E.6.10 and E.6.23, pp.246,249,254–255.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement
open InvariantSubspaces.BlockSelection
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}

theorem earlierBlockSelection_of_e67 (h67 : E67Input T M V) :
    EarlierBlockSelection M V := by
  intro U hU hhyper hfit
  have hc : HasCharacteristicTwo (centralizer (U : Set G)) := by
    change centralizer (pCore 2 (centralizer (U : Set G)) :
      Set (centralizer (U : Set G))) ≤ pCore 2 (centralizer (U : Set G))
    rw [← hfit]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  obtain ⟨d⟩ := h67 U hU (centralizer (U : Set G))
    (inf_le_right.trans (Subgroup.centralizer_le hU.1)) le_rfl hc
  have hex : ∃ i, ¬ d.block i ≤ M := by
    by_contra! hall
    exact hU.2.2.1 (d.generated.le.trans (sup_le inf_le_right (iSup_le hall)))
  obtain ⟨i,hi⟩ := hex
  have halt : ChapterC.IsAlternatingBlock (d.block i) 3 ∨
      ChapterC.IsAlternatingBlock (d.block i) 5 := by
    rcases d.type i with ⟨n,hn⟩ | ha | ha
    · obtain ⟨_,_,_,_,_,_,_,_,_,hbound⟩ := d.rankOne i n hn
      have hh := hn.1
      rw [hhyper.2] at hbound
      omega
    · exact Or.inl ha
    · exact Or.inr ha
  have hs : ChapterC.IsShort (d.block i) := halt.elim (fun ha => ha.2.1) (fun ha => ha.2.1)
  have hb : ChapterC.IsBlock ((d.block i).subgroupOf (centralizer (U : Set G))) :=
    ⟨inferInstance,hs.of_mulEquiv (subgroupOfEquivOfLe (d.le i)).symm,d.subnormal i⟩
  exact ⟨d.block i,⟨d.le i,hb,halt⟩,hi⟩

theorem source_earlierBlockSelection
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) :
    EarlierBlockSelection M V :=
  earlierBlockSelection_of_e67 (e67Input_knownSimple h)
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement
