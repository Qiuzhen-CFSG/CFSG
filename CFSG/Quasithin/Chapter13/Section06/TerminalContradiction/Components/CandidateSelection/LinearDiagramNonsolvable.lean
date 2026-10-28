module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LinearDiagram
public import FeitThompson.FinalTheorem
/-!
# The linear terminal seed from the nonsolvable outside member

The original 13.6.25(3) makes the selected H-star member nonsolvable.
Its Sylow two-subgroup cannot be normal: the Sylow is solvable and its
odd-order quotient is solvable by Feit--Thompson. Thus H-star minimality
gives the actual minimal-parabolic hypothesis needed to construct the
linear diagram actor. This removes the ambient Sylow-normalizer bound
from the linear branch of the original source argument.

Source: Aschbacher--Smith, 13.6.25(3), 13.6.27 and E.2.2(2b), printed
pp.934 and 215--216.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
variable {G : Type*} [Group G] [Finite G]
private theorem not_normal_sylow_of_nonsolvable
    (T : Sylow 2 G) (hns : ¬ Group.IsSolvable G) : ¬ (T : Subgroup G).Normal := by
  intro hnormal
  let := hnormal
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  have hodd : Odd (Nat.card (G ⧸ (T : Subgroup G))) := by
    rw [← index_eq_card]
    exact Nat.not_even_iff_odd.mp (fun h => T.not_dvd_index h.two_dvd)
  exact hns ((Group.isSolvable_iff_subgroup_quotient (T : Subgroup G)).mpr
    ⟨inferInstance, odd_order_theorem _ hodd⟩)
/-- The actual nonsolvable H-star member supplies minimal parabolicity without
requiring a separate bound on the ambient Sylow normalizer. -/
theorem residual_diagram_of_HStar_in_overgroup_nonsolvable
    (T : Sylow 2 G) {M A C : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hA : A ∈ Chapter3.HStar (T : Subgroup G) M)
    (hns : ¬ Group.IsSolvable A) (hAC : A ≤ C)
    (e : (pResidual 2 A ⧸ pCore 2 (pResidual 2 A)) ≃* L3Four) :
    ∃ e' : ((pResidual 2 A).map (inclusion hAC) ⧸
        pCore 2 ((pResidual 2 A).map (inclusion hAC))) ≃* L3Four,
      NontrivialDynkinAction ((T : Subgroup G).subgroupOf C)
        ((pResidual 2 A).map (inclusion hAC)) e' := by
  have hTA : (T : Subgroup G) ≤ A := hA.1.1.2
  let S := T.subtype hTA
  have hnormal : ¬ ((T : Subgroup G).subgroupOf A).Normal :=
    not_normal_sylow_of_nonsolvable S hns
  have hP : ChapterB.IsMinimalParabolicOver S ⊤ :=
    ChapterE.Section06.FixedPointBounds.ParabolicCartan.minimalParabolic_subtype T A
      (Chapter3.HStar.minimalParabolic T hTM hA (Or.inr hnormal))
  obtain ⟨e',hd⟩ := exists_nontrivialDynkinAction_of_minimalParabolic
    (pResidual 2 A) e S (pResidual_sup_sylow_eq_top S) hP
  obtain ⟨e'',hd'⟩ := nontrivialDynkinAction_map
    (inclusion hAC) (inclusion_injective hAC) (pResidual 2 A) (S : Subgroup A) e' hd
  have hS : (S : Subgroup A).map (inclusion hAC) = (T : Subgroup G).subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le (hTA.trans hAC)]
    change ((T : Subgroup G).subgroupOf A).map A.subtype = _
    exact map_subgroupOf_eq_of_le hTA
  exact ⟨e'',hS ▸ hd'⟩

/-- Source 13.6.25(3) makes the selected outside member nonsolvable. Together
with the exact linear equality from 5.2.3, this constructs its candidate. -/
theorem linear_candidate_of_HStar_nonsolvable
    (T : Sylow 2 G) {M A C : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hA : A ∈ Chapter3.HStar (T : Subgroup G) M)
    (hns : ¬ Group.IsSolvable A) (hAC : A ≤ C)
    (e : (pResidual 2 A ⧸ pCore 2 (pResidual 2 A)) ≃* L3Four)
    (K : Subgroup C)
    (hK : (pResidual 2 A).map A.subtype = K.map C.subtype) :
    Candidate ((T : Subgroup G).subgroupOf C) K := by
  have he : (pResidual 2 A).map (inclusion hAC) = K := by
    apply map_injective C.subtype_injective
    rw [map_map]
    exact hK
  have hd := residual_diagram_of_HStar_in_overgroup_nonsolvable T hTM hA hns hAC e
  rw [he] at hd
  exact Or.inr (Or.inr hd)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
