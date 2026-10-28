module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Basic
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry

/-!
# Selecting an outside point parabolic over S∩L

The two-group S∩L fixes a nonzero natural vector, so its point parabolic contains
S∩L. If that parabolic lay in M, the full point stabilizer would preserve the
marked two-plane. Rigidity of invariant subspaces of a full parabolic would
identify that plane with the fixed line, contradicting their dimensions.
Noncentrality of the projected Z-action and the MS-pair hypotheses are separate
remaining obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130 (PDF pp.1146–1147).
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic

variable {G : Type*} [Group G] {d : LocalData G} {L : Subgroup G}

/-- The fixed two-subgroup determines a nonzero point and hence an actual parabolic over S∩L. -/
theorem exists_point_over_sylow (h : NaturalDual d L) :
    ∃ x : Space 4, x ≠ 0 ∧ d.S ⊓ L ≤ point h x := by
  let A := ((d.S ⊓ L).subgroupOf L).map (linearAction (by decide) h.model)
  have hp : IsPGroup 2 (d.S ⊓ L : Subgroup G) :=
    d.T.isPGroup'.to_le (inf_le_left.trans inf_le_left)
  have hA : IsPGroup 2 A :=
    (hp.of_equiv (subgroupOfEquivOfLe (show d.S ⊓ L ≤ L from inf_le_right)).symm).map _
  have hn := BinaryLinear.fixedSpace_ne_bot (V := Space 4)
    (by norm_num [Space, Nat.card_eq_fintype_card]) hA
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  refine ⟨x, hx0, ?_⟩
  intro s hs
  apply (mem_point h x ⟨s, hs.2⟩).mpr
  exact hx _ (mem_map_of_mem _ hs)

/-- No point parabolic can lie in the marked plane parabolic L∩M. -/
theorem point_not_le_M (h : NaturalDual d L) (plane : PlaneParabolic d L h.model)
    {x : Space 4} (hx : x ≠ 0) : ¬ point h x ≤ d.M := by
  intro hPM
  have hp : pointStabilizer x ≤ BinaryLinear.parabolic plane.plane := by
    intro g hg
    obtain ⟨l, hl⟩ := linearAction_surjective (by decide) h.model g
    have hm : l ∈ (d.M ⊓ L).subgroupOf L :=
      ⟨hPM ((mem_point h x l).mpr (hl ▸ hg)), l.property⟩
    rw [plane.intersection] at hm
    change linearAction (by decide) h.model l ∈ BinaryLinear.parabolic plane.plane at hm
    rwa [hl] at hm
  have h0 : plane.plane ≠ ⊥ := by
    intro he
    have hd := plane.dimension
    rw [he, finrank_bot] at hd
    omega
  have h1 : plane.plane ≠ ⊤ := by
    intro he
    have hd := plane.dimension
    rw [he, finrank_top] at hd
    norm_num [Space] at hd
  rw [← parabolic_line_eq hx] at hp
  have he := BinaryLinear.FourParabolicAction.parabolic_le_imp_eq h0 h1 hp
  have hd := finrank_span_singleton (K := ZMod 2) hx
  rw [he, plane.dimension] at hd
  omega

/-- A point parabolic over S∩L, together with its proved failure of containment in M. -/
theorem exists_outside_point (h : NaturalDual d L) (plane : PlaneParabolic d L h.model) :
    ∃ x : Space 4, x ≠ 0 ∧ d.S ⊓ L ≤ point h x ∧ ¬ point h x ≤ d.M := by
  obtain ⟨x, hx, hS⟩ := exists_point_over_sylow h
  exact ⟨x, hx, hS, point_not_le_M h plane hx⟩


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic

end
