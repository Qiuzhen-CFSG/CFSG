module

public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Solvable parabolics generating A₆ and S₆ over every Sylow two-subgroup

The alternating duad and syntheme parabolics are the already constructed
copies of S₄. Their full symmetric counterparts are solvable extensions
by the sign image. Conjugating the standard incident pair transports both
solvability and the proved generating join to every Sylow two-subgroup.

Source: Aschbacher–Smith, I.5, printed pp.419–422; used in the
solvable-overgroup argument of 13.8.21(2), printed p.956 (PDF p.973).
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix

private theorem solvable_of_even (H : Subgroup S6)
    [Group.IsSolvable (H.comap (alternatingGroup (Fin 6)).subtype)] :
    Group.IsSolvable H := by
  apply Group.isSolvable_of_ker_le_range
    ((alternatingGroup (Fin 6)).subtype.subgroupComap H)
    (Equiv.Perm.sign.comp H.subtype)
  intro g hg
  exact ⟨⟨⟨g.val, hg⟩, g.property⟩, rfl⟩

instance a6Duad_solvable : Group.IsSolvable a6DuadStabilizer := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  exact Group.isSolvable_of_surjective a6DuadModelEquiv.surjective

instance a6Syntheme_solvable : Group.IsSolvable a6SynthemeStabilizer := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  exact Group.isSolvable_of_surjective
    ResidualPairRecognition.ComponentLocals.edgeEquiv.surjective

instance duad_solvable : Group.IsSolvable duadStabilizer := by
  let : Group.IsSolvable (duadStabilizer.comap (alternatingGroup (Fin 6)).subtype) := a6Duad_solvable
  exact solvable_of_even _
instance syntheme_solvable : Group.IsSolvable synthemeStabilizer := by
  let : Group.IsSolvable (synthemeStabilizer.comap (alternatingGroup (Fin 6)).subtype) := a6Syntheme_solvable
  exact solvable_of_even _

private theorem solvable_map {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (H : Subgroup X) [Group.IsSolvable H] : Group.IsSolvable (H.map f) :=
  Group.isSolvable_of_surjective (f.subgroupMap_surjective H)

theorem a6_solvable_parabolic_generation (P : Sylow 2 A6) :
    ∃ J K : Subgroup A6, (P : Subgroup A6) ≤ J ∧ (P : Subgroup A6) ≤ K ∧
      Group.IsSolvable J ∧ Group.IsSolvable K ∧ J ⊔ K = ⊤ := by
  obtain ⟨g, hg, _⟩ := a6_coatoms_over_sylow P
  let e := (MulAut.conj g).mapSubgroup
  refine ⟨e a6DuadStabilizer, e a6SynthemeStabilizer,
    hg ▸ e.monotone a6Borel_le_duadStabilizer,
    hg ▸ e.monotone a6Borel_le_synthemeStabilizer,
    solvable_map _ _, solvable_map _ _, ?_⟩
  rw [← e.map_sup, a6_parabolics_sup, e.map_top]

theorem solvable_parabolic_generation (P : Sylow 2 S6) :
    ∃ J K : Subgroup S6, (P : Subgroup S6) ≤ J ∧ (P : Subgroup S6) ≤ K ∧
      Group.IsSolvable J ∧ Group.IsSolvable K ∧ J ⊔ K = ⊤ := by
  obtain ⟨g, hg, _⟩ := coatoms_over_sylow P
  let e := (MulAut.conj g).mapSubgroup
  refine ⟨e duadStabilizer, e synthemeStabilizer,
    hg ▸ e.monotone borel_le_duadStabilizer,
    hg ▸ e.monotone borel_le_synthemeStabilizer,
    solvable_map _ _, solvable_map _ _, ?_⟩
  rw [← e.map_sup, parabolics_sup, e.map_top]


end Theory.SpecificGroups.SymmetricSix
