module

public import Theory.GroupTheory.MaximalTwoLocalCentralizers
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
public import Stellmacher.OmegaOneCenterMap
public import CFSG.Quasithin.MainForward.SourceReduction
public import CFSG.Quasithin.Chapter15.Section03.Constructions

/-!
# The centralizer-overgroup split in Theorem E

For a simple QTKE group, T is nontrivial. Thus Z = Ω₁(Z(T)) is a
nonidentity two-subgroup and T lies in C_G(Z). The centralizer-overgroup
family is nonempty, so it either has a unique member M_c belonging to M(T)
or has cardinality greater than one. These are precisely the additional
clauses of Hypotheses 14.1.5 and 15.4.1 in the empty-faithful-family branch.
The final theorem uses Section 15.3's literal central-involution subgroup;
the two omega-center conventions are definitionally equal.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Hypothesis
14.1.5, p.976; Hypothesis 15.4.1, p.1155; Theorem 15.4.25, p.1165.
This proves the source split; the two classification results still require
their independent recognition proofs.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section04

variable {G : Type*} [Group G] [Finite G] {K : GroupClass}

theorem centralOmega_ne_bot (h : IsSimpleQTKE K G) (T : Sylow 2 G) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ := by
  let _ : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot _).mpr
    (MainForward.sylow_ne_bot h T)
  have hn := Subgroup.omega_center_ne_bot T.isPGroup'
  intro he
  apply hn
  apply Subgroup.map_injective (f := (T : Subgroup G).subtype)
    (T : Subgroup G).subtype_injective
  simpa only [Stellmacher.omegaOneCenterAmbient, Subgroup.map_bot] using he

omit [Finite G] in
theorem sylow_le_centralizer_centralOmega (T : Sylow 2 G) :
    (T : Subgroup G) ≤
      centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  intro t ht
  rw [mem_centralizer_iff]
  intro z hz
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht |>.symm

theorem centralizer_overgroups_nonempty (h : IsSimpleQTKE K G) (T : Sylow 2 G) :
    (maximalTwoLocalOvergroups
      (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))).Nonempty := by
  let _ := Stellmacher.omegaOneCenterAmbient_elementaryAbelian (T : Subgroup G)
  exact maximalTwoLocalOvergroups_centralizer_nonempty (centralOmega_ne_bot h T)
    (IsElementaryAbelian.isPGroup 2 _)

theorem centralizer_overgroup_cases (h : IsSimpleQTKE K G) (T : Sylow 2 G) :
    (∃ M ∈ maximalTwoLocalOvergroups (T : Subgroup G),
      maximalTwoLocalOvergroups
        (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) = {M}) ∨
      1 < (maximalTwoLocalOvergroups
        (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard := by
  let _ := Stellmacher.omegaOneCenterAmbient_elementaryAbelian (T : Subgroup G)
  exact maximalTwoLocalOvergroups_centralizer_cases (centralOmega_ne_bot h T)
    (IsElementaryAbelian.isPGroup 2 _) (sylow_le_centralizer_centralOmega T)

theorem centralizer_overgroup_cases_section03 (h : IsSimpleQTKE K G) (T : Sylow 2 G) :
    (∃ M ∈ maximalTwoLocalOvergroups (T : Subgroup G),
      maximalTwoLocalOvergroups
        (centralizer (Section03.centralInvolutions T : Set G)) = {M}) ∨
      1 < (maximalTwoLocalOvergroups
        (centralizer (Section03.centralInvolutions T : Set G))).ncard :=
  centralizer_overgroup_cases h T

end CFSG.Quasithin.Chapter15.Section04
