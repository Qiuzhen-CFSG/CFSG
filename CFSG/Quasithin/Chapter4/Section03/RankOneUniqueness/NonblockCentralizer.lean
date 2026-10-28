module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Configuration
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore

/-!
# The elementary centralizer step in original 4.3.9

Put S = T ∩ H and Z = Ω₁Z(S). The normalizer of a nontrivial C_Z(L)
lies in N_G(L), by the actual crossing element and maximal-overgroup
control. If C_Z(L) = C_Z(K), the escaping component K centralizes this
subgroup, so it must be trivial. The normal two-subgroup C_S(K) then
meets Z nontrivially unless C_S(K) = 1.

The fixed-subgroup equality remains explicit: its source proof uses the
natural-module splitting and I.1.6 with n > 1. Thus the final theorem is
a conditional step for original 4.3.9, not the completed MS reduction.
No block assumption or later uniqueness theorem is used.

Source: Aschbacher–Smith 4.3.5 and 4.3.9, printed pp.615–616.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual crossing controls the normalizer of every nonzero C_Z(L). -/
theorem SourceConfiguration.nonblock_omega_fixed_normalizer
    (c : SourceConfiguration T L)
    (hne : omegaCenterIn ((T : Subgroup G) ⊓ c.H) ⊓ centralizer (L : Set G) ≠ ⊥) :
    normalizer (omegaCenterIn ((T : Subgroup G) ⊓ c.H) ⊓
      centralizer (L : Set G) : Set G) ≤ normalizer (L : Set G) := by
  let S := (T : Subgroup G) ⊓ c.H
  let Z := omegaCenterIn S
  let A := Z ⊓ centralizer (L : Set G)
  have hLA : L ≤ normalizer (A : Set G) :=
    (le_centralizer_iff.mpr (show A ≤ centralizer (L : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hn : normalizer (S : Set G) ≤ normalizer (A : Set G) :=
    (le_inf (normalizer_le_normalizer_omegaCenterIn S)
      (c.normalizer_sylow.trans (normalizer_le_normalizer_centralizer L))).trans
        inf_normalizer_le_normalizer_inf
  have hAT : A ≤ (T : Subgroup G) :=
    (inf_le_left.trans (map_subtype_le _)).trans inf_le_left
  exact c.crossing_normalizer_control (T.isPGroup'.to_le hAT) hne
    (sup_le hLA (sup_le (S.le_normalizer.trans hn)
      (zpowers_le.mpr (hn c.crossing_normalizes))))

/-- Equality of the two fixed subgroups forces C_Z(K) to be trivial. -/
theorem SourceConfiguration.nonblock_omega_centralizer_eq_bot
    (c : SourceConfiguration T L)
    (he : omegaCenterIn ((T : Subgroup G) ⊓ c.H) ⊓ centralizer (L : Set G) =
      omegaCenterIn ((T : Subgroup G) ⊓ c.H) ⊓
        centralizer (c.K.map c.H.subtype : Set G)) :
    omegaCenterIn ((T : Subgroup G) ⊓ c.H) ⊓
      centralizer (c.K.map c.H.subtype : Set G) = ⊥ := by
  by_contra hn
  have hnL := c.nonblock_omega_fixed_normalizer (fun hb => hn (he ▸ hb))
  have hK : c.K.map c.H.subtype ≤ normalizer
      (omegaCenterIn ((T : Subgroup G) ⊓ c.H) ⊓ centralizer (L : Set G) : Set G) := by
    change c.K.map c.H.subtype ≤ normalizer
      ((omegaCenterIn ((T : Subgroup G) ⊓ c.H) ⊓ centralizer (L : Set G) : Subgroup G) : Set G)
    rw [he]
    exact (le_centralizer_iff.mpr inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  exact c.component_outside (hK.trans hnL)

/-- Source application of the normal two-group center argument: C_S(K) = 1. -/
theorem SourceConfiguration.nonblock_sylow_centralizer_eq_bot
    (c : SourceConfiguration T L)
    (he : omegaCenterIn ((T : Subgroup G) ⊓ c.H) ⊓ centralizer (L : Set G) =
      omegaCenterIn ((T : Subgroup G) ⊓ c.H) ⊓
        centralizer (c.K.map c.H.subtype : Set G)) :
    ((T : Subgroup G) ⊓ c.H) ⊓ centralizer (c.K.map c.H.subtype : Set G) = ⊥ := by
  let S := (T : Subgroup G) ⊓ c.H
  let A := c.K.map c.H.subtype
  have hnA : S ≤ normalizer (A : Set G) :=
    inf_le_right.trans c.normalizer_component.le
  have hnC : S ≤ normalizer (S ⊓ centralizer (A : Set G) : Set G) :=
    (le_inf S.le_normalizer (hnA.trans (normalizer_le_normalizer_centralizer A))).trans
      inf_normalizer_le_normalizer_inf
  by_contra hn
  apply inf_omegaCenterIn_ne_bot_of_normalized_twoGroup
    (S ⊓ centralizer (A : Set G)) S inf_le_left (T.isPGroup'.to_le inf_le_left) hnC hn
  exact bot_unique ((le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans_eq
    (c.nonblock_omega_centralizer_eq_bot he))
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
