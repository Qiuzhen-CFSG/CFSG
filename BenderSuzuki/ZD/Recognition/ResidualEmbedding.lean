module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Setup
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action
import Mathlib.GroupTheory.Nilpotent

/-!
# The fusion endpoint of the residual ZD argument

If `M` contains an ambient Sylow two-subgroup and controls its fusion,
an even abelianization of `M` gives a proper two-residual of `G` by focal
transfer. In a simple group that residual would be trivial, forcing `M = G`.
Consequently `O²(M) = M`: a proper two-residual would give a nontrivial
two-group quotient, whose abelianization is nontrivial as well.

This proves the final contradiction in GLS, Volume 4, Chapter 2, after
Proposition 17.6. The action premise is now supplied by
`residualAction_of_minimalCounterexample`; the generation and local residual
arguments remain source obligations. The conditional assembly API below is
preserved for its existing consumers.
-/

noncomputable section

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII PFchapter1section1

universe u

/-- The focal endpoint rules out an even abelianization of `M`. This needs
only properness, simplicity, Sylow containment, and fusion control. -/
public theorem SimpleReduction.not_two_dvd_abelianization
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (r : SimpleReduction Z M) (h : IsProductDisconnected Z M) :
    ¬ 2 ∣ Nat.card (M ⧸ derivedSubgroup M) := by
  intro heven
  obtain ⟨S, hSM, hfusion⟩ := r.fusion
  obtain ⟨hlt, hsup⟩ :=
    hallPResidual_factorization_of_dvd_abelianization_of_controlsFusionIn
      M S hSM hfusion heven
  rcases r.simple.eq_bot_or_eq_top_of_normal (External.hallPResidual 2 G)
      (External.hallPResidual_normal 2 G) with hbot | htop
  · exact h.proper (by simpa [hbot] using hsup)
  · exact hlt.ne htop

private theorem two_dvd_abelianization_of_twoResidual_ne_top
    {H : Type*} [Group H] [Finite H]
    (hres : External.hallPResidual 2 H ≠ ⊤) :
    2 ∣ Nat.card (H ⧸ derivedSubgroup H) := by
  let R := External.hallPResidual 2 H
  let : R.Normal := External.hallPResidual_normal 2 H
  let Q := H ⧸ R
  let : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hres
  have hQ : IsPGroup 2 Q := External.hallPResidual_quotient_isPGroup 2
  let : Group.IsNilpotent Q := hQ.isNilpotent
  have hcomm : commutator Q ≠ ⊤ :=
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Q).ne
  obtain ⟨n, hn⟩ := (hQ.to_quotient (commutator Q)).exists_card_eq
  have hnpos : n ≠ 0 := by
    intro hnzero
    have hidx := Subgroup.one_lt_index_of_ne_top hcomm
    rw [Subgroup.index_eq_card, hn, hnzero] at hidx
    norm_num at hidx
  have heven : 2 ∣ (commutator Q).index := by
    rw [Subgroup.index_eq_card, hn]
    exact dvd_pow_self 2 hnpos
  let q : H →* Q := QuotientGroup.mk' R
  have hmap : (commutator H).map q = commutator Q := by
    rw [map_commutator_eq, q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective R)]
    rfl
  have hle : commutator H ≤ (commutator Q).comap q :=
    Subgroup.map_le_iff_le_comap.mp hmap.le
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective R)] at hdvd
  have := heven.trans hdvd
  simpa only [derivedSubgroup, derivedSeries_one, Subgroup.index_eq_card] using this

/-- In the simple reduction, `M` has no nontrivial two-group quotient.
Here `hallPResidual 2 M` is `O²(M)`, not `O_{2'}(M)`. -/
public theorem SimpleReduction.twoResidual_eq_top
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (r : SimpleReduction Z M) (h : IsProductDisconnected Z M) :
    External.hallPResidual 2 M = ⊤ := by
  by_contra hres
  exact r.not_two_dvd_abelianization h
    (two_dvd_abelianization_of_twoResidual_ne_top hres)

/-- Conditional assembly of the residual argument. The three source
obligations have distinct mathematical outputs and can be proved independently.
This does not assert the unconditional residual strong-embedding theorem. -/
public theorem stronglyEmbedded_of_residual_steps
    (action : ∀ {G : Type u} [Group G] [Finite G]
      (Z : Set G) (M : Subgroup G),
      MinimalCounterexample Z M → SimpleReduction Z M → ResidualAction Z M)
    (generation : ∀ {G : Type u} [Group G] [Finite G]
      (Z : Set G) (M : Subgroup G),
      MinimalCounterexample Z M → SimpleReduction Z M → ResidualAction Z M →
      ¬ IsStronglyEmbedded M → ResidualGeneration Z M)
    (residual : ∀ {G : Type u} [Group G] [Finite G]
      (Z : Set G) (M : Subgroup G),
      MinimalCounterexample Z M → SimpleReduction Z M → ResidualAction Z M →
      ¬ IsStronglyEmbedded M → ResidualGeneration Z M →
      External.hallPResidual 2 M ≠ ⊤)
    {G : Type u} [Group G] [Finite G] (Z : Set G) (M : Subgroup G)
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) :
    IsStronglyEmbedded M := by
  by_contra hnot
  have ha := action Z M h r
  have hg := generation Z M h r ha hnot
  exact residual Z M h r ha hnot hg (r.twoResidual_eq_top h.disconnected)

end BenderSuzuki.ZD
