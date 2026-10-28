module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.Evenness
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.FourObstruction

/-!
# Centralizer selection for the residual two-point stabilizer

Evenness supplies an involution of `D = M ∩ Mᵗ`. Finiteness then permits
choosing one which maximizes `Γ = Z ∩ M ∩ C_G(u)`, as in GLS, Volume 4,
Chapter 2, (16A). Its centralizer is proper by simplicity and product
disconnection. The last lemma isolates the generation contradiction used
in Lemma 16.4 and Proposition 16.5: `[O_{2'}(D),t]` cannot lie in the
centralizer of an involution which already centralizes `z` and `t`.

These are preliminary results only. The model recognition, coprime
commutator generation, and rank contradiction of Proposition 16.5 remain
separate proof obligations.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The set `Γ` in (16A), before taking its generated subgroup. -/
@[expose] public def residualCentralizerTrace (Z : Set G) (M : Subgroup G) (u : G) : Set G :=
  {z | z ∈ Z ∧ z ∈ M ∧ Commute z u}

/-- The nonzero-rank part of Proposition 16.5, without local recognition. -/
public theorem residualPairStabilizer_exists_involution
    (h : IsProductDisconnected Z M) (ha : ResidualAction Z M)
    (hn : ¬ IsStronglyEmbedded M) {t : G} (ht : t ∉ M) :
    ∃ u ∈ residualPairStabilizer M t, IsInvolution u := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card'
    (G := residualPairStabilizer M t) 2 (two_dvd_card_residualPairStabilizer h ha hn ht)
  have hi : IsInvolution u := by
    obtain ⟨hsq, hne⟩ := orderOf_eq_prime_iff.mp hu
    exact ⟨hne, hsq⟩
  exact ⟨u, u.property, IsInvolution.map_of_injective hi
    (residualPairStabilizer M t).subtype (residualPairStabilizer M t).subtype_injective⟩

/-- The maximal choice in source (16A). No model structure is assumed. -/
public theorem exists_residualCentralizerTrace_maximal
    (h : IsProductDisconnected Z M) (ha : ResidualAction Z M)
    (hn : ¬ IsStronglyEmbedded M) {t : G} (ht : t ∉ M) :
    ∃ u ∈ residualPairStabilizer M t, IsInvolution u ∧ u ∉ Z ∧
      ∀ v ∈ residualPairStabilizer M t, IsInvolution v →
        (residualCentralizerTrace Z M v).ncard ≤
          (residualCentralizerTrace Z M u).ncard := by
  obtain ⟨v, hvD, hv⟩ := residualPairStabilizer_exists_involution h ha hn ht
  obtain ⟨u, hu, hmax⟩ := Set.exists_max_image
    {u | u ∈ residualPairStabilizer M t ∧ IsInvolution u}
    (fun u => (residualCentralizerTrace Z M u).ncard)
    (Set.toFinite _) ⟨v, hvD, hv⟩
  exact ⟨u, hu.1, hu.2, not_mem_Z_of_mem_residualPairStabilizer h ht hu.1,
    fun w hw hi => hmax w ⟨hw, hi⟩⟩

/-- Maximality turns containment of traces into equality, as used in 16.4. -/
public theorem residualCentralizerTrace_eq_of_maximal
    {t u v : G}
    (hmax : ∀ w ∈ residualPairStabilizer M t, IsInvolution w →
      (residualCentralizerTrace Z M w).ncard ≤
        (residualCentralizerTrace Z M u).ncard)
    (hvD : v ∈ residualPairStabilizer M t) (hv : IsInvolution v)
    (hle : residualCentralizerTrace Z M u ⊆ residualCentralizerTrace Z M v) :
    residualCentralizerTrace Z M u = residualCentralizerTrace Z M v :=
  Set.eq_of_subset_of_ncard_le hle (hmax v hvD hv)

/-- Simplicity here forces trivial center: the abelian branch would make a
 distinguished involution central, contrary to its proper centralizer. -/
public theorem SimpleReduction.center_eq_bot
    (r : SimpleReduction Z M) (h : IsProductDisconnected Z M) :
    Subgroup.center G = ⊥ := by
  rcases r.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with hc | hc
  · exact hc
  · obtain ⟨z, hz, hzM⟩ := h.nonempty
    have hzC : z ∈ Subgroup.center G := hc ▸ Subgroup.mem_top z
    have htop : (⊤ : Subgroup G) ≤ M := by
      intro x _
      apply h.centralizer_le hz hzM
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hzC x)
    exact False.elim (h.proper (top_le_iff.mp htop))

/-- The selected centralizer is eligible for proper-subgroup induction. -/
public theorem SimpleReduction.involution_centralizer_ne_top
    (r : SimpleReduction Z M) (h : IsProductDisconnected Z M)
    {u : G} (hu : IsInvolution u) :
    Subgroup.centralizer ({u} : Set G) ≠ ⊤ := by
  intro heq
  have huC := Subgroup.centralizer_eq_top_iff_subset.mp heq (Set.mem_singleton u)
  rw [r.center_eq_bot h] at huC
  exact hu.ne_one (Subgroup.mem_bot.mp huC)

/-- The generation contradiction in 16.4 and 16.5, before the local model
 analysis establishes containment of the commutator subgroup. -/
public theorem residualCommutator_not_le_involution_centralizer
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hg : ResidualGeneration Z M) {z t u : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hu : IsInvolution u) (hzu : Commute z u) (htu : Commute t u) :
    ¬ residualCommutator M t ≤ Subgroup.centralizer ({u} : Set G) := by
  intro hK
  have hL : residualGenerated M z t ≤ Subgroup.centralizer ({u} : Set G) :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr hzu.eq))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr htu.eq))) hK
  rw [hg z hz hzM t ht htM] at hL
  exact r.involution_centralizer_ne_top h hu (top_le_iff.mp hL)

end BenderSuzuki.ZD
