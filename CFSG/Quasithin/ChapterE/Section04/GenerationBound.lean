module

public import CFSG.Quasithin.ChapterE.Section04.GenerationBound.Construction
public import CFSG.Quasithin.ChapterE.Section04.GenerationBound.ResidualObstruction

/-!
# The maximal-subfamily argument for E.4.2

Choose a subfamily of maximal cardinality whose local two-residuals fix
the fixed space at its rank budget. Some omitted overgroup fails to
normalize the corresponding weak subgroup. Local residual control permits
adjoining that overgroup, while monotonicity preserves all earlier
centralization conditions, contradicting maximality.

`moduleA_le_of_local_residual_control` proves this argument with its local
obligation explicit. `moduleA_le_of_residual_commutators` reduces that
obligation to the printed commutator equalities. Neither is the unconditional
source theorem: derivation of the local control from `IsLocalOvergroup`
remains open. In particular, a nontrivial odd abelian quotient obstructs the
blanket residual equality, as proved in `ResidualObstruction`.

The local convention remains F*(H/O₂(H)), as documented in GenerationSetup;
O²(H) always denotes the two-residual, distinct from O₂(H).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.2,
printed p.241 (PDF p.252).
-/

public section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValueBound
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The source set of subfamilies: each selected two-residual fixes the fixed
space at the sum of its local ranks. -/
@[expose] def IsAdmissible (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    (k : ℕ) (Γ : Finset (Subgroup G)) : Prop :=
  ∀ H ∈ Γ, fixedSpace ρ (weakSubgroup (fixedSpaceFamily ρ (k + 1))
    (localRankBudget Γ) T) ≤ fixedSpace ρ ((pResidual 2 H).map H.subtype)

/-- The embedded two-residual and the ambient Sylow subgroup generate each overgroup of T. -/
theorem residual_sup_sylow (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) :
    (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := congrArg (Subgroup.map H.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTH))
  simpa only [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH,
    ← MonoidHom.range_eq_map, range_subtype] using h

/-- Each selected overgroup preserves the fixed space, since its residual fixes it and T preserves it. -/
theorem IsAdmissible.le_stabilizer (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    {k : ℕ} {Γ : Finset (Subgroup G)} (hΓ : IsAdmissible ρ T k Γ)
    {H : Subgroup G} (hH : H ∈ Γ) (hTH : (T : Subgroup G) ≤ H) :
    H ≤ subspaceStabilizer ρ (fixedSpace ρ
      (weakSubgroup (fixedSpaceFamily ρ (k + 1)) (localRankBudget Γ) T)) := by
  rw [← residual_sup_sylow T H hTH]
  apply sup_le
  · apply le_subspaceStabilizer
    intro h hh v hv
    have hf : ρ h v = v := hΓ H hH hv ⟨h, hh⟩
    rw [hf]
    exact hv
  · exact fixedSpace_invariant_normalizer ρ (T.toSubgroup.le_normalizer.trans
      (weakSubgroup_normalizer ρ (k + 1) (localRankBudget Γ) T))

/-- An admissible subfamily must leave an overgroup which does not normalize W_j; otherwise all of G preserves its fixed space and L fixes C_V(T). -/
theorem exists_not_normalizing_of_admissible
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hcore : pCore 2 G = ⊥) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (hfixed : ¬ fixedSpace ρ T ≤ fixedSpace ρ L)
    {Δ Γ : Finset (Subgroup G)} (hΔ : IsGeneratingFamily T Δ) (hΓΔ : Γ ⊆ Δ)
    (hΓ : IsAdmissible ρ T (localRankBudget Δ) Γ)
    (hΩ : (fixedSpaceFamily ρ (localRankBudget Δ + 1)).Nonempty) :
    ∃ H ∈ Δ, H ∉ Γ ∧ ¬ H ≤ normalizer (weakSubgroup
      (fixedSpaceFamily ρ (localRankBudget Δ + 1)) (localRankBudget Γ) T : Set G) := by
  classical
  by_contra! hn
  let W := weakSubgroup (fixedSpaceFamily ρ (localRankBudget Δ + 1)) (localRankBudget Γ) T
  have hstab : ∀ H ∈ Δ, H ≤ subspaceStabilizer ρ (fixedSpace ρ W) := by
    intro H hH
    by_cases hHΓ : H ∈ Γ
    · exact hΓ.le_stabilizer ρ T hHΓ (hΔ.1 H (hΓΔ hHΓ))
    · exact fixedSpace_invariant_normalizer ρ (hn H hH hHΓ)
  have htop : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ (fixedSpace ρ W) := by
    rw [← hΔ.2.1]
    exact sSup_le (fun H hH => hstab H hH)
  have hL : fixedSpace ρ W ≤ fixedSpace ρ L := by
    have h := le_fixedSpace_commutator_of_invariant ρ (le_top.trans htop :
      L ≤ subspaceStabilizer ρ (fixedSpace ρ W)) (le_refl (fixedSpace ρ W))
    rw [show ⁅L, W⁆ = L from commutator_weakSubgroup_eq_component ρ T L hcore hgen hΩ _] at h
    exact h
  exact hfixed ((fixedSpace_le_weakSubgroup_fixedSpace ρ _ _ T).trans hL)

/-- Failure of normalization produces an actual corank-family generator outside the embedded two-core. -/
theorem exists_corank_member_not_le_core
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (H : Subgroup G) {k j : ℕ}
    (hn : ¬ H ≤ normalizer (weakSubgroup (fixedSpaceFamily ρ k) j T : Set G)) :
    ∃ B ∈ corankFamily (fixedSpaceFamily ρ k) j,
      B ≤ (T : Subgroup G) ∧ ¬ B ≤ (pCore 2 H).map H.subtype := by
  by_contra! hall
  apply hn
  apply weakSubgroup_normalized_of_le_core ρ T H
  exact sSup_le (fun B hB => hall B hB.1 hB.2)

/-- The maximal-subfamily argument with its local residual-control obligation
explicit. This is a conditional reduction, not the source theorem E.4.2. -/
theorem moduleA_le_of_local_residual_control
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hcore : pCore 2 G = ⊥) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (hfixed : ¬ fixedSpace ρ T ≤ fixedSpace ρ L)
    (Δ : Finset (Subgroup G)) (hΔ : IsGeneratingFamily T Δ)
    (hlocal : ∀ (j : ℕ) (H : Subgroup G), H ∈ Δ →
      j + primeRank 2 (H ⧸ pCore 2 H) ≤ localRankBudget Δ →
      ¬ H ≤ normalizer (weakSubgroup (fixedSpaceFamily ρ (localRankBudget Δ + 1)) j T : Set G) →
      fixedSpace ρ (weakSubgroup (fixedSpaceFamily ρ (localRankBudget Δ + 1))
        (j + primeRank 2 (H ⧸ pCore 2 H)) T) ≤
          fixedSpace ρ ((pResidual 2 H).map H.subtype)) :
    moduleA ρ ≤ (localRankBudget Δ : ℕ∞) := by
  classical
  apply (moduleA_le_iff_next_family_empty ρ (localRankBudget Δ)).mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro A hA
  let S := Δ.powerset.filter (IsAdmissible ρ T (localRankBudget Δ))
  have hS : S.Nonempty := ⟨∅, by simp [S, IsAdmissible]⟩
  obtain ⟨Γ, hΓS, hmax⟩ := S.exists_max_image Finset.card hS
  obtain ⟨hΓΔ, hΓ⟩ := Finset.mem_filter.mp hΓS
  have hsub : Γ ⊆ Δ := Finset.mem_powerset.mp hΓΔ
  obtain ⟨H, hHΔ, hHΓ, hn⟩ := exists_not_normalizing_of_admissible ρ T L
    hcore hgen hfixed hΔ hsub hΓ ⟨A, hA⟩
  have hins : insert H Γ ⊆ Δ := Finset.insert_subset hHΔ hsub
  have hm : localRankBudget Γ + primeRank 2 (H ⧸ pCore 2 H) ≤ localRankBudget Δ := by
    rw [← localRankBudget_insert Γ H hHΓ]
    exact localRankBudget_mono hins
  have hadm : IsAdmissible ρ T (localRankBudget Δ) (insert H Γ) := by
    intro K hK
    rcases Finset.mem_insert.mp hK with hKH | hK
    · subst K
      rw [localRankBudget_insert Γ H hHΓ]
      exact hlocal (localRankBudget Γ) H hHΔ hm hn
    · have hw := weakSubgroup_mono (fixedSpaceFamily ρ (localRankBudget Δ + 1))
        (T : Subgroup G) (localRankBudget_mono (Finset.subset_insert H Γ))
      exact (fixedSpace_antitone ρ hw).trans (hΓ K hK)
  have hcard := hmax (insert H Γ) (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hins, hadm⟩)
  rw [Finset.card_insert_of_notMem hHΓ] at hcard
  omega

/-- The printed commutator equalities suffice for the local-control obligation.
Their derivation from the printed local Fitting hypothesis is not asserted. -/
theorem moduleA_le_of_residual_commutators
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hcore : pCore 2 G = ⊥) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (hfixed : ¬ fixedSpace ρ T ≤ fixedSpace ρ L)
    (Δ : Finset (Subgroup G)) (hΔ : IsGeneratingFamily T Δ)
    (hc : ∀ H ∈ Δ, ∀ (j : ℕ) (B : Subgroup G),
      B ∈ corankFamily (fixedSpaceFamily ρ (localRankBudget Δ + 1)) j →
      B ≤ (T : Subgroup G) → ¬ B ≤ (pCore 2 H).map H.subtype →
      ⁅(pResidual 2 H).map H.subtype, B⁆ = (pResidual 2 H).map H.subtype) :
    moduleA ρ ≤ (localRankBudget Δ : ℕ∞) := by
  apply moduleA_le_of_local_residual_control ρ T L hcore hgen hfixed Δ hΔ
  intro j H hH hm hn
  obtain ⟨B, hB, hBT, hBQ⟩ := exists_corank_member_not_le_core ρ T H hn
  exact fixedSpace_weakSubgroup_le_residual_of_commutator ρ T H (hΔ.1 H hH)
    hm hB hBT (hc H hH j B hB hBT hBQ)

end CFSG.Quasithin.ChapterE.ValueBound

