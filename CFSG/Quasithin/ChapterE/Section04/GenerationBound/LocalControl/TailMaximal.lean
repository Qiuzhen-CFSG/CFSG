module

public import CFSG.Quasithin.ChapterE.Section04.GenerationBound.LocalControl.CoreSpace

/-!
# Maximal subfamilies preserving the later fixed spaces

The local step in E.4.2 can be weakened from pointwise fixation by O²(H)
to preservation by H of every later weak fixed space. Choose a subfamily
of maximal cardinality for this latter property. Raising the rank budget
preserves every old condition. An omitted overgroup failing to normalize
the earlier weak subgroup can then be adjoined using local eventual
invariance. The ambient quasisimple commutator calculation supplies the
contradiction if no such omitted overgroup exists.

The kernel-times-Sylow normality criterion from CoreSpace is sufficient for
this local step. Its derivation in the prime-order and quasisimple local
quotient cases is not asserted here. In particular these theorems do not
claim to prove E.4.2 or to refute its stronger local residual-control route.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.2,
printed p.241 (PDF p.252).
-/

public section

open Subgroup Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValueBound.LocalControl
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Each selected overgroup preserves every weak fixed space from the subfamily budget onwards. -/
@[expose] def IsTailAdmissible (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    (k : ℕ) (Γ : Finset (Subgroup G)) : Prop :=
  ∀ H ∈ Γ, ∀ n, localRankBudget Γ ≤ n →
    H ≤ subspaceStabilizer ρ
      (fixedSpace ρ (weakSubgroup (fixedSpaceFamily ρ (k + 1)) n T))

/-- A subfamily preserving the later spaces leaves an omitted overgroup that does not normalize the current weak subgroup. -/
theorem exists_not_normalizing_of_tail_admissible
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hcore : pCore 2 G = ⊥) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (hfixed : ¬ fixedSpace ρ T ≤ fixedSpace ρ L)
    {Δ Γ : Finset (Subgroup G)} (hΔ : IsGeneratingFamily T Δ)
    (hΓ : IsTailAdmissible ρ T (localRankBudget Δ) Γ)
    (hΩ : (fixedSpaceFamily ρ (localRankBudget Δ + 1)).Nonempty) :
    ∃ H ∈ Δ, H ∉ Γ ∧ ¬ H ≤ normalizer (weakSubgroup
      (fixedSpaceFamily ρ (localRankBudget Δ + 1)) (localRankBudget Γ) T : Set G) := by
  classical
  by_contra! hn
  let W := weakSubgroup (fixedSpaceFamily ρ (localRankBudget Δ + 1)) (localRankBudget Γ) T
  have hstab : ∀ H ∈ Δ, H ≤ subspaceStabilizer ρ (fixedSpace ρ W) := by
    intro H hH
    by_cases hHΓ : H ∈ Γ
    · exact hΓ H hHΓ _ le_rfl
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

omit [Finite G] in
/-- An overgroup preserving the tail after its rank cost can be adjoined while keeping every old invariance condition. -/
theorem IsTailAdmissible.insert
    [DecidableEq (Subgroup G)]
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    {k : ℕ} {Γ : Finset (Subgroup G)} (hΓ : IsTailAdmissible ρ T k Γ)
    (H : Subgroup G) (hHΓ : H ∉ Γ)
    (hH : ∀ n, localRankBudget Γ + primeRank 2 (H ⧸ pCore 2 H) ≤ n →
      H ≤ subspaceStabilizer ρ
        (fixedSpace ρ (weakSubgroup (fixedSpaceFamily ρ (k + 1)) n T))) :
    IsTailAdmissible ρ T k (insert H Γ) := by
  classical
  intro K hK n hn
  rcases Finset.mem_insert.mp hK with hKH | hK
  · subst K
    exact hH n ((localRankBudget_insert Γ H hHΓ) ▸ hn)
  · exact hΓ K hK n ((localRankBudget_mono (Finset.subset_insert H Γ)).trans hn)

/-- Conditional E.4.2 bound from local preservation of all later fixed spaces. Local residual centralization is not required. -/
theorem moduleA_le_of_local_eventual_invariance
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hcore : pCore 2 G = ⊥) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (hfixed : ¬ fixedSpace ρ T ≤ fixedSpace ρ L)
    (Δ : Finset (Subgroup G)) (hΔ : IsGeneratingFamily T Δ)
    (hlocal : ∀ (j : ℕ) (H : Subgroup G), H ∈ Δ →
      j + primeRank 2 (H ⧸ pCore 2 H) ≤ localRankBudget Δ →
      ¬ H ≤ normalizer (weakSubgroup (fixedSpaceFamily ρ (localRankBudget Δ + 1)) j T : Set G) →
      ∀ n, j + primeRank 2 (H ⧸ pCore 2 H) ≤ n →
        H ≤ subspaceStabilizer ρ
          (fixedSpace ρ (weakSubgroup (fixedSpaceFamily ρ (localRankBudget Δ + 1)) n T))) :
    moduleA ρ ≤ (localRankBudget Δ : ℕ∞) := by
  classical
  apply (moduleA_le_iff_next_family_empty ρ (localRankBudget Δ)).mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro A hA
  let S := Δ.powerset.filter (IsTailAdmissible ρ T (localRankBudget Δ))
  have hS : S.Nonempty := ⟨∅, by simp [S, IsTailAdmissible]⟩
  obtain ⟨Γ, hΓS, hmax⟩ := S.exists_max_image Finset.card hS
  obtain ⟨hΓΔ, hΓ⟩ := Finset.mem_filter.mp hΓS
  have hsub : Γ ⊆ Δ := Finset.mem_powerset.mp hΓΔ
  obtain ⟨H, hHΔ, hHΓ, hn⟩ := exists_not_normalizing_of_tail_admissible ρ T L
    hcore hgen hfixed hΔ hΓ ⟨A, hA⟩
  have hins : insert H Γ ⊆ Δ := Finset.insert_subset hHΔ hsub
  have hm : localRankBudget Γ + primeRank 2 (H ⧸ pCore 2 H) ≤ localRankBudget Δ := by
    rw [← localRankBudget_insert Γ H hHΓ]
    exact localRankBudget_mono hins
  have hadm := hΓ.insert ρ T H hHΓ (hlocal (localRankBudget Γ) H hHΔ hm hn)
  have hcard := hmax (insert H Γ) (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hins, hadm⟩)
  rw [Finset.card_insert_of_notMem hHΓ] at hcard
  omega

/-- Relative normality of each relevant local kernel times T suffices for the full numerical bound. This additional premise remains to be established from the source inputs. -/
theorem moduleA_le_of_local_kernel_sup_normal
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hcore : pCore 2 G = ⊥) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (hfixed : ¬ fixedSpace ρ T ≤ fixedSpace ρ L)
    (Δ : Finset (Subgroup G)) (hΔ : IsGeneratingFamily T Δ)
    (hlocal : ∀ (j : ℕ) (H : Subgroup G), H ∈ Δ →
      j + primeRank 2 (H ⧸ pCore 2 H) ≤ localRankBudget Δ →
      ¬ H ≤ normalizer (weakSubgroup (fixedSpaceFamily ρ (localRankBudget Δ + 1)) j T : Set G) →
      ((subspaceKernel ρ (coreFixedSpace ρ (localRankBudget Δ)
        (j + primeRank 2 (H ⧸ pCore 2 H)) H) H ⊔ (T : Subgroup G)).subgroupOf H).Normal) :
    moduleA ρ ≤ (localRankBudget Δ : ℕ∞) := by
  apply moduleA_le_of_local_eventual_invariance ρ T L hcore hgen hfixed Δ hΔ
  intro j H hH hm hn
  exact eventual_invariance_of_kernel_sup_normal ρ T H (hΔ.1 H hH) _ _
    (hlocal j H hH hm hn)

end CFSG.Quasithin.ChapterE.ValueBound.LocalControl
