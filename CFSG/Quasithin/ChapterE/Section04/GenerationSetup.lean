module

public import CFSG.Quasithin.ChapterE.Section04.Basic
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.PGroupCore
public import Theory.PrimeRank
public import Theory.GroupTheory.ConjugacyFamilySpan
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The generating-family construction in E.4.2

This module publishes the actual local quotient condition and rank budget,
independently of the construction of the Mathieu overgroups. The corank-family
span is the source W_j(X, Ω). In particular its witness A need not lie in X;
this matters when X is the two-core of an overgroup. Conjugation invariance
proves normalization, and faithfulness excludes trivial corank-family members.

The printed statement of E.4.2 writes F*(H)/O₂(H). Its proof and the E.4.3
application instead use F*(H/O₂(H)), which is the condition encoded here.
These operations must not be interchanged. The generation-bound theorem and
the existence of the Mathieu generating families remain separate obligations.
The residual O²(H) in that proof is not the two-core O₂(H).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.2–3,
printed pp. 241–242 (PDF pp. 252–253).
-/

public section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValueBound
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- All subgroups of corank at most j in a member of Ω. The containing member need not lie in the subgroup in which the weak closure is computed. -/
@[expose] def corankFamily (Ω : Set (Subgroup G)) (j : ℕ) : Set (Subgroup G) :=
  {B | ∃ A ∈ Ω, B ≤ A ∧ Nat.log 2 (B.relIndex A) ≤ j}

/-- The actual W_j(X, Ω) used in E.4.2: generate the corank-family members contained in X. -/
@[expose] def weakSubgroup (Ω : Set (Subgroup G)) (j : ℕ) (X : Subgroup G) : Subgroup G :=
  SubgroupFamily.span (corankFamily Ω j) X

/-- The local condition used in the proofs of E.4.2 and E.4.3: the generalized Fitting subgroup of H/O₂(H) is quasisimple or has prime order. -/
@[expose] def IsLocalOvergroup (H : Subgroup G) : Prop :=
  let Q := H ⧸ pCore 2 H
  IsQuasisimple (generalizedFitting Q) ∨ (Nat.card (generalizedFitting Q)).Prime

/-- The source sum k(Δ), using the intrinsic two-core quotient of each actual overgroup. -/
@[expose] noncomputable def localRankBudget (Δ : Finset (Subgroup G)) : ℕ :=
  ∑ H ∈ Δ, primeRank 2 (H ⧸ pCore 2 H)

/-- A finite family of overgroups of the specified Sylow two-subgroup, generating G and satisfying the source local quotient condition. This does not assert that such a family exists. -/
@[expose] def IsGeneratingFamily (T : Sylow 2 G) (Δ : Finset (Subgroup G)) : Prop :=
  (∀ H ∈ Δ, (T : Subgroup G) ≤ H) ∧ sSup (Δ : Set (Subgroup G)) = ⊤ ∧
    ∀ H ∈ Δ, IsLocalOvergroup H

/-- The fixed-space family is conjugation invariant, through the actual representation operator. -/
theorem fixedSpaceFamily_conjugationInvariant (ρ : Representation (ZMod 2) G V) (k : ℕ) :
    SubgroupFamily.ConjugationInvariant (fixedSpaceFamily ρ k) := by
  intro A hA g
  let E : V ≃ₗ[ZMod 2] V :=
    { ρ g with
      invFun := ρ g⁻¹
      left_inv := fun v => by
        change ρ g⁻¹ (ρ g v) = v
        simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
          map_one, Module.End.one_apply]
      right_inv := fun v => by
        change ρ g (ρ g⁻¹ v) = v
        simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
          map_one, Module.End.one_apply] }
  apply fixedSpaceFamily_map_of_equivariant ρ ρ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective E _ hA
  intro x v
  change ρ g (ρ x v) = ρ (g * x * g⁻¹) (ρ g v)
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel,
    mul_one]

/-- Conjugation preserves the corank family because it preserves relative subgroup indices. -/
theorem corankFamily_conjugationInvariant {Ω : Set (Subgroup G)}
    (hΩ : SubgroupFamily.ConjugationInvariant Ω) (j : ℕ) :
    SubgroupFamily.ConjugationInvariant (corankFamily Ω j) := by
  rintro B ⟨A, hA, hBA, hj⟩ g
  refine ⟨A.map (MulAut.conj g).toMonoidHom, hΩ A hA g, Subgroup.map_mono hBA, ?_⟩
  simpa only [Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) B A (MulAut.conj g).injective] using hj

/-- The normalizer of X normalizes the weak subgroup formed from the fixed-space family. -/
theorem weakSubgroup_normalizer [Finite G]
    (ρ : Representation (ZMod 2) G V) (k j : ℕ) (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (weakSubgroup (fixedSpaceFamily ρ k) j X : Set G) :=
  SubgroupFamily.normalizer_le_span_normalizer
    (corankFamily_conjugationInvariant (fixedSpaceFamily_conjugationInvariant ρ k) j) X

/-- Increasing the permitted corank enlarges the family. -/
theorem corankFamily_mono (Ω : Set (Subgroup G)) {i j : ℕ} (hij : i ≤ j) :
    corankFamily Ω i ⊆ corankFamily Ω j := by
  rintro B ⟨A, hA, hBA, hi⟩
  exact ⟨A, hA, hBA, hi.trans hij⟩

/-- Every generator of W_j(X, Ω) lies in X. -/
theorem weakSubgroup_le (Ω : Set (Subgroup G)) (j : ℕ) (X : Subgroup G) :
    weakSubgroup Ω j X ≤ X := SubgroupFamily.span_le _ _

/-- The weak subgroups increase with j. -/
theorem weakSubgroup_mono (Ω : Set (Subgroup G)) (X : Subgroup G)
    {i j : ℕ} (hij : i ≤ j) : weakSubgroup Ω i X ≤ weakSubgroup Ω j X := by
  apply sSup_le
  intro B hB
  exact SubgroupFamily.le_span (corankFamily_mono Ω hij hB.1) hB.2

/-- In a faithful action, no corank-at-most-k subgroup of an A_(k+1) member is trivial. This is the first paragraph of the E.4.2 proof. -/
theorem corankFamily_ne_bot (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    {j k : ℕ} (hjk : j ≤ k) {B : Subgroup G}
    (hB : B ∈ corankFamily (fixedSpaceFamily ρ (k + 1)) j) : B ≠ ⊥ := by
  obtain ⟨A, hA, hBA, hrank⟩ := hB
  intro hbot
  have hfix := hA.2.2 B hBA (by omega)
  rw [hbot, fixedSpace_bot] at hfix
  exact hA.2.1.1 ((fixedSpace_eq_top_iff ρ hρ A).mp hfix)

/-- A fixed-space-family member contained in X is itself a nontrivial generator of every W_j(X, Ω). -/
theorem weakSubgroup_ne_bot (ρ : Representation (ZMod 2) G V)
    {j k : ℕ} {A X : Subgroup G} (hA : A ∈ fixedSpaceFamily ρ (k + 1)) (hAX : A ≤ X) :
    weakSubgroup (fixedSpaceFamily ρ (k + 1)) j X ≠ ⊥ := by
  have hmem : A ∈ corankFamily (fixedSpaceFamily ρ (k + 1)) j :=
    ⟨A, hA, le_rfl, by simp⟩
  intro hbot
  exact hA.2.1.1 (le_bot_iff.mp (hbot ▸ SubgroupFamily.le_span hmem hAX))

/-- In particular, C_V(T) is contained in each V_j = C_V(W_j(T, Ω)). -/
theorem fixedSpace_le_weakSubgroup_fixedSpace (ρ : Representation (ZMod 2) G V)
    (Ω : Set (Subgroup G)) (j : ℕ) (X : Subgroup G) :
    fixedSpace ρ X ≤ fixedSpace ρ (weakSubgroup Ω j X) :=
  fixedSpace_antitone ρ (weakSubgroup_le Ω j X)

/-- The rank budget increases on subfamilies. -/
theorem localRankBudget_mono {Γ Δ : Finset (Subgroup G)} (h : Γ ⊆ Δ) :
    localRankBudget Γ ≤ localRankBudget Δ :=
  Finset.sum_le_sum_of_subset h

/-- Adjoining a new overgroup adds exactly its quotient two-rank to the budget. -/
theorem localRankBudget_insert [DecidableEq (Subgroup G)]
    (Δ : Finset (Subgroup G)) (H : Subgroup G) (hH : H ∉ Δ) :
    localRankBudget (insert H Δ) = localRankBudget Δ + primeRank 2 (H ⧸ pCore 2 H) := by
  simp only [localRankBudget, Finset.sum_insert hH, Nat.add_comm]

/-- When G = LT, the strict fixed-space hypothesis of E.4.3 implies the noncentralization hypothesis of E.4.2. -/
theorem fixedSpace_sylow_not_le_component (ρ : Representation (ZMod 2) G V)
    {L T : Subgroup G} (hgen : L ⊔ T = ⊤)
    (hfixed : fixedSpace ρ ⊤ < fixedSpace ρ T) :
    ¬ fixedSpace ρ T ≤ fixedSpace ρ L := by
  intro h
  let C := subspaceKernel ρ (fixedSpace ρ T) ⊤
  have hLC : L ≤ C := by
    intro l hl
    exact ⟨mem_top _, fun v hv => h hv ⟨l, hl⟩⟩
  have hTC : T ≤ C := by
    intro t ht
    exact ⟨mem_top _, fun v hv => hv ⟨t, ht⟩⟩
  have htop : (⊤ : Subgroup G) ≤ C := hgen ▸ sup_le hLC hTC
  exact hfixed.not_ge ((le_fixedSpace_subspaceKernel ρ (fixedSpace ρ T) ⊤).trans
    (fixedSpace_antitone ρ htop))
end CFSG.Quasithin.ChapterE.ValueBound
