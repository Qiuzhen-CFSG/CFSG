module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SmallMGenericity
public import Stellmacher.SectionOne.ExceptionalMinimalKernel
public import Theory.Representation.NormalizedCThreeKernel
public import Theory.GroupAction.FixedQuotientCommutator

/-!
# Full-module action data in the bounded exceptional case

For an elementary abelian actor with minimal action ratio and a failed
local factor, an explicit bound `m(S)≤2` forces `m(S)=2`. The failed factor
has a sixteen-element commutator space. The normalized-three action theorem
gives a four-element image and two common fixed points; minimality eliminates
the kernel and forces `|S|=4`. The resulting cardinal equality gives
`V=[V,F] C_V(S)` and puts the full `S`-commutator inside `[V,F]`.

The stronger endpoint also retains normalization of the selected factor by
`C_W(S)`, proved directly from its local coordinate commutator identity.
The original action-data endpoint remains as a signature-preserving wrapper.

This is the valid action-theoretic part of Stellmacher (1.6), journal p.18,
with the explicit numerical bound needed to justify full-module containment.
It does not assert the unrestricted source claim, nor assume the later
classification of the odd core. Source: `refs/latex/stellmacher-n-group.tex`.
-/

open scoped IsMulCommutative commutatorElement

namespace Stellmacher.SectionOne

open RankOneThreeGroupAssembly

universe u

public theorem exists_exceptional_small_m_normalized_action_data
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hnongeneric : ¬ RankOneAssemblyGenericHypothesis (G := G) (V := V) S)
    (hmin : ∀ K : Subgroup G, K ≤ S → K ≠ ⊥ →
      m (G := G) (V := V) S ≤ m (G := G) (V := V) K)
    (hm : m (G := G) (V := V) S ≤ 2) :
    m (G := G) (V := V) S = 2 ∧ Nat.card S = 4 ∧
      ∃ F : Subgroup G, F ≤ oddCore G ∧ Nat.card F = 3 ∧
        S ⊔ (oddCore G ⊓ Subgroup.centralizer (S : Set G)) ≤ Subgroup.normalizer (F : Set G) ∧
        Nat.card (commutatorAction F V) = 16 ∧
        S ⊓ fixingSubgroup G (commutatorAction F V : Set V) = ⊥ ∧
        Nat.card (commutatorAction F V ⊓ FixedPoints.subgroup S V : Subgroup V) = 2 ∧
        commutatorAction F V ⊔ FixedPoints.subgroup S V = ⊤ ∧
        commutatorAction S V ≤ commutatorAction F V := by
  have hmEq : m (G := G) (V := V) S = 2 := by
    apply le_antisymm hm
    exact le_of_not_gt (fun hlt => hnongeneric (generic_of_m_lt_two S hS hlt))
  obtain ⟨A, F, hAmax, hAcard, hFWA, hFcard, hcoord, _, hfixedA, hUcard⟩ :=
    exists_exceptional_local_factor_fixed_card_data S hS hnongeneric
  have hFnorm := hcoord.normalized S A F hS
  have hCnorm : oddCore G ⊓ Subgroup.centralizer (S : Set G) ≤
      Subgroup.normalizer (F : Set G) := by
    obtain ⟨I, _, hIS, _, heq, _⟩ := hcoord
    let WA := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    have hCWA : oddCore G ⊓ Subgroup.centralizer (S : Set G) ≤
        oddCore G ⊓ Subgroup.centralizer (A : Set G) :=
      inf_le_inf le_rfl (Subgroup.centralizer_le hAmax.1)
    have hCWAnorm := hCWA.trans (Subgroup.normalizer_commutator_ge_left
      (oddCore G ⊓ Subgroup.centralizer (A : Set G)) S)
    have hCInorm : oddCore G ⊓ Subgroup.centralizer (S : Set G) ≤
        Subgroup.normalizer (I : Set G) :=
      (inf_le_right.trans (Subgroup.centralizer_le hIS)).trans
        (Subgroup.centralizer_le_normalizer (I : Set G))
    rw [← heq, Subgroup.commutator_def]
    apply Subgroup.le_normalizer_closure_iff.mpr
    rintro c hc _ ⟨w, hw, i, hi, rfl⟩
    have hw' : c * w * c⁻¹ ∈ WA :=
      (Subgroup.mem_normalizer_iff.mp (hCWAnorm hc) w).mp hw
    have hi' : c * i * c⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp (hCInorm hc) i).mp hi
    have hc' := Subgroup.commutator_mem_commutator hw' hi'
    change c * ⁅w, i⁆ * c⁻¹ ∈ ⁅WA, I⁆
    simpa only [← MulAut.conj_apply, ← map_commutatorElement] using hc'
  obtain ⟨I, hAI, hIS, hIcard, _, hfull⟩ := hcoord
  have hFA : ⁅F, A⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hFWA.trans (local_commutator_le_centralizer S A hS hAmax.1))
  obtain ⟨_, hfixedS, hindex⟩ :=
    Representation.normalizedCThree_cardSixteen_kernel_data F A I S hS hAI hIS
      hFnorm hFcard hAcard hIcard hFA (fun b hb hn => (hfull b hb hn).1)
      hUcard hfixedA
  obtain ⟨hkernel, hScard⟩ := exceptional_minimal_m_kernel_eq_bot S
    (commutatorAction F V) hmin hUcard hfixedS hindex
  let _ : IsInvariant S V (commutatorAction F V) :=
    _root_.commutatorAction_isInvariant_of_normalizing_actor S F hFnorm
  have hprod : Nat.card (commutatorAction F V) * Nat.card (FixedPoints.subgroup S V) =
      Nat.card V * Nat.card (commutatorAction F V ⊓ FixedPoints.subgroup S V : Subgroup V) := by
    have hCpos : (0 : ℚ) < Nat.card (FixedPoints.subgroup S V) := by
      exact_mod_cast Nat.card_pos (α := FixedPoints.subgroup S V)
    unfold m at hmEq
    rw [hScard] at hmEq
    have hc := (div_eq_iff (ne_of_gt (mul_pos hCpos (by norm_num : (0 : ℚ) < 4)))).mp hmEq
    have hnat : Nat.card V = 8 * Nat.card (FixedPoints.subgroup S V) := by
      exact_mod_cast (show (Nat.card V : ℚ) = 8 * Nat.card (FixedPoints.subgroup S V) by nlinarith [hc])
    rw [hUcard, hfixedS, hnat]
    norm_num
    omega
  obtain ⟨hcover, hcomm⟩ := commutatorAction_le_of_fixed_card_product_eq
    (A := S) (commutatorAction F V) hprod
  exact ⟨hmEq, hScard, F, hFWA.trans (local_commutator_le_oddCore S A), hFcard,
    sup_le hFnorm hCnorm, hUcard, hkernel, hfixedS, hcover, hcomm⟩

/-- Compatibility endpoint retaining only normalization by the Sylow subgroup. -/
public theorem exists_exceptional_small_m_action_data
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hnongeneric : ¬ RankOneAssemblyGenericHypothesis (G := G) (V := V) S)
    (hmin : ∀ K : Subgroup G, K ≤ S → K ≠ ⊥ →
      m (G := G) (V := V) S ≤ m (G := G) (V := V) K)
    (hm : m (G := G) (V := V) S ≤ 2) :
    m (G := G) (V := V) S = 2 ∧ Nat.card S = 4 ∧
      ∃ F : Subgroup G, F ≤ oddCore G ∧ Nat.card F = 3 ∧
        S ≤ Subgroup.normalizer (F : Set G) ∧
        Nat.card (commutatorAction F V) = 16 ∧
        S ⊓ fixingSubgroup G (commutatorAction F V : Set V) = ⊥ ∧
        Nat.card (commutatorAction F V ⊓ FixedPoints.subgroup S V : Subgroup V) = 2 ∧
        commutatorAction F V ⊔ FixedPoints.subgroup S V = ⊤ ∧
        commutatorAction S V ≤ commutatorAction F V := by
  obtain ⟨hmEq, hScard, F, hFW, hFcard, hnorm, hUcard, hker, hfix, hcover, hcomm⟩ :=
    exists_exceptional_small_m_normalized_action_data S hS hnongeneric hmin hm
  exact ⟨hmEq, hScard, F, hFW, hFcard, le_sup_left.trans hnorm,
    hUcard, hker, hfix, hcover, hcomm⟩

end Stellmacher.SectionOne
