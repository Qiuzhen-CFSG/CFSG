module
public import Theory.GroupTheory.ZStar.OddCore
public import Theory.GroupTheory.PPrimeCoreNormalComplement
public import Theory.GroupTheory.ZStar.OddCommutators
public import Theory.GroupAction.Cardinalities

/-!
# Strong induction on proper subgroups in the Z*-argument

The exact induction conclusion gives a normal odd-order subgroup containing
all commutators with the distinguished involution. The strong induction
hypothesis quantifies over smaller finite groups in the same universe, with
the actual involution and odd-commutator assumptions. These exposed predicates
are unfolded by the final strong-induction assembly.

For a proper subgroup containing the involution, injectivity of its subtype
preserves element orders. Apply induction there and absorb the resulting
normal odd subgroup into its odd core. If the subgroup is normal and the
ambient odd core is trivial, its odd core maps into the trivial subgroup;
hence the distinguished involution centralizes it.

This is the proper-subgroup step of Glauberman's Z* minimal-counterexample
argument, ported from the first half of
`c3503435:glauberman_zStar/Submission/ZStar/Induction.lean`.
-/

namespace Glauberman.ZStar

open Subgroup BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G] [Finite G]

/-- The odd-order-commutator form of the Z* conclusion. -/
@[expose] public def OddOrderZStarConclusion
    (G : Type u) [Group G] [Finite G] (t : G) : Prop :=
  ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
    ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N

/-- The strong-induction hypothesis available at a finite group `G`. -/
@[expose] public def OddOrderZStarInductionHypothesis
    (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], Nat.card H < Nat.card G →
    ∀ t : H, IsInvolution t →
      (∀ h : H, Odd (orderOf (h * t * h⁻¹ * t⁻¹))) →
      OddOrderZStarConclusion H t

omit [Finite G] in
/-- A trivial commutator is the same as commuting with `t`. -/
private theorem commute_of_commutator_eq_one {t g : G}
    (h : g * t * g⁻¹ * t⁻¹ = 1) :
    g * t = t * g := by
  calc
    g * t = (g * t * g⁻¹ * t⁻¹) * (t * g) := by group
    _ = t * g := by rw [h, one_mul]

/-- Strong induction gives `t ∈ Z*(H)` for every proper subgroup `H`
containing `t`, expressed in the ambient group. -/
public theorem properSubgroup_commutators_mem_pPrimeCore_of_induction
    {G : Type u} [Group G] [Finite G]
    (hIH : OddOrderZStarInductionHypothesis G)
    (t : G) (htI : IsInvolution t)
    (hodd : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹)))
    (H : Subgroup G) (hHproper : H ≠ ⊤) (htH : t ∈ H) :
    ∀ h : G, h ∈ H →
      h * t * h⁻¹ * t⁻¹ ∈ (pPrimeCore 2 H).map H.subtype := by
  classical
  have hHlt : Nat.card H < Nat.card G := by
    have hlt : H < (⊤ : Subgroup G) := lt_top_iff_ne_top.mpr hHproper
    simpa using natCard_lt_of_subgroup_lt hlt
  let tH : H := ⟨t, htH⟩
  have htHI : IsInvolution tH := by
    constructor
    · intro htHone
      apply htI.1
      exact congrArg Subtype.val htHone
    · apply Subtype.ext
      simpa [tH] using htI.2
  have hoddH : ∀ h : H, Odd (orderOf (h * tH * h⁻¹ * tH⁻¹)) := by
    intro h
    rw [← Subgroup.orderOf_coe (h * tH * h⁻¹ * tH⁻¹)]
    simpa [tH] using hodd (h : G)
  obtain ⟨N, hNnormal, hNodd, hNcomm⟩ :=
    hIH H hHlt tH htHI hoddH
  have hNle : N ≤ pPrimeCore 2 H := by
    exact le_sSup ⟨hNnormal, Nat.coprime_two_left.mpr hNodd⟩
  intro h hh
  let hH : H := ⟨h, hh⟩
  have hmem : hH * tH * hH⁻¹ * tH⁻¹ ∈ pPrimeCore 2 H :=
    hNle (hNcomm hH)
  apply Subgroup.mem_map.mpr
  refine ⟨hH * tH * hH⁻¹ * tH⁻¹, hmem, ?_⟩
  rfl

/-- In a core-free minimal counterexample, `t` centralizes every proper
normal subgroup containing it. -/
public theorem properNormal_central_of_induction
    {G : Type u} [Group G] [Finite G]
    (hIH : OddOrderZStarInductionHypothesis G)
    (hcore : pPrimeCore 2 G = ⊥)
    (t : G) (htI : IsInvolution t)
    (hodd : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹)))
    (N : Subgroup G) (hNnormal : N.Normal) (hNproper : N ≠ ⊤)
    (htN : t ∈ N) :
    ∀ n : G, n ∈ N → n * t = t * n := by
  let : N.Normal := hNnormal
  have hmap_le : (pPrimeCore 2 N).map N.subtype ≤ pPrimeCore 2 G :=
    pPrimeCore_map_subtype_le_pPrimeCore_of_normal (G := G) (p := 2) N
  rw [hcore] at hmap_le
  intro n hn
  have hcommCore :=
    properSubgroup_commutators_mem_pPrimeCore_of_induction
      hIH t htI hodd N hNproper htN n hn
  have hcommBot : n * t * n⁻¹ * t⁻¹ ∈ (⊥ : Subgroup G) :=
    hmap_le hcommCore
  apply commute_of_commutator_eq_one
  exact Subgroup.mem_bot.mp hcommBot

end Glauberman.ZStar

