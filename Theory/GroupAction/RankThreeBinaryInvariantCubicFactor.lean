module
public import Theory.GroupAction.RankThreeBinaryCoatomFixedCard
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
/-!
# Invariant cubic lines are coatom fixed factors

Let elementary binary A of order eight act faithfully on a finite three-group
F, with no whole-A fixed points and with each nonidentity actor fixing at
most nine elements. Every A-invariant subgroup H of order three equals the
fixed subgroup of an index-two subgroup of A.

Restrict the original action to H. Its automorphism group has order two,
so the restricted kernel has index one or two. Index one contradicts whole
fixed freedom. H lies in the kernel fixed subgroup; the preceding coatom
fixed-card theorem makes that subgroup also have order three, giving equality.

This identifies the invariant cubic subgroups in the approved quotient-action
reading of Stellmacher (8.6)(c3) with the fixed factors of (21), printed p.45.
The action is retained literally; no factor transitivity is assumed here.
-/

public theorem rank_three_binary_invariant_cubic_eq_fixed_factor
    {A F : Type*} [Group A] [Finite A] [Group F] [Finite F]
    [IsElementaryAbelian 2 A] [MulDistribMulAction A F] [FaithfulSMul A F]
    (hA : Nat.card A = 8) (hF : IsPGroup 3 F)
    (hfixed : ∀ a : A, a ≠ 1 → Nat.card (FixedPoints.subgroup (Subgroup.zpowers a) F) ≤ 9)
    (hfull : FixedPoints.subgroup (⊤ : Subgroup A) F = ⊥)
    (H : Subgroup F) (hH : IsInvariant A F H) (hcard : Nat.card H = 3) :
    ∃ K : Subgroup A, K.index = 2 ∧ H = FixedPoints.subgroup K F := by
  classical
  let _ := hH
  let _ : IsCyclic H := isCyclic_of_prime_card hcard
  let action : A →* MulAut H := MulDistribMulAction.toMulAut A H
  let K := action.ker
  have hHK : H ≤ FixedPoints.subgroup K F := by
    intro x hx a
    have hh := congrArg (fun f : MulAut H => (f (⟨x,hx⟩:H) : F))
      (MonoidHom.mem_ker.mp a.property)
    exact hh
  have hHne : H ≠ ⊥ := by
    intro hh
    have hc := Subgroup.card_eq_one.mpr hh
    omega
  have hKdiv : K.index ∣ 2 := by
    change action.ker.index ∣ 2
    rw [Subgroup.index_ker]
    have hAut : Nat.card (MulAut H) = 2 := by
      rw [IsCyclic.card_mulAut,hcard,Nat.totient_prime Nat.prime_three]
    exact hAut ▸ Subgroup.card_subgroup_dvd_card action.range
  have hKindex : K.index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hKdiv with hone | htwo
    · have hKtop : K = ⊤ := Subgroup.index_eq_one.mp hone
      rw [hKtop,hfull] at hHK
      exact (hHne (le_bot_iff.mp hHK)).elim
    · exact htwo
  have hCne : FixedPoints.subgroup K F ≠ ⊥ := by
    intro hh
    exact hHne (le_bot_iff.mp (hh ▸ hHK))
  have hCcard := rank_three_binary_coatom_fixed_card hA hF hfixed K hKindex hCne
  exact ⟨K,hKindex,Subgroup.eq_of_le_of_card_ge hHK (by rw [hCcard,hcard])⟩
