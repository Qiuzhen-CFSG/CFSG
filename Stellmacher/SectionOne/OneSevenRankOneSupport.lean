module

public import Stellmacher.SectionOne.OffenderActiveFactorSupport
public import Stellmacher.SectionOne.OneSevenFixedSupportLineControl

/-!
# Selecting the support of a rank-one offender

A nontrivial offender whose full action commutator has order two moves
one of the four-element factor supports in the proved (1.7) decomposition.
The restricted commutator on that support is nontrivial and therefore is
the entire order-two commutator. Invariance of the support places this line
inside it, and the strengthened endpoint retains that containment. Every
actor fixing the line pointwise acts on the selected support modulo the
line. The original selection theorem is preserved as a wrapper dropping
the additional containment field.

This supplies selection, not just control of a preselected factor, for
Stellmacher (9.9)(1), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`. Applying it to the terminal quotient
and lifting the support remain separate geometric and quotient-action steps.
-/

namespace Stellmacher.SectionOne

universe u

/-- Select a rank-one factor support and retain its full commutator line. -/
public theorem oneSeven_support_of_rank_one_offender_with_line
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (sylow : Sylow 2 K) (actor : Subgroup K)
    (hoffender : oneA (V := V) (sylow : Subgroup K) actor)
    (hrank : Nat.card (commutatorAction actor V) = 2) :
    ∃ factor : Subgroup K, IsOneSevenFactor (V := V) factor ∧
      commutatorAction actor V ≤ commutatorAction factor V ∧
      commutatorSubgroup actor V (commutatorAction factor V) =
        commutatorAction actor V ∧
      ∀ mover : K, (∀ point ∈ commutatorAction actor V, mover • point = point) →
        ∀ point ∈ commutatorAction factor V,
          point⁻¹ * (mover • point) ∈ commutatorAction actor V := by
  classical
  have hnontrivial : commutatorAction actor V ≠ ⊥ := by
    intro heq
    have hone := Subgroup.card_eq_one.mpr heq
    omega
  have hactor : actor ≠ ⊥ := by
    intro heq
    apply hnontrivial
    apply le_bot_iff.mp
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨mover, point, _, rfl⟩
    have hmover : (mover : K) = 1 := heq ▸ mover.property
    change point⁻¹ * ((mover : K) • point) ∈ (⊥ : Subgroup V)
    simp [hmover]
  obtain ⟨family, hproduct, hfamily⟩ := oneA_sl2_factors h sylow actor hoffender hactor
  let generated : Subgroup K := ⁅oddCore K, actor⁆ ⊔ actor
  change IsInternalDirectProduct generated family at hproduct
  let indices := {factor : Subgroup K // factor ∈ family}
  let count := Fintype.card indices
  let enumeration : Fin count ≃ indices := (Fintype.equivFin indices).symm
  let factors : Fin count → Subgroup K := fun index => (enumeration index).val
  have hmember (index : Fin count) : factors index ∈ family := (enumeration index).property
  have hinjective : Function.Injective factors := by
    intro first second heq
    exact enumeration.injective (Subtype.ext heq)
  have hgenerate : generated = ⨆ index, factors index := by
    rw [hproduct.1]
    apply le_antisymm
    · apply iSup_le
      intro factor
      obtain ⟨index, rfl⟩ := enumeration.surjective factor
      exact le_iSup factors index
    · exact iSup_le fun index => le_iSup (fun factor : indices => factor.val) (enumeration index)
  have hmodule := oneSevenFactor_module_product h factors
    (fun index => hfamily _ (hmember index)) hinjective generated hgenerate
  have hmoved : ∃ index : Fin count, ∃ mover : actor,
      ∃ point ∈ commutatorAction (factors index) V, mover • point ≠ point := by
    by_contra hnone
    push Not at hnone
    have hfixed : (⊤ : Subgroup V) ≤ FixedPoints.subgroup actor V := by
      rw [hmodule.1, iSup_option]
      apply sup_le
      · intro point hpoint
        rw [FixedPoints.mem_subgroup] at hpoint ⊢
        exact fun mover => hpoint ⟨mover, (show actor ≤ generated from le_sup_right) mover.property⟩
      · exact iSup_le fun index point hpoint =>
          (FixedPoints.mem_subgroup _ _ _).mpr fun mover => hnone index mover point hpoint
    apply hnontrivial
    apply le_bot_iff.mp
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨mover, point, _, rfl⟩
    have hpoint := (FixedPoints.mem_subgroup _ _ _).mp (hfixed (Subgroup.mem_top point)) mover
    change point⁻¹ * (mover • point) = 1
    rw [hpoint, inv_mul_cancel]
  obtain ⟨index, mover, point, hpoint, hmove⟩ := hmoved
  let support := commutatorAction (factors index) V
  let restricted := commutatorSubgroup actor V support
  have hrestricted : restricted ≤ commutatorAction actor V := by
    apply Subgroup.closure_mono
    rintro _ ⟨mover, point, _, rfl⟩
    exact ⟨mover, point, Subgroup.mem_top point, rfl⟩
  have hrestricted_ne : restricted ≠ ⊥ := by
    intro heq
    have hmem : point⁻¹ * (mover • point) ∈ restricted :=
      Subgroup.subset_closure ⟨mover, point, hpoint, rfl⟩
    rw [heq] at hmem
    exact hmove (inv_mul_eq_one.mp hmem).symm
  have hrestricted_card := (Subgroup.one_lt_card_iff_ne_bot restricted).mpr hrestricted_ne
  have hequal : restricted = commutatorAction actor V :=
    Subgroup.eq_of_le_of_card_ge hrestricted (by omega)
  have hnormalize : actor ≤ Subgroup.normalizer (factors index : Set K) := by
    have hle : factors index ≤ generated := by rw [hgenerate]; exact le_iSup factors index
    exact (show actor ≤ generated from le_sup_right).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp (hproduct.2.1 _ (hmember index)))
  have hinvariant : IsInvariant actor V support :=
    commutatorAction_isInvariant_of_normalizing_actor actor (factors index) hnormalize
  have hline : commutatorAction actor V ≤ support := by
    rw [← hequal]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨mover, point, hpoint, rfl⟩
    exact support.mul_mem (support.inv_mem hpoint) ((hinvariant.invariant mover point).mp hpoint)
  refine ⟨factors index, hfamily _ (hmember index), hline, hequal, ?_⟩
  exact fun mover hfix => oneSevenFactor_fixed_line_control h (factors index)
    (hfamily _ (hmember index)) (commutatorAction actor V) hline hrank mover hfix

/-- The original support-selection interface, preserving the control conclusions. -/
public theorem oneSeven_support_of_rank_one_offender
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (sylow : Sylow 2 K) (actor : Subgroup K)
    (hoffender : oneA (V := V) (sylow : Subgroup K) actor)
    (hrank : Nat.card (commutatorAction actor V) = 2) :
    ∃ factor : Subgroup K, IsOneSevenFactor (V := V) factor ∧
      commutatorSubgroup actor V (commutatorAction factor V) =
        commutatorAction actor V ∧
      ∀ mover : K, (∀ point ∈ commutatorAction actor V, mover • point = point) →
        ∀ point ∈ commutatorAction factor V,
          point⁻¹ * (mover • point) ∈ commutatorAction actor V := by
  obtain ⟨factor, hfactor, _, hrestricted, hcontrol⟩ :=
    oneSeven_support_of_rank_one_offender_with_line h sylow actor hoffender hrank
  exact ⟨factor, hfactor, hrestricted, hcontrol⟩

end Stellmacher.SectionOne
