module
public import Theory.SpecificGroups.ReeTwo.CoreParabolicOrbits
public import Theory.SpecificGroups.ReeTwo.FixingActionCensus
public import Theory.SpecificGroups.ReeTwo.InvertingActionCensus

/-!
# The unrestricted squaring-action census on the Ree core

An automorphism squaring the native five-action sends the middle root to
an element of the same order in its cyclic-four fixed group. It therefore
fixes or inverts that root. The two previously verified twenty-element
censuses exhaust all possibilities and make the fourth-power relation a
conclusion. This is the action input for recognizing actual cyclic-four
extensions of the core.

Source: Shinoda (1975), (2.3), with the explicit root and action certificates
in `CoreParabolicOrbits`, `FixingActionCensus`, and `InvertingActionCensus`.
-/

public section
namespace ReeTwo.Core

private theorem fixed_pow {H:Type*} [Group H] (δ:MulAut H) (x:H)
    (hx:δ x=x) (n:ℕ) : (δ^n) x=x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ,MulAut.mul_apply,hx,ih]

private theorem fixed_of_square_five {H:Type*} [Group H] (δ:MulAut H) (x:H)
    (hδ:δ^5=1) (hx:(δ^2) x=x) : δ x=x := by
  have hf:=fixed_pow (δ^2) x hx 3
  have hp:(δ^2)^3=δ:=by
    rw [←pow_mul,show 2*3=5+1 from rfl,pow_add,hδ,pow_one,_root_.one_mul]
  rwa [hp] at hf

private theorem four_generator_orientation {H:Type*} [Group H] (t x:H)
    (ht:orderOf t=4) (hx:orderOf x=4) (hm:x∈Subgroup.zpowers t) :
    x=t ∨ x=t⁻¹ := by
  classical
  have ht4:t^4=1:=by simpa only [ht] using pow_orderOf_eq_one t
  rw [(orderOf_pos_iff.mp (by rw [ht];decide)).mem_zpowers_iff_mem_range_orderOf,
    ht] at hm
  obtain ⟨n,hn,he⟩:=Finset.mem_image.mp hm
  have hn4:=Finset.mem_range.mp hn
  interval_cases n
  · have hz:x=1:=by simpa only [pow_zero] using he.symm
    rw [hz,orderOf_one] at hx
    norm_num at hx
  · exact Or.inl (by simpa only [pow_one] using he.symm)
  · have hh:x^2=1:=by
      rw [←he,←pow_mul]
      exact ht4
    have hd:=orderOf_dvd_of_pow_eq_one hh
    rw [hx] at hd
    norm_num at hd
  · right
    rw [←he]
    apply eq_inv_iff_mul_eq_one.mpr
    rw [←pow_succ]
    exact ht4

/-- Squaring the five-action forces the middle root to be fixed or inverted. -/
theorem squaring_action_root_two (β:MulAut Core) (hc:β*c*β⁻¹=c^2) :
    β (root 2)=root 2 ∨ β (root 2)=(root 2)⁻¹ := by
  have ht:c (root 2)=root 2:=by decide +kernel
  have hf:(c^2) (β (root 2))=β (root 2):=by
    simpa only [ht] using (InvertingActionCensus.squaring_apply β c hc (root 2)).symm
  apply four_generator_orientation _ _ root_two_order ((β.orderOf_eq _).trans root_two_order)
  exact (fixed_c_iff_mem_zpowers _).mp (fixed_of_square_five c _ c_five hf)

/-- The complete squaring census has two orientations and twenty representatives
in each orientation, without an assumed fourth-power relation. -/
theorem squaring_action_census (β:MulAut Core) (hc:β*c*β⁻¹=c^2) :
    (∃i:Fin 20,β=FixingActionCensus.representative i) ∨
    (∃i:Fin 20,β=InvertingActionCensus.representative i) := by
  rcases squaring_action_root_two β hc with hpos | hneg
  · exact Or.inl (FixingActionCensus.exhaustive_of_conj_c_root_two β hc hpos)
  · exact Or.inr (InvertingActionCensus.exhaustive_of_conj_c_root_two β hc hneg)

/-- Every automorphism squaring the native five-action has fourth power one. -/
theorem squaring_action_four (β:MulAut Core) (hc:β*c*β⁻¹=c^2) : β^4=1 := by
  rcases squaring_action_census β hc with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · exact FixingActionCensus.representative_four i
  · exact InvertingActionCensus.representative_four i

end ReeTwo.Core
