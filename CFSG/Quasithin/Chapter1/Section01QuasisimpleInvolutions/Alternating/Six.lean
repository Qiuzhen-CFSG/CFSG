module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Alternating.Comparisons
public import Theory.SpecificGroups.AlternatingSix.SylowFixedAction
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed

/-!
# The marked A₆ action and its simple/triple alternatives

A Sylow-fixing involution of Aut(A₆) belongs to the natural S₆. An outer
one is induced by a transposition or three transpositions. In the latter
case a permutation conjugacy followed by the exceptional automorphism
changes the quotient model and intertwines the original action with a
transposition. Inner actions retain the characteristic-two Lie alternative.

The only extra premise in the classification theorem below is oddness of
the center. The independent even-cover exclusion must discharge it before
this is a complete source case.
Source: Aschbacher--Smith, proof of 1.1.5(3), printed p.502;
GLS, Volume 3, Proposition 5.2.7.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions.Alternating
open Theory.GroupTheory Chapter15.Section03.Candidates.ComponentStructure

open Subgroup Equiv Equiv.Perm GLS3.Chapter5
open AlternatingSix.ShadowLocal

private theorem outer_intertwines (σ : Perm (Fin 6)) (g : A6) :
    outerAltAut (permutationAction σ g) =
      permutationAction (outerHom σ) (outerAltAut g) := by
  apply Subtype.ext
  change outerHom (σ * g.val * σ⁻¹) = outerHom σ * outerHom g.val * (outerHom σ)⁻¹
  simp only [map_mul, map_inv]

private theorem normal_form (P : Sylow 2 A6) (β : AutA6) (hβ : orderOf β = 2)
    (hfix : ∀ x ∈ (P : Subgroup A6), β x = x) (hi : β ∉ AlternatingSix.ShadowLocal.inner) :
    ∃ (δ : MulAut A6) (σ : Perm (Fin 6)), σ.IsSwap ∧
      ∀ x, δ (β x) = permutationAction σ (δ x) := by
  obtain ⟨σ, hσ⟩ := involution_mem_natural_of_fixes_sylow P β hβ hfix
  change permutationAction σ = β at hσ
  have ho : orderOf σ = 2 :=
    (orderOf_injective permutationAction permutationAction_injective σ).symm.trans (hσ ▸ hβ)
  have hodd : σ ∉ alternatingGroup (Fin 6) := by
    intro heven
    apply hi
    exact ⟨⟨σ, heven⟩, (permutationAction_coe ⟨σ, heven⟩).symm.trans hσ⟩
  rcases odd_involution_cycleType σ ho hodd with hs | ht
  · refine ⟨1, σ, hs, ?_⟩
    intro x
    change β x = permutationAction σ x
    rw [hσ]
  · have hc : IsConj σ (outerHom (swap (4 : Fin 6) 5)) :=
      isConj_of_cycleType_eq (ht.trans outerHom_standardSwap_cycleType.symm)
    obtain ⟨p, hp⟩ := isConj_iff.mp hc
    refine ⟨(permutationAction p).trans outerAltAut.symm, swap 4 5,
      swap_isSwap_iff.mpr (by decide), ?_⟩
    intro x
    apply outerAltAut.injective
    change outerAltAut (outerAltAut.symm (permutationAction p (β x))) =
      outerAltAut (permutationAction (swap 4 5)
        (outerAltAut.symm (permutationAction p x)))
    rw [MulEquiv.apply_symm_apply, outer_intertwines, MulEquiv.apply_symm_apply]
    have he : permutationAction p * β =
        permutationAction (outerHom (swap 4 5)) * permutationAction p := by
      rw [← hσ, ← map_mul, ← map_mul]
      exact congrArg permutationAction (mul_inv_eq_iff_eq_mul.mp hp)
    exact congrArg (fun a : AutA6 => a x) he


variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    {α : MulAut L} {P : Sylow 2 L}

/-- The original action is inner, or an actual changed A₆ quotient model
intertwines it with a transposition. No condition on the center is used. -/
theorem six_inner_or_transposition (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* alternatingGroup (Fin 6)) :
    (α ∈ (MulAut.conj (G := L)).range ∧ center L = pCore 2 L) ∨
      ∃ (e' : L ⧸ center L ≃* alternatingGroup (Fin 6))
        (σ : Perm (Fin 6)), σ.IsSwap ∧ ∀ x : L,
        (e' (QuotientGroup.mk' (center L) (α x)) : Perm (Fin 6)) =
          σ * e' (QuotientGroup.mk' (center L) x) * σ⁻¹ := by
  obtain ⟨ho, _, Q, hQ⟩ := d.centralQuotient_model_inputs e
  by_cases hi : MulAut.centralQuotientAction e α ∈ AlternatingSix.ShadowLocal.inner
  · exact Or.inl (d.inner_and_center_of_quotient_inner e hi)
  · obtain ⟨δ, σ, hs, hδ⟩ := normal_form Q _ ho hQ hi
    refine Or.inr ⟨e.trans δ, σ, hs, ?_⟩
    intro x
    have h := hδ (e (QuotientGroup.mk' (center L) x))
    rw [MulAut.centralQuotientAction_apply] at h
    exact congrArg Subtype.val h

/-- The complete canonical A₆ conclusion once the independent cover
obstruction has established that the center is odd. -/
theorem six_of_odd_center (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* alternatingGroup (Fin 6))
    (hodd : Odd (Nat.card (center L))) : ModelAction115 L α := by
  rcases six_inner_or_transposition d e with ⟨hi, hz⟩ | ⟨e', σ, hs, ha⟩
  · obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
    have hc : Nat.card (center L) = 1 := Nat.eq_one_of_dvd_coprimes
      (hodd.coprime_two_right.pow_right k) dvd_rfl (by rw [hz, hk])
    let eL := (quotientEquivOfCenterBot (Subgroup.card_eq_one.mp hc)).trans e
    let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
    exact .lie eL.isSimpleGroup (lie_model_of_equiv_six eL) hi
  · exact .six σ hs (action_of_odd_center e' (Or.inl rfl) hodd σ ha)

/-- The full A₆ contract for an actual simple-group model, with no extra
center or action premise. -/
theorem six_of_equiv (d : MarkedInvolution α P)
    (e : L ≃* alternatingGroup (Fin 6)) : ModelAction115 L α := by
  have hc : Nat.card (center L) = 1 := by
    rw [Nat.card_congr (centerCongr e).toEquiv,
      alternatingGroup.center_eq_bot (by simp), Subgroup.card_bot]
  let q := quotientEquivOfCenterBot (Subgroup.card_eq_one.mp hc)
  exact six_of_odd_center d (q.symm.trans e) (by rw [hc]; decide)

/-- Application to the genuine commutator of PSp₄(2), with its original
marked automorphism and the cover obstruction still explicit. -/
theorem projective_derived_of_odd_center (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))
    (hodd : Odd (Nat.card (center L))) : ModelAction115 L α :=
  six_of_odd_center d (equiv_six_of_projective_derived e) hodd

/-- Application to any genuine PSL₂(9) quotient model. -/
theorem psl_nine_of_odd_center (d : MarkedInvolution α P)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 9)
    (hodd : Odd (Nat.card (center L))) : ModelAction115 L α := by
  obtain ⟨e⟩ := equiv_six_of_psl_nine h
  exact six_of_odd_center d e hodd

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions.Alternating
