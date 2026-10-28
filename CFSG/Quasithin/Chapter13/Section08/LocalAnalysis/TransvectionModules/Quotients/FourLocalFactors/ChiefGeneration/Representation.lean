module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Models
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Four-dimensional generation from two noncentral chief factors

A noncentral binary factor has dimension at least two, since every action on
at most one binary dimension is trivial. Summing the dimensions of all steps
of the complete invariant chief series shows that two noncentral factors
exhaust dimension four: there are no central factors left. The difference
space is invariant. Intersecting it with each successive chief term and using
the covering property propagates generation through the series. This uses no
splitting or semisimplicity assumption.

The chief-series interface is the literal `TwoNoncentralChiefFactors` used
in the chapter. Source application: Aschbacher–Smith, combined manuscript
(1 March 2004), proof of 13.7.6(3a), printed p.939 (PDF p.956), and
13.8.6(4), printed p.948 (PDF p.965).
-/

public section

open Module Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.ChiefGeneration
variable {J E : Type*} [Group J] [AddCommGroup E] [Module (ZMod 2) E]

private theorem fixed_of_finrank_le_one (σ : Representation (ZMod 2) J E)
    [FiniteDimensional (ZMod 2) E] (hd : finrank (ZMod 2) E ≤ 1) (g : J) (v : E) :
    σ g v = v := by
  rcases Nat.eq_zero_or_pos (finrank (ZMod 2) E) with hz | hp
  · let : Subsingleton E := (Module.finrank_zero_iff.mp hz)
    exact Subsingleton.elim _ _
  · obtain ⟨c, hc, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
      (by omega : finrank (ZMod 2) E = 1) (σ g)
    fin_cases c
    · change σ g = (0 : ZMod 2) • LinearMap.id at hc
      have hz : σ g v = 0 := by rw [hc, zero_smul]; rfl
      have hv := congrArg (σ g⁻¹) hz
      rw [hz]
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply, map_zero] using hv.symm
    · change σ g = (1 : ZMod 2) • LinearMap.id at hc
      rw [hc, one_smul]; rfl

private theorem noncentral_step_dimension (σ : Representation (ZMod 2) J E)
    [FiniteDimensional (ZMod 2) E] {A B : Subrepresentation σ} (hAB : A ≤ B)
    (hn : ∃ g : J, ∃ v, sectionRepresentation σ A B g v ≠ v) :
    finrank (ZMod 2) A.toSubmodule + 2 ≤ finrank (ZMod 2) B.toSubmodule := by
  have hd := (sectionLower σ A B).toSubmodule.finrank_quotient_add_finrank
  have he := (sectionLowerEquiv σ hAB).finrank_eq
  have hq : 2 ≤ finrank (ZMod 2) (B.toSubmodule ⧸ (sectionLower σ A B).toSubmodule) := by
    by_contra! hh
    obtain ⟨g, v, hv⟩ := hn
    exact hv (fixed_of_finrank_le_one (sectionRepresentation σ A B) (by omega) g v)
  omega

private def differenceSubrepresentation (σ : Representation (ZMod 2) J E) :
    Subrepresentation σ where
  toSubmodule := Coinvariants.ker σ
  apply_mem_toSubmodule g := by
    intro x hx
    simpa only [sub_add_cancel] using
      (Coinvariants.ker σ).add_mem (Coinvariants.sub_mem_ker g x) hx

private theorem cover_le_difference (σ : Representation (ZMod 2) J E)
    {A B : Subrepresentation σ} (hAB : A ⋖ B)
    (hA : A ≤ differenceSubrepresentation σ)
    (hn : ∃ g : J, ∃ v, sectionRepresentation σ A B g v ≠ v) :
    B ≤ differenceSubrepresentation σ := by
  rcases hAB.eq_or_eq (le_inf hAB.le hA) inf_le_left with h | h
  · obtain ⟨g, v, hv⟩ := hn
    apply False.elim (hv _)
    apply (sectionRepresentation_trivial_iff σ A B g).mpr _ v
    intro w hw
    have hm : σ g w - w ∈ (B ⊓ differenceSubrepresentation σ).toSubmodule :=
      ⟨B.toSubmodule.sub_mem (B.apply_mem_toSubmodule g hw) hw,
        Coinvariants.sub_mem_ker g w⟩
    simpa only [h] using hm
  · rw [← h]
    exact inf_le_right

/-- The two noncentral factors exhaust dimension four, and generation lifts
through the complete chief series. -/
theorem ker_eq_top_of_two_noncentral (σ : Representation (ZMod 2) J E)
    [FiniteDimensional (ZMod 2) E] (hd : finrank (ZMod 2) E = 4)
    (hc : TwoNoncentralChiefFactors σ) : Coinvariants.ker σ = ⊤ := by
  classical
  obtain ⟨n, chain, h0, ht, hcov, hcount⟩ := hc
  let p : Fin n → Prop := fun i => ∃ g : J, ∃ v,
    sectionRepresentation σ (chain i.castSucc) (chain i.succ) g v ≠ v
  let d : Fin (n + 1) → ℕ := fun i => finrank (ZMod 2) (chain i).toSubmodule
  have hstep (i : Fin n) : d i.castSucc + 1 + (if p i then 1 else 0) ≤ d i.succ := by
    by_cases hp : p i
    · simpa only [if_pos hp, Nat.add_assoc] using
        noncentral_step_dimension σ (hcov i).le hp
    · simp only [if_neg hp, add_zero]
      apply Submodule.finrank_lt_finrank_of_lt
      exact ⟨(hcov i).le, fun h => (hcov i).lt.not_ge h⟩
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hstep i)
  have hc' : (∑ i : Fin n, if p i then 1 else 0) = 2 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter] using hcount
  have hzero : d 0 = 0 := by
    dsimp only [d]
    rw [h0]
    exact finrank_bot _ _
  have htop : d (Fin.last n) = 4 := by
    dsimp only [d]
    rw [ht]
    exact (finrank_top (ZMod 2) E).trans hd
  have hcast := Fin.sum_univ_castSucc d
  have hsucc := Fin.sum_univ_succ d
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one, hc'] at hsum
  have hn : n ≤ 2 := by omega
  have hcn : (Finset.univ.filter p).card = 2 := by
    simpa only [Finset.card_filter] using hc'
  have hfull : Finset.univ.filter p = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    simpa only [Finset.card_univ, Fintype.card_fin, hcn] using hn
  have hp (i : Fin n) : p i := by
    have : i ∈ Finset.univ.filter p := hfull.symm ▸ Finset.mem_univ i
    exact (Finset.mem_filter.mp this).2
  have hle (i : Fin (n + 1)) : chain i ≤ differenceSubrepresentation σ := by
    induction i using Fin.induction with
    | zero => rw [h0]; exact bot_le
    | succ i ih => exact cover_le_difference σ (hcov i) ih (hp i)
  have h := hle (Fin.last n)
  rw [ht] at h
  exact top_unique h
end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.ChiefGeneration

end
