module
public import Theory.GroupAction.CardFourCubic
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.Sylow

/-!
# Cubic local Transitivity

A Sylow nine acts on the normal fixed four through a cubic group. The centralizer has order twelve, so the cubic action is nontrivial and regular on the three nonidentity elements.
Source: Aschbacher (1994), 45.7(3).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace ElementarySixteenCubic
variable {N:Type*} [Group N] [Finite N]

private theorem cubic_automorphisms_transitive {E:Type*} [Group E] [Finite E]
    (hE:Nat.card E=4) (I:Subgroup (MulAut E)) (hI:Nat.card I=3)
    (x y:E) (hx:x≠1) (hy:y≠1) : ∃a:I,(a:MulAut E) x=y := by
  classical
  let f:I→{v:E//v≠1}:=fun a=>⟨a.val x,fun h=>hx (a.val.injective (h.trans (map_one a.val).symm))⟩
  have hi:Function.Injective f:=by
    intro a b hab
    by_contra hn
    have hc:(b⁻¹*a:I)≠1:=fun h=>hn (inv_mul_eq_one.mp h).symm
    have hcval:((b⁻¹*a:I):MulAut E)≠1:=fun h=>hc (Subtype.ext h)
    have hc3:((b⁻¹*a:I):MulAut E)^3=1:=by
      have hh:(b⁻¹*a:I)^Nat.card I=1:=pow_card_eq_one'
      rw [hI] at hh
      exact congrArg Subtype.val hh
    apply Theory.GroupAction.CardFourCubic.moves_nonidentity hE _ hc3 hcval x hx
    change b.val.symm (a.val x)=x
    rw [show a.val x=b.val x from congrArg Subtype.val hab]
    exact b.val.symm_apply_apply x
  have hc:Nat.card I=Nat.card {v:E//v≠1}:=by
    let : Fintype E:=Fintype.ofFinite E
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_unique]
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hI,hE]
  obtain ⟨a,ha⟩:=((Nat.bijective_iff_injective_and_card f).mpr ⟨hi,hc⟩).surjective ⟨y,hy⟩
  exact ⟨a,congrArg Subtype.val ha⟩

/-- A Sylow nine acts transitively on the nonidentity elements of the normal fixed four. -/
theorem sylow_three_transitive_on_four
    (S:Subgroup N) [S.Normal] [IsElementaryAbelian 2 S]
    (hS:Nat.card S=4) (hN:Nat.card N=72)
    (hC:Nat.card (centralizer (S:Set N))=12) (W:Sylow 3 N) :
    ∀x y:S,x≠1→y≠1→∃w:W,(w:N)*(x:N)*(w:N)⁻¹=y := by
  have hW:Nat.card W=9:=by
    have hfac:Nat.factorization 72 3=2:=by
      have hz:padicValNat 3 8=0:=padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
      rw [Nat.factorization_def 72 Nat.prime_three,
        show (72:ℕ)=3^2*8 by norm_num,
        padicValNat_base_pow_mul (by norm_num) (by norm_num) 2,hz]
    rw [W.card_eq_multiplicity,hN,hfac]
    norm_num
  let α:W→*MulAut S:= (MulAut.conjNormal:N→*MulAut S).comp (W:Subgroup N).subtype
  have hAut:Nat.card (MulAut S)=6:=by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 2 (by simpa using hS)]
    decide
  have hd:Nat.card α.range∣3:=by
    have h1:=α.range.card_subgroup_dvd_card
    rw [hAut] at h1
    have h2:Nat.card α.range∣9:=hW ▸ card_range_dvd α
    exact Nat.dvd_gcd h1 h2
  have hn:Nat.card α.range≠1:=by
    intro h
    have hb:α.range=⊥:=Subgroup.card_eq_one.mp h
    have hle:(W:Subgroup N)≤centralizer (S:Set N):=by
      intro w hw
      apply mem_centralizer_iff.mpr
      intro s hs
      have he:α (⟨w,hw⟩:W)=1:=hb.le ⟨_,rfl⟩
      have hh:=congrArg (fun a:MulAut S=>(a ⟨s,hs⟩:N)) he
      change w*s*w⁻¹=s at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hh:=card_dvd_of_le hle
    rw [hW,hC] at hh
    norm_num at hh
  have hi:Nat.card α.range=3:=((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left hn
  intro x y hx hy
  obtain ⟨a,ha⟩:=cubic_automorphisms_transitive hS α.range hi x y hx hy
  obtain ⟨w,hw⟩:=a.property
  refine ⟨w,?_⟩
  have hh:=congrArg Subtype.val ha
  rw [← hw] at hh
  exact hh
end ElementarySixteenCubic
