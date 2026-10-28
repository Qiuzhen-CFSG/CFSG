module
public import Theory.Alternating.Aut
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Detecting inner actors on a perfect double cover of A₅

The central quotient embeds the automorphism group of a perfect cover in
S₅. A subgroup containing all inner automorphisms is therefore either
inner or surjects onto S₅. The latter contains an actor squaring any given
five-cycle. Since the covering center has order two, that equality lifts
uniquely to elements of order five in the cover.

The primary Frattini plane in the nilpotent-Fitting A.3.6 row rules out
such squaring. Its literal Cartan application is in
CartanCore.Actions.FieldDetection.OddLinear.Sieve.NilpotentFive.
Source: Aschbacher--Smith A.3.6 and 11.5.6(3), pp.43--45,780--781.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.Alternating.FiveCoverInnerActors
private def symAut : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))

private theorem five_cycle_isConj_square (x : Equiv.Perm (Fin 5))
    (hx : orderOf x = 5) : IsConj x (x ^ 2) := by
  have hxp : orderOf (x ^ 2) = 5 := by
    rw [orderOf_pow', hx]
    · decide
    · decide
  have hc := Equiv.Perm.isCycle_of_prime_order'' (σ := x) (by decide)
    (by simpa only [Fintype.card_fin] using hx)
  have hc2 := Equiv.Perm.isCycle_of_prime_order'' (σ := x ^ 2) (by decide)
    (by simpa only [Fintype.card_fin] using hxp)
  apply Equiv.Perm.isConj_of_cycleType_eq
  rw [hc.cycleType, hc2.cycleType, ←hc.orderOf, ←hc2.orderOf, hx, hxp]

/-- A single five-element detects every outer actor above the inner subgroup. -/
theorem inner_of_no_five_squaring {R : Type*} [Group R] [Finite R] [Group.IsPerfect R]
    (e : R ⧸ center R ≃* alternatingGroup (Fin 5))
    (hz : Nat.card (center R) = 2) (H : Subgroup (MulAut R))
    (hH : MulAut.innerSubgroup R ≤ H) (g : R) (hg : orderOf g = 5)
    (hn : ∀ a ∈ H, a g ≠ g ^ 2) : H ≤ MulAut.innerSubgroup R := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center R))
  let f := symAut.symm.toMonoidHom.comp (MulAut.centralQuotientAction e)
  have hfconj (r : R) : f (MulAut.conj r) = (q r).val := by
    apply symAut.injective
    change symAut (symAut.symm _) = _
    rw [symAut.apply_symm_apply, MulAut.centralQuotientAction_conj]
    ext x
    rfl
  have hsurjq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have heven (s : Equiv.Perm (Fin 5)) (hs : s ∈ alternatingGroup (Fin 5)) :
      ∃ a ∈ H, f a = s := by
    obtain ⟨r,hr⟩ := hsurjq ⟨s,hs⟩
    exact ⟨MulAut.conj r,hH ⟨r,rfl⟩,(hfconj r).trans (congrArg Subtype.val hr)⟩
  intro a ha
  by_contra hout
  have hodd : f a ∉ alternatingGroup (Fin 5) := by
    intro hs
    let y : alternatingGroup (Fin 5) := ⟨f a,hs⟩
    have hi : MulAut.centralQuotientAction e a = MulAut.conj y := by
      have heq := symAut.apply_symm_apply (MulAut.centralQuotientAction e a)
      calc
        _ = symAut (f a) := heq.symm
        _ = _ := by ext x; rfl
    obtain ⟨r,hr⟩ := (MulAut.centralQuotientAction_inner_iff e a).mp ⟨y,hi⟩
    exact hout ⟨r,hr.symm⟩
  have hfull (s : Equiv.Perm (Fin 5)) : ∃ b ∈ H, f b = s := by
    by_cases hs : s ∈ alternatingGroup (Fin 5)
    · exact heven s hs
    · have hp : s * (f a)⁻¹ ∈ alternatingGroup (Fin 5) := by
        rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two, inv_mem_iff]
        exact iff_of_false hs hodd
      obtain ⟨b,hb,he⟩ := heven _ hp
      exact ⟨b*a,H.mul_mem hb ha,by rw [map_mul,he,inv_mul_cancel_right]⟩
  have hqg : orderOf (q g) = 5 := by
    have hd : orderOf (q g) ∣ 5 := by simpa only [hg] using orderOf_map_dvd q g
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h1 | h5
    · have hone : q g = 1 := orderOf_eq_one_iff.mp h1
      have hzg : g ∈ center R := by
        apply (QuotientGroup.eq_one_iff _).mp
        exact e.injective (hone.trans e.map_one.symm)
      have hc := (center R).orderOf_dvd_natCard hzg
      rw [hz,hg] at hc
      norm_num at hc
    · exact h5
  have ho : orderOf ((q g).val) = 5 := (Subgroup.orderOf_coe (q g)).trans hqg
  obtain ⟨s,hs⟩ := isConj_iff.mp (five_cycle_isConj_square (q g).val ho)
  obtain ⟨b,hb,hfb⟩ := hfull s
  have hpoint : (f b) * (q g).val * (f b)⁻¹ = (q (b g)).val := by
    have h := congrArg (fun z : MulAut (alternatingGroup (Fin 5)) => (z (q g)).val)
      (symAut.apply_symm_apply (MulAut.centralQuotientAction e b))
    change _ = (MulAut.centralQuotientAction e b (q g)).val at h
    exact h.trans (congrArg Subtype.val (MulAut.centralQuotientAction_apply e b g))
  have he : q (g ^ 2) = q (b g) := by
    apply Subtype.ext
    rw [map_pow]
    exact hs.symm.trans (hfb ▸ hpoint)
  let c := (g ^ 2)⁻¹ * b g
  have hc : c ∈ center R := QuotientGroup.eq.mp (e.injective he)
  have hc2 : c ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := (⟨c,hc⟩ : center R))
    rw [hz] at h
    exact congrArg Subtype.val h
  have hcomm : Commute (g ^ 2) c := (Subgroup.mem_center_iff.mp hc _)
  have hbc : b g = g ^ 2 * c := by dsimp [c]; group
  have hg5 : g ^ 5 = 1 := by rw [←hg]; exact pow_orderOf_eq_one g
  have hc5 : c ^ 5 = 1 := by
    have h : (b g) ^ 5 = 1 := by rw [←map_pow,hg5,map_one]
    rw [hbc,hcomm.mul_pow,←pow_mul, Nat.mul_comm 2 5, pow_mul,hg5,one_pow,one_mul] at h
    exact h
  have hc1 : c = 1 := by
    have h : c ^ 5 = c := by
      calc
        _ = (c ^ 2) ^ 2 * c := by group
        _ = c := by rw [hc2,one_pow,one_mul]
    exact h.symm.trans hc5
  exact hn b hb (by rw [hbc,hc1,mul_one])

end Theory.SpecificGroups.Alternating.FiveCoverInnerActors
