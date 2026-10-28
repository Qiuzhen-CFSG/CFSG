module
public import Theory.GroupAction.Extraspecial27InvolutionFixed
public import Theory.PGroupCore

/-!
# Two-group actors on an extraspecial group of order twenty-seven

A nonidentity involution fixing the center has exactly the center as its
fixed subgroup. A two-group acting faithfully and fixing the center therefore
acts freely on the twenty-four noncentral elements: a nontrivial point
stabilizer would contain such an involution. Orbit counting makes the actor
order divide twenty-four, hence eight.

The small special-unitary Sylow normalizer uses this bound to prove that
its center-preserving two-power actors are inner. This supplies the degree-one
SU3 case of DGS, Groups and Graphs (1985), 6.1, pp.118--119.
-/

public noncomputable section
open Subgroup MulAction
namespace MulAut

/-- A faithful two-group fixing the center of an extraspecial group of order 27 has order dividing eight. -/
theorem two_center_preserving_card_dvd_eight
    {F A : Type*} [Group F] [Finite F] [IsExtraspecial 3 F]
    [Group A] [Finite A] (hA : IsPGroup 2 A)
    (hF : Nat.card F=27) (action : A →* MulAut F) (hi : Function.Injective action)
    (hcenter : ∀ a:A, ∀ z ∈ center F, action a z=z) : Nat.card A ∣ 8 := by
  classical
  let : MulAction A F := MulAction.compHom F action
  let X : SubMulAction A F := {
    carrier := {x | x ∉ center F}
    smul_mem' := by
      intro a x hx hax
      change action a x ∈ center F at hax
      have he : action a x = x := (action a).injective (hcenter a _ hax)
      exact hx (he ▸ hax) }
  have hstab (x:X) : stabilizer A x = ⊥ := by
    apply card_eq_one.mp
    rcases (hA.to_subgroup (stabilizer A x)).card_eq_or_dvd with hc | hc
    · exact hc
    obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' 2 hc
    have ht2 : (t:A)^2=1 := by
      have he := pow_orderOf_eq_one t
      rw [ht] at he
      exact congrArg Subtype.val he
    have htn : (t:A) ≠ 1 := by
      intro he
      have het : t=1 := Subtype.ext he
      simp [het] at ht
    have hα : Function.Involutive (action (t:A)) := by
      intro y
      have hh := congrArg action ht2
      rw [map_pow,map_one,pow_two] at hh
      exact congrArg (fun a:MulAut F => a y) hh
    have hn : action (t:A) ≠ 1 := fun hh => htn (hi (hh.trans action.map_one.symm))
    have hf := fixed_eq_center_of_extraspecial27_involution hF (action (t:A)) hα hn (hcenter t)
    have hfix : action (t:A) x.val = x.val := congrArg Subtype.val (mem_stabilizer_iff.mp t.property)
    exact (x.property (hf.le ((mem_fixedSubgroup _ _).mpr hfix))).elim
  have hd : Nat.card A ∣ Nat.card X := by
    let := Fintype.ofFinite (Quotient (orbitRel A X))
    rw [Nat.card_congr (selfEquivSigmaOrbitsQuotientStabilizer A X),Nat.card_sigma]
    apply Finset.dvd_sum
    intro ω _
    change Nat.card A ∣ (stabilizer A ω.out).index
    rw [hstab,index_bot]
  have hc : Nat.card X = 24 := by
    let := Fintype.ofFinite F
    have hh := Fintype.card_subtype_compl (fun x:F => x ∈ center F)
    have hh' : Nat.card {x:F // x ∉ center F} = Nat.card F - Nat.card (center F) := by
      simpa only [Nat.card_eq_fintype_card] using hh
    change Nat.card {x:F // x ∉ center F} = 24
    rw [hh',hF,IsExtraspecial.center_order_p 3 F]
  rw [hc] at hd
  obtain ⟨n,hn⟩ := hA.exists_card_eq
  rw [hn] at hd ⊢
  have hnle : n≤3 := by
    by_contra hh
    have h16 : 16 ∣ 24 := (pow_dvd_pow 2 (by omega : 4≤n)).trans hd
    norm_num at h16
  exact pow_dvd_pow 2 hnle
end MulAut
