module

public import Theory.Representation.PSL3Two.SingerRestriction
public import Theory.Representation.GoldschmidtONan.Basic

/-!
# The fixed and moved parts of a five-dimensional Singer subspace

Odd-order averaging splits an invariant subspace containing the fixed plane
into that plane and its literal displacement span. The dimension is therefore
three. Every nonidentity Singer element generates its order-seven subgroup,
so the action on the seven nonzero moved vectors is regular and transitive.

Source: Aschbacher–Smith, Lemma J.2.3, printed pp.433–434
(PDF pp.444–445), combined manuscript of 1 March 2004.
-/

public section

open Representation Representation.BinaryOffender Representation.RegularCyclicNormalClosure
open Subgroup
namespace BinaryLinearThree.SingerRestriction.FiveSpace

section General
variable {X V : Type*} [_root_.Group X] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) X V) (H : Subgroup X) (A : Submodule (ZMod 2) V)

private theorem moved_le (hA : ∀ h ∈ H, ∀ a ∈ A, ρ h a ∈ A) :
    displacementSpan ρ H A ≤ A := by
  apply Submodule.span_le.mpr
  rintro _ ⟨h, hh, a, ha, rfl⟩
  exact A.sub_mem (hA h hh a ha) ha

private theorem fixed_inf_moved [Finite H] (hodd : Odd (Nat.card H)) :
    fixedSpace ρ H ⊓ displacementSpan ρ H A = ⊥ := by
  exact (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hodd).disjoint.mono_right
    (displacementSpan_mono ρ le_rfl le_top) |>.eq_bot

private theorem fixed_sup_moved [Finite H] (hodd : Odd (Nat.card H))
    (hFA : fixedSpace ρ H ≤ A) (hA : ∀ h ∈ H, ∀ a ∈ A, ρ h a ∈ A) :
    fixedSpace ρ H ⊔ displacementSpan ρ H A = A := by
  classical
  let := Fintype.ofFinite H
  have hcard : (Fintype.card H : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    rw [← Nat.card_eq_fintype_card, hk]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, Nat.cast_one, zero_add]
  apply le_antisymm (sup_le hFA (moved_le ρ H A hA))
  intro v hv
  let N : V := ∑ h : H, ρ h v
  have hN : N ∈ fixedSpace ρ H := by
    intro h
    change ρ (h : X) N = N
    simp only [N, map_sum, ← Module.End.mul_apply, ← map_mul]
    change (∑ k : H, ρ ((h * k : H) : X) v) = ∑ k : H, ρ k v
    exact (Group.mulLeft_bijective h).sum_comp (fun k : H => ρ k v)
  have hm : N - v ∈ displacementSpan ρ H A := by
    have hm : (∑ h : H, (ρ h v - v)) ∈ displacementSpan ρ H A :=
      Submodule.sum_mem _ fun h _ => Submodule.subset_span ⟨h, h.property, v, hv, rfl⟩
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul (ZMod 2), hcard, one_smul] at hm
    exact hm
  exact Submodule.mem_sup.mpr ⟨N, hN, -(N-v), (displacementSpan ρ H A).neg_mem hm,
    by abel⟩

private theorem moved_invariant (hA : ∀ h ∈ H, ∀ a ∈ A, ρ h a ∈ A)
    (h : X) (hh : h ∈ H) :
    ∀ v ∈ displacementSpan ρ H A, ρ h v ∈ displacementSpan ρ H A := by
  apply Submodule.span_induction
  · rintro _ ⟨k, hk, a, ha, rfl⟩
    rw [map_sub]
    have he : ρ h (ρ k a) = ρ (h*k*h⁻¹) (ρ h a) := by
      simp only [← Module.End.mul_apply, ← map_mul]
      simp [mul_assoc]
    rw [he]
    exact Submodule.subset_span ⟨h*k*h⁻¹, H.mul_mem (H.mul_mem hh hk) (H.inv_mem hh),
      ρ h a, hA h hh a ha, rfl⟩
  · simp only [map_zero]; exact (displacementSpan ρ H A).zero_mem
  · intro x y _ _ hx hy
    rw [map_add]
    exact (displacementSpan ρ H A).add_mem hx hy
  · intro r x _ hx
    rw [map_smul]
    exact (displacementSpan ρ H A).smul_mem r hx

private theorem transitive_of_prime_card [Finite H] [Finite V]
    (hH : Nat.card H = 7) (hM : Module.finrank (ZMod 2) A = 3)
    (hA : ∀ h ∈ H, ∀ a ∈ A, ρ h a ∈ A)
    (hdis : fixedSpace ρ H ⊓ A = ⊥)
    (v : V) (hv : v ∈ A) (hv0 : v ≠ 0)
    (w : V) (hw : w ∈ A) (hw0 : w ≠ 0) : ∃ h ∈ H, ρ h v = w := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hfree (g : H) (hg : ρ g v = v) : g = 1 := by
    by_contra hg1
    have hf : v ∈ fixedSpace ρ H := by
      intro k
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_prime_card hH hg1 (g' := k))
      have hfix : v ∈ fixedSpace (ρ.comp H.subtype) (Subgroup.zpowers g) :=
        (mem_fixedSpace_zpowers_iff _ _ _).mpr hg
      exact hn ▸ hfix ⟨g ^ n, Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) n⟩
    have hz : v ∈ (⊥ : Submodule (ZMod 2) V) := hdis ▸ (show v ∈ fixedSpace ρ H ⊓ A from ⟨hf,hv⟩)
    exact hv0 hz
  let f : H → {x : A // x ≠ 0} := fun h =>
    ⟨⟨ρ h v, hA h h.property v hv⟩, fun hz => hv0 ((ρ.apply_bijective h).injective
      ((congrArg (fun x : A => (x : V)) hz).trans (map_zero _).symm))⟩
  have hfi : Function.Injective f := by
    intro g k he
    have he' : ρ g v = ρ k v := congrArg (fun x : {x : A // x ≠ 0} => (x.val : V)) he
    have hk : ρ ((k⁻¹*g : H) : X) v = v := by
      change ρ ((k : X)⁻¹ * g) v = v
      rw [map_mul, Module.End.mul_apply, he', Representation.inv_self_apply]
    exact inv_mul_eq_one.mp (hfree (k⁻¹*g) hk) |>.symm
  have hc : Nat.card {x : A // x ≠ 0} = Nat.card H := by
    let := Fintype.ofFinite A
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hM, hH]
    decide
  have hs : Function.Surjective f := (Nat.bijective_iff_injective_and_card f).mpr ⟨hfi, hc.symm⟩ |>.surjective
  obtain ⟨h, he⟩ := hs ⟨⟨w, hw⟩, fun hz => hw0 (congrArg Subtype.val hz)⟩
  exact ⟨h, h.property, congrArg (fun x : {x : A // x ≠ 0} => (x.val : V)) he⟩
end General

variable (H : Subgroup Group) (hH : Nat.card H = 7)
  (A : Submodule (ZMod 2) Steinberg) (hA5 : Module.finrank (ZMod 2) A = 5)
  (hFA : fixedSpace S H ≤ A) (hA : ∀ h ∈ H, ∀ a ∈ A, S h a ∈ A)

include hH hA5 hFA hA in
/-- The literal displacement span is the three-dimensional complement to the
Singer fixed plane in the given invariant five-space. -/
theorem decomposition :
    Module.finrank (ZMod 2) (displacementSpan S H A) = 3 ∧
    A = fixedSpace S H ⊔ displacementSpan S H A ∧
    fixedSpace S H ⊓ displacementSpan S H A = ⊥ := by
  have ho : Odd (Nat.card H) := by rw [hH]; decide
  have hi := fixed_inf_moved S H A ho
  have hs := fixed_sup_moved S H A ho hFA hA
  refine ⟨?_, hs.symm, hi⟩
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (fixedSpace S H)
    (displacementSpan S H A)
  rw [hs, hi, finrank_bot, finrank_fixedSpace_order_seven H hH, hA5] at hd
  omega

include hA in
/-- Singer elements preserve the literal displacement span of an invariant subspace. -/
theorem moved_mem (h : Group) (hh : h ∈ H) (v : Steinberg)
    (hv : v ∈ displacementSpan S H A) : S h v ∈ displacementSpan S H A :=
  moved_invariant S H A hA h hh v hv

include hH hA5 hFA hA in
/-- The order-seven subgroup is transitive on the nonzero vectors in the moved
three-space; no orbit hypothesis is assumed. -/
theorem transitive (v : Steinberg) (hv : v ∈ displacementSpan S H A) (hv0 : v ≠ 0)
    (w : Steinberg) (hw : w ∈ displacementSpan S H A) (hw0 : w ≠ 0) :
    ∃ h ∈ H, S h v = w := by
  let : Finite Steinberg := Module.finite_of_finite (ZMod 2)
  have hd := decomposition H hH A hA5 hFA hA
  exact transitive_of_prime_card S H (displacementSpan S H A) hH hd.1
    (moved_mem H A hA) hd.2.2 v hv hv0 w hw hw0

end BinaryLinearThree.SingerRestriction.FiveSpace
