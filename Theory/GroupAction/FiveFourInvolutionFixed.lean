module

public import Theory.GroupAction.FourthPowerFixed
public import Theory.GroupAction.FiveInvertingInvolutionFixed
public import Theory.GroupTheory.SpecificGroups.FiveFourInvolution

/-!
# Fixed points and displacement of a five-four reflection

In a faithful action of a faithful `C₅ ⋊ C₄` on elementary sixteen,
every involution has equal fixed and displacement subgroups, of order four.
The involution inverts the order-five generator, so the fixed-space count
applies. Binary quadraticity and rank-nullity identify its displacement.

This is the source-neutral action calculation used in Parrott,
*A characterization of the Tits' simple group* (1972), pp.674–676.
-/

namespace Theory.GroupAction
open Subgroup
open scoped IsMulCommutative

/-- The fixed and displacement subgroups of a reflection both have order four. -/
public theorem five_four_involution_fixed_displacement
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (f : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ →*
      MulAut V) (hf : Function.Injective f)
    (u : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ)
    (hu : orderOf u = 2) :
    Nat.card (FixedPoints.subgroup (zpowers (f u)) V) = 4 ∧
      Nat.card (commutatorAction (zpowers (f u)) V) = 4 ∧
      commutatorAction (zpowers (f u)) V = FixedPoints.subgroup (zpowers (f u)) V := by
  let t : Multiplicative (ZMod 5) := Multiplicative.ofAdd 1
  let a : MulAut V := f (SemidirectProduct.inl t)
  have ht : orderOf t = 5 := by simp [t, orderOf_ofAdd_eq_addOrderOf]
  have ha : orderOf a = 5 := by
    rw [orderOf_injective f hf,
      orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective]
    exact ht
  have hb : (f u) ^ 2 = 1 := by
    rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one]
  have hinv : f u * a * (f u)⁻¹ = a⁻¹ := by
    have hh := congrArg f (faithful_five_four_involution_inverts_left φ hφ u hu t)
    simpa only [map_mul, map_inv] using hh
  have hfixed := card_fixed_of_involution_inverting_five_on_sixteen hV a (f u) ha hb hinv
  obtain ⟨hcount, hle⟩ := MulAut.involution_fixed_displacement_card_data (f u) hb
  have hdisplacement : Nat.card (commutatorAction (zpowers (f u)) V) = 4 := by
    rw [hV, hfixed] at hcount
    omega
  exact ⟨hfixed, hdisplacement,
    eq_of_le_of_card_ge hle (by rw [hfixed, hdisplacement])⟩

/-- Every fixed vector is a single displacement of the involution. -/
public theorem five_four_involution_exists_displacement
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (f : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ →*
      MulAut V) (hf : Function.Injective f)
    (u : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ)
    (hu : orderOf u = 2) (v : V) (hv : f u v = v) :
    ∃ w : V, f u w * w⁻¹ = v := by
  let c := f u
  let F := FixedPoints.subgroup (zpowers c) V
  let δ : V →* V := {
    toFun := fun w => c w * w⁻¹
    map_one' := by simp
    map_mul' := by
      intro w t
      simp only [map_mul, mul_inv_rev]
      ac_rfl }
  have hc2 : c ^ 2 = 1 := by
    change (f u) ^ 2 = 1
    rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one]
  have hcc (w : V) : c (c w) = w := congrArg (fun b : MulAut V => b w) hc2
  have hinv (w : V) : w⁻¹ = w := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) w))
  have hker : δ.ker = F := by
    ext w
    change c w * w⁻¹ = 1 ↔ w ∈ F
    rw [mul_inv_eq_one]
    exact (MulAut.mem_fixed_zpowers_iff c w).symm
  have hrange : δ.range ≤ F := by
    rintro _ ⟨w, rfl⟩
    apply (MulAut.mem_fixed_zpowers_iff c _).mpr
    change c (c w * w⁻¹) = c w * w⁻¹
    rw [map_mul, map_inv, hcc, hinv, hinv]
    exact mul_comm _ _
  have hF : Nat.card F = 4 :=
    (five_four_involution_fixed_displacement hV φ hφ f hf u hu).1
  have heq : δ.range = F := by
    apply eq_of_le_of_card_ge hrange
    have hh := δ.ker.card_mul_index
    rw [index_ker, hker, hF, hV] at hh
    omega
  have hvF : v ∈ F := (MulAut.mem_fixed_zpowers_iff c v).mpr hv
  have hvδ : v ∈ δ.range := heq.symm ▸ hvF
  exact hvδ

end Theory.GroupAction
