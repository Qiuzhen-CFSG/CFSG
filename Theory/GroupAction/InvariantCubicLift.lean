module
public import Theory.GroupAction.FixedPointHom
public import Theory.GroupTheory.PrimeDihedralShear
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.Group

/-!
# Invariant cyclic lifts over a cubic quotient

Let a two-group act on a finite three-group and its quotient of order three.
There is a lift of a nonidentity quotient element whose cyclic subgroup is
invariant: every actor fixes or inverts the chosen lift.

The kernel of the action on the quotient fixes a lift by coprime action.
If the quotient action is nontrivial, a commutator with an actor inducing
inversion gives a lift inverted by that actor and fixed by the action kernel.
This retains the full kernel of the original surjection; the lift need not
have order three.

Source application: the T-invariant elementary-nine enlargement in
Aschbacher–Smith, 14.5.20, printed p.1019, refs/quasithin.pdf.
-/

public noncomputable section

open Subgroup

namespace Theory.GroupAction
variable {A P Q : Type*} [Group A] [Group P] [Finite P]
  [Group Q] [Finite Q] [MulDistribMulAction A P] [MulDistribMulAction A Q]

/-- A cubic quotient has a nontrivial lift fixed or inverted by every two-actor. -/
theorem invariant_cubic_lift
    (hA : IsPGroup 2 A) (hP : IsPGroup 3 P) (hQ : Nat.card Q = 3)
    (f : P →* Q) (hf : Function.Surjective f)
    (he : ∀ (a : A) (x : P), f (a • x) = a • f x) :
    ∃ x : P, f x ≠ 1 ∧ ∀ a : A, a • x = x ∨ a • x = x⁻¹ := by
  classical
  let σ := MulDistribMulAction.toMulAut A Q
  let K := σ.ker
  let : IsCyclic Q := isCyclic_of_prime_card hQ
  have hAut : Nat.card (MulAut Q) = 2 := by
    rw [IsCyclic.card_mulAut,hQ]
    decide
  have hpow (a : A) : σ a ^ 2 = 1 := hAut ▸ pow_card_eq_one'
  have hfixed (z : Q) : ∃ w : P, f w = z ∧ ∀ k : K, (k : A) • w = w := by
    let : MulDistribMulAction K P := MulDistribMulAction.compHom P K.subtype
    let : MulDistribMulAction K Q := MulDistribMulAction.compHom Q K.subtype
    have hz : z ∈ fixedPointSubgroup K Q := by
      intro k
      exact DFunLike.congr_fun k.property z
    have hk : ¬ 2 ∣ Nat.card f.ker := by
      obtain ⟨n,hn⟩ := (hP.to_subgroup f.ker).exists_card_eq
      rw [hn]
      exact (by decide : ¬ 2 ∣ 3) ∘ Nat.prime_two.dvd_of_dvd_pow
    obtain ⟨w,hw⟩ := FixedPoints.mapHom_surjective_of_coprime_kernel
      (hA.to_subgroup K) f hf (fun k x => he k x) hk ⟨z,hz⟩
    exact ⟨w,congrArg Subtype.val hw,w.property⟩
  obtain ⟨z,hz⟩ : ∃ z : Q, z ≠ 1 := by
    by_contra! hn
    have hc : Nat.card Q = 1 := Nat.card_eq_one_iff_exists.mpr ⟨1,hn⟩
    omega
  obtain ⟨w,hw,hwfix⟩ := hfixed z
  have hfix_conj (a : A) (k : K) : (k : A) • (a • w) = a • w := by
    have hk : a⁻¹ * k * a ∈ K := by
      change σ (a⁻¹ * k * a) = 1
      simp only [map_mul,map_inv,show σ (k : A) = 1 from k.property,mul_one,inv_mul_cancel]
    have hh := congrArg (a • ·) (hwfix ⟨a⁻¹ * k * a,hk⟩)
    simpa only [←mul_smul,←mul_assoc,mul_inv_cancel,one_mul] using hh
  by_cases htriv : ∀ a : A, σ a = 1
  · exact ⟨w,hw ▸ hz,fun a => Or.inl (hwfix ⟨a,htriv a⟩)⟩
  obtain ⟨t,ht⟩ := not_forall.mp htriv
  have htwo := (Nat.card_eq_two_iff' (1 : MulAut Q)).mp hAut
  have hsame (a : A) (ha : σ a ≠ 1) : σ a = σ t :=
    (htwo.unique ha ht)
  have htinv (z : Q) : t • z = z⁻¹ := by
    have hmem : σ t = 1 ∨ ∀ z, σ t z = z⁻¹ := by
      apply MulAut.prime_involutive (by rw [hQ]; decide)
      intro z
      have hh := congrArg (fun b : MulAut Q => b z) (hpow t)
      simpa only [pow_two,MulAut.mul_apply,MulAut.one_apply] using hh
    exact hmem.resolve_left ht z
  let x := (t • w) * w⁻¹
  have ht2 : (t * t) • w = w := hwfix ⟨t*t,by
    change σ (t*t) = 1
    simpa only [map_mul,pow_two] using hpow t⟩
  have htx : t • x = x⁻¹ := by
    dsimp only [x]
    rw [smul_mul',smul_inv',←mul_smul,ht2,mul_inv_rev,inv_inv]
  have hxfix (k : K) : (k : A) • x = x := by
    dsimp only [x]
    rw [smul_mul',smul_inv',hfix_conj t k,hwfix k]
  have hfx : f x ≠ 1 := by
    dsimp only [x]
    rw [map_mul,map_inv,he,hw,htinv]
    intro hh
    have hz2 : z ^ 2 = 1 := by
      simpa only [pow_two,mul_inv_rev,inv_inv,inv_one] using congrArg Inv.inv hh
    have hz3 : z ^ 3 = 1 := hQ ▸ pow_card_eq_one'
    exact hz (by calc
      z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz2,hz3]; simp)
  refine ⟨x,hfx,?_⟩
  intro a
  by_cases ha : σ a = 1
  · exact Or.inl (hxfix ⟨a,ha⟩)
  · have hk : t⁻¹ * a ∈ K := by
      change σ (t⁻¹ * a) = 1
      rw [map_mul,map_inv,hsame a ha,inv_mul_cancel]
    have hh := congrArg (t • ·) (hxfix ⟨t⁻¹*a,hk⟩)
    have hax : a • x = t • x := by
      simpa only [←mul_smul,mul_inv_cancel_left] using hh
    exact Or.inr (hax.trans htx)

end Theory.GroupAction
