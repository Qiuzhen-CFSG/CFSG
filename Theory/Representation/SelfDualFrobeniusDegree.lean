module
public import Theory.Representation.AbelianFrobeniusDegree
public import Theory.Representation.ThreeWeightSquare
public import Theory.Representation.SL3.BinaryFieldDescent.BaseChange
/-!
# Paired character orbits in self-dual Frobenius representations

For a faithful representation with an abelian odd-order Frobenius kernel,
a nontrivial character has a free complement orbit. Self-duality supplies
the inverse orbit. When the complement also has odd order these orbits are
disjoint, so the degree is at least twice the complement order. Scalar
extension removes any splitting-field assumption.

The full M₂₂-cover application in `Theory.Mathieu.M22.CoverSelfDualDegree`
uses the actual eleven-by-five subgroup to exclude degree-eight isometry
models in Aschbacher--Smith 4.4.3, printed p.623. The weight argument is
G.7.2(2), pp.347--348, with duality retaining the second orbit.
-/

public noncomputable section
open Subgroup
namespace Representation

private theorem character_eq_one_of_free {K U : Type*} [Group K] [Finite K] [Group U]
    (a : MulAut K) (hf : MonoidHom.FixedPointFree a)
    (χ : K →* U) (hχ : ∀ k, χ (a k) = χ k) : χ = 1 := by
  ext k
  obtain ⟨x,rfl⟩ := hf.commutatorMap_surjective k
  change χ (x / a x) = 1
  rw [map_div,hχ,div_self']

variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]

/-- An odd complement and the inverse orbit give twice the Frobenius degree bound. -/
theorem double_card_le_finrank_of_selfDual_frobenius [IsAlgClosed F]
    [FiniteDimensional F V] (ρ : Representation F G V)
    (K C : Subgroup G) [Finite K] [Nontrivial K] [IsMulCommutative K] [Finite C]
    (hKodd : Odd (Nat.card K)) (hCodd : Odd (Nat.card C))
    (hρ : Function.Injective ρ) (horder : (Nat.card K : F) ≠ 0)
    (hnorm : C ≤ normalizer (K : Set G))
    (hfree : ∀ c : C, c ≠ 1 → ∀ k : K, (c : G) * k * (c : G)⁻¹ = k → k = 1)
    (e : Representation.Equiv (ρ.comp K.subtype) (Representation.dual (ρ.comp K.subtype))) :
    2 * Nat.card C ≤ Module.finrank F V := by
  classical
  let σ : Representation F K V := ρ.comp K.subtype
  let n : C →* normalizer (K : Set G) := inclusion hnorm
  let a : C →* MulAut K := K.normalizerMonoidHom.comp n
  let p : C →* Equiv.Perm σ.CharacterWeight :=
    (automizerWeightPerm ρ K).comp (K.normalizerMonoidHom.rangeRestrict.comp n)
  obtain ⟨k,hk⟩ := exists_ne (1 : K)
  have hex : ∃ χ : σ.CharacterWeight, χ.val ≠ 1 := by
    by_contra! h
    apply hk
    apply eq_of_characterWeight_values σ (hρ.comp K.subtype_injective) horder
    intro χ
    simp [h χ]
  obtain ⟨χ,hχ⟩ := hex
  let invWeight : σ.CharacterWeight → σ.CharacterWeight := fun ψ =>
    ⟨ψ.val⁻¹, ThreeWeightSquare.weight_dual_inv σ horder ψ.val
      (ThreeWeightSquare.weight_equiv e ψ.val ψ.property)⟩
  have hinv (ψ : σ.CharacterWeight) : invWeight (invWeight ψ) = ψ := by
    apply Subtype.ext
    exact inv_inv ψ.val
  have hinji : Function.Injective invWeight := Function.LeftInverse.injective hinv
  have hp (c : C) (ψ : σ.CharacterWeight) : (p c ψ).val = ψ.val.comp (a c).symm.toMonoidHom := rfl
  have hcomm (c : C) (ψ : σ.CharacterWeight) : p c (invWeight ψ) = invWeight (p c ψ) := rfl
  have hstab (c : C) (hc : p c χ = χ) : c = 1 := by
    by_contra hne
    apply hχ
    apply character_eq_one_of_free (a c).symm
    · intro x hx
      apply hfree c hne x
      have hh : a c x = x := (congrArg (a c) hx).symm.trans ((a c).apply_symm_apply x)
      exact congrArg Subtype.val hh
    · intro x
      exact DFunLike.congr_fun ((hp c χ).symm.trans (congrArg Subtype.val hc)) x
  have ho : Function.Injective (fun c : C => p c χ) := by
    intro c d h
    change p c χ = p d χ at h
    have hh : p (d⁻¹*c) χ = χ := by
      rw [map_mul,map_inv]
      change (p d).symm (p c χ) = χ
      rw [h]
      exact (p d).symm_apply_apply χ
    exact (inv_mul_eq_one.mp (hstab _ hh)).symm
  have hne : χ ≠ invWeight χ := by
    intro hh
    apply hχ
    apply MonoidHom.ext
    intro x
    have hi : χ.val x = (χ.val x)⁻¹ := DFunLike.congr_fun (congrArg Subtype.val hh) x
    have h2 : (χ.val x)^2 = 1 := by
      rw [pow_two]
      calc
        _ = χ.val x * (χ.val x)⁻¹ := congrArg (fun y => χ.val x * y) hi
        _ = 1 := mul_inv_cancel _
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2)
      (orderOf_dvd_of_pow_eq_one (show (χ.val x)^Nat.card K = 1 by rw [←map_pow,pow_card_eq_one',map_one]))
    have hcop : Nat.Coprime 2 (Nat.card K) := Nat.coprime_two_left.mpr hKodd
    rw [hcop.gcd_eq_one] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have hcross (c : C) : p c χ ≠ invWeight χ := by
    intro hc
    have h2 : c^2 = 1 := hstab _ (by
      rw [pow_two,map_mul]
      change p c (p c χ) = χ
      rw [hc,hcomm,hc,hinv])
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_natCard c)
    have hcop : Nat.Coprime 2 (Nat.card C) := Nat.coprime_two_left.mpr hCodd
    rw [hcop.gcd_eq_one] at hd
    have hc1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
    exact hne (by simpa only [hc1,map_one,Equiv.Perm.one_apply] using hc)
  let f : C ⊕ C → σ.CharacterWeight := Sum.elim (fun c => p c χ) (fun c => invWeight (p c χ))
  have hdis (c d : C) : p c χ ≠ invWeight (p d χ) := by
    intro hh
    apply hcross (d⁻¹*c)
    rw [map_mul,map_inv]
    change (p d).symm (p c χ) = invWeight χ
    rw [hh,←hcomm]
    exact (p d).symm_apply_apply (invWeight χ)
  have hf : Function.Injective f := by
    intro x y h
    cases x with
    | inl c => cases y with
      | inl d => exact congrArg Sum.inl (ho h)
      | inr d => exact (hdis c d h).elim
    | inr c => cases y with
      | inl d => exact (hdis d c h.symm).elim
      | inr d => exact congrArg Sum.inr (ho (hinji h))
  obtain ⟨hfin,hcard⟩ := characterWeight_card_le σ horder
  let := hfin
  have hb := (Nat.card_le_card_of_injective f hf).trans hcard
  simpa only [Nat.card_sum,two_mul] using hb

/-- The paired-orbit degree bound over the original coefficient field. -/
theorem double_card_le_finrank_of_selfDual_frobenius_of_field
    [FiniteDimensional F V] (ρ : Representation F G V)
    (K C : Subgroup G) [Finite K] [Nontrivial K] [IsMulCommutative K] [Finite C]
    (hKodd : Odd (Nat.card K)) (hCodd : Odd (Nat.card C))
    (hρ : Function.Injective ρ) (horder : (Nat.card K : F) ≠ 0)
    (hnorm : C ≤ normalizer (K : Set G))
    (hfree : ∀ c : C, c ≠ 1 → ∀ k : K, (c : G) * k * (c : G)⁻¹ = k → k = 1)
    (e : ρ.Equiv ρ.dual) : 2 * Nat.card C ≤ Module.finrank F V := by
  let E := AlgebraicClosure F
  let σ := ρ.extendScalars E
  let d : σ.Equiv σ.dual := (BinaryFieldDescent.extendEquiv e).trans
    (BinaryFieldDescent.dualBaseChange ρ)
  let dK : Representation.Equiv (σ.comp K.subtype) (Representation.dual (σ.comp K.subtype)) :=
    .mk d.toLinearEquiv (fun k => d.isIntertwining' k)
  have horder' : (Nat.card K : E) ≠ 0 := by
    intro hz
    apply horder
    apply (algebraMap F E).injective
    simpa using hz
  have hh := double_card_le_finrank_of_selfDual_frobenius σ K C hKodd hCodd
    ((extendScalars_faithful_iff E ρ).mp hρ) horder' hnorm hfree dK
  simpa only [Module.finrank_baseChange] using hh

end Representation
