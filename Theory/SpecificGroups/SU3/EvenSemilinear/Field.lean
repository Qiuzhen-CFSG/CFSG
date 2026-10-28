module

public import Theory.SpecificGroups.SU3.EvenSemilinear.Coordinates
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.TorusWeights

/-!
# Field recovery from the binary unitary torus

Normalize the additive first-coordinate equivalence to fix one. The set of
scalars on which it is multiplicative is a subfield containing every torus
weight. The weight homomorphism has kernel of size at most three. A proper
subfield of a field of order q² has at most q elements: an element outside
it gives an injection from two copies of that subfield into the full field.
For q greater than two the weight image is too large, so the multiplicative
subfield is the whole field.

This proves the field-recovery step of Steinberg, Theorem 36, (3)–(4),
`refs/KGroup/GLS3/Chapter2St1.tex`, without a prime fixed-field restriction.
The binary coordinate equivalence uses the square formula, not division by two.
-/

public section
open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
open OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

private theorem torusWeight_ker_cube (k : Eˣ) (hk : k ∈ (torusWeight J).ker) : k ^ 3 = 1 := by
  have hv := congrArg (fun u : Eˣ => (u : E)) (MonoidHom.mem_ker.mp hk)
  rw [torusWeight_val] at hv
  have hbar : J.conj (k : E) ≠ 0 := (map_ne_zero J.conj).mpr (Units.ne_zero k)
  have he : (k : E) = J.conj (k : E) ^ 2 := (div_eq_one_iff_eq (pow_ne_zero 2 hbar)).mp hv
  have hf := congrArg J.conj he
  rw [map_pow, J.conj_involutive] at hf
  have hh : (k : E) ^ 4 = (k : E) := by
    calc
      (k : E) ^ 4 = ((k : E) ^ 2) ^ 2 := by ring
      _ = J.conj (k : E) ^ 2 := by rw [← hf]
      _ = (k : E) := he.symm
  apply Units.ext
  change (k : E) ^ 3 = 1
  apply mul_left_cancel₀ (Units.ne_zero k)
  calc
    (k : E) * (k : E) ^ 3 = (k : E) ^ 4 := by ring
    _ = (k : E) := hh
    _ = (k : E) * 1 := (mul_one _).symm

private theorem torusWeight_ker_card [Finite E] : Nat.card (torusWeight J).ker ≤ 3 := by
  have hle : (torusWeight J).ker ≤ (powMonoidHom 3 : Eˣ →* Eˣ).ker := by
    intro k hk
    exact torusWeight_ker_cube J k hk
  have hh := (Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)).trans_eq (IsCyclic.card_powMonoidHom_ker (G := Eˣ) 3)
  exact hh.trans (Nat.gcd_le_right _ (by decide))

private theorem proper_subfield_card_sq_le [Finite E] (S : Subfield E) (hS : S ≠ ⊤) :
    Nat.card S ^ 2 ≤ Nat.card E := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ S := by
    by_contra! h
    apply hS
    ext x
    simp [h x]
  let f : S × S → E := fun z => z.1.val + x * z.2.val
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    change (a : E) + x * (b : E) = (c : E) + x * (d : E) at h
    have hbd : b = d := by
      by_contra hbd
      have hnz : (b : E) - (d : E) ≠ 0 := sub_ne_zero.mpr (fun he => hbd (Subtype.ext he))
      apply hx
      have he : x = ((c : E) - (a : E)) / ((b : E) - (d : E)) := by
        apply (eq_div_iff hnz).mpr
        linear_combination h
      rw [he]
      exact S.div_mem (S.sub_mem c.property a.property) (S.sub_mem b.property d.property)
    apply Prod.ext _ hbd
    apply Subtype.ext
    rw [hbd] at h
    exact add_right_cancel h
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod, pow_two] using hh

private def multiplicativeSubfield (f : E ≃+ E) (hf1 : f 1 = 1) : Subfield E where
  carrier := {a | ∀ x, f (a * x) = f a * f x}
  zero_mem' := by simp
  one_mem' := by simp [hf1]
  add_mem' := by
    intro a b ha hb x
    simp only [add_mul, map_add]
    rw [ha x, hb x]
  neg_mem' := by
    intro a ha x
    simp only [neg_mul, map_neg]
    rw [ha x]
  mul_mem' := by
    intro a b ha hb x
    rw [mul_assoc, ha, hb, ha, mul_assoc]
  inv_mem' := by
    intro a ha
    by_cases hzero : a = 0
    · subst a
      simp
    · have hfa : f a ≠ 0 := by simpa using hzero
      have hfinv : f a * f a⁻¹ = 1 := by
        rw [← ha, mul_inv_cancel₀ hzero, hf1]
      intro x
      apply mul_left_cancel₀ hfa
      calc
        f a * f (a⁻¹ * x) = f (a * (a⁻¹ * x)) := (ha _).symm
        _ = f x := by rw [← mul_assoc, mul_inv_cancel₀ hzero, one_mul]
        _ = (f a * f a⁻¹) * f x := by rw [hfinv, one_mul]
        _ = f a * (f a⁻¹ * f x) := mul_assoc _ _ _

/-- Multiplicativity on the Hermitian torus weights implies multiplicativity
on the entire field of square order greater than four. -/
theorem mul_eq_of_torusWeight [Finite E] {q : ℕ} (hq : 2 < q)
    (hcard : Nat.card E = q ^ 2) (f : E ≃+ E) (hf1 : f 1 = 1)
    (hweight : ∀ k : Eˣ, ∀ x : E, f ((torusWeight J k : E) * x) =
      f (torusWeight J k : E) * f x) (a x : E) : f (a * x) = f a * f x := by
  classical
  let S := multiplicativeSubfield f hf1
  have hsmall (hne : S ≠ ⊤) : Nat.card S ≤ q := by
    have hs := proper_subfield_card_sq_le S hne
    rw [hcard] at hs
    nlinarith
  let e : (torusWeight J).range → S := fun z =>
    ⟨(z.val : E), by
      obtain ⟨k, hk⟩ := z.property
      change ∀ x, f ((z.val : E) * x) = f (z.val : E) * f x
      rw [← hk]
      exact hweight k⟩
  have heinj : Function.Injective e := by
    intro x y he
    apply Subtype.ext
    exact Units.ext (congrArg Subtype.val he)
  have henot : ¬ Function.Surjective e := by
    intro he
    obtain ⟨x, hx⟩ := he 0
    exact Units.ne_zero x.val (congrArg Subtype.val hx)
  have hrlt : Nat.card (torusWeight J).range < Nat.card S := by
    let := Fintype.ofFinite (torusWeight J).range
    let := Fintype.ofFinite S
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_lt_of_injective_not_surjective e heinj henot
  have hprod := (torusWeight J).ker.card_mul_index
  rw [Subgroup.index_ker, Nat.card_units, hcard] at hprod
  have hk := torusWeight_ker_card J
  have htop : S = ⊤ := by
    by_contra hne
    have hs := hsmall hne
    have hle : q ^ 2 - 1 ≤ 3 * (q - 1) := by
      rw [← hprod]
      exact Nat.mul_le_mul hk (by omega)
    have hq2 : 1 ≤ q ^ 2 := one_le_pow₀ (by omega)
    have hq1 : 1 ≤ q := by omega
    have hx := Nat.sub_add_cancel hq2
    have hy := Nat.sub_add_cancel hq1
    nlinarith
  have ha : a ∈ S := htop ▸ Subfield.mem_top a
  exact ha x

theorem first_field_of_torus_intertwining [Finite E] [CharP E 2] {q : ℕ} (hq : 2 < q)
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (φ : MulAut (hermitianUnipotentCoord J))
    (hact : ∀ k : Eˣ, ∃ l : Eˣ, ∀ z : hermitianUnipotentCoord J,
      φ (hermitianTorusAction J k z) = hermitianTorusAction J l (φ z)) :
    ∃ (σ : E ≃+* E) (t : Eˣ), ∀ z : hermitianUnipotentCoord J,
      (φ z).val.1 = (t : E) * σ z.val.1 := by
  let f₀ := coordFirstAddEquiv J hcard hfixed φ
  have hnz : f₀ 1 ≠ 0 := by simp
  let t : Eˣ := Units.mk0 (f₀ 1) hnz
  let f : E ≃+ E :=
    { toFun := fun a => (t : E)⁻¹ * f₀ a
      invFun := fun a => f₀.symm ((t : E) * a)
      left_inv := fun a => by simp
      right_inv := fun a => by simp
      map_add' := fun a b => by simp only [map_add, mul_add] }
  have hweight (k : Eˣ) : ∃ l : Eˣ, ∀ a : E,
      f₀ ((torusWeight J k : E) * a) = (torusWeight J l : E) * f₀ a := by
    obtain ⟨l, hl⟩ := hact k
    refine ⟨l, fun a => ?_⟩
    obtain ⟨z, hz⟩ := coord_first_surjective J hcard hfixed a
    change z.val.1 = a at hz
    subst a
    have he := congrArg (fun z : hermitianUnipotentCoord J => z.val.1) (hl z)
    rw [← coordFirstAddEquiv_apply J hcard hfixed φ, hermitianTorusAction_fst, hermitianTorusAction_fst,
      ← coordFirstAddEquiv_apply J hcard hfixed φ] at he
    simpa [f₀, torusWeight_val, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using he
  have hfweight (k : Eˣ) (a : E) : f ((torusWeight J k : E) * a) =
      f (torusWeight J k : E) * f a := by
    obtain ⟨l, hl⟩ := hweight k
    have hl1 := hl 1
    rw [mul_one] at hl1
    change (t : E)⁻¹ * f₀ ((torusWeight J k : E) * a) =
      ((t : E)⁻¹ * f₀ (torusWeight J k : E)) * ((t : E)⁻¹ * f₀ a)
    rw [hl a, hl1]
    change _ = ((t : E)⁻¹ * ((torusWeight J l : E) * (t : E))) * _
    field_simp
  have hf1 : f 1 = 1 := by
    change (t : E)⁻¹ * f₀ 1 = 1
    exact inv_mul_cancel₀ hnz
  let σ : E ≃+* E :=
    { f with map_mul' := mul_eq_of_torusWeight J hq hcard f hf1 hfweight }
  refine ⟨σ, t, fun z => ?_⟩
  change (φ z).val.1 = (t : E) * ((t : E)⁻¹ * f₀ z.val.1)
  rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero t), one_mul]
  exact (coordFirstAddEquiv_apply J hcard hfixed φ z).symm


end BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
