module

public import Theory.Representation.SL2NaturalOffenders.FieldAction.Coordinates

/-!
# Counting the linear kernel of a semilinear elementary group

A nonidentity element of the linear kernel is an involution. Put it in upper
transvection coordinates. Commutation makes every other actor upper triangular
with equal diagonal entries, and involutivity makes both diagonal entries one
for each linear actor. Thus the kernel embeds into the scalar field by its
upper-right entry. Commutation with an actor having nontrivial coefficient
automorphism forces those entries to be fixed scalars.

The common fixed vectors lie on the first coordinate line; their first
coordinates belong to one scalar eigenspace of the same automorphism. The
product estimate for fixed scalars and that eigenspace bounds the kernel order
times the common fixed-space order by the field order.

This is the nontrivial-kernel estimate in the natural-module case of
Aschbacher--Smith B.4.2(1), printed p.86 of the combined manuscript
(1 March 2004). All semilinearity and faithfulness assumptions concern the
specified representation; no offender classification is used.
-/

public section

namespace Representation.SL2NaturalOffenders
open Representation.BinaryOffender
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group H]

/-- A nontrivial linear kernel and a nontrivial coefficient action force this
product bound, independently of any offender inequality. -/
theorem kernel_mul_fixedSpace_card_le
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hfaith : Function.Injective ρ)
    (A : Subgroup H) (hA : IsElementaryAbelian 2 A)
    (φ : A →* (F ≃+* F))
    (hsemi : ∀ (a : A) (c : F) (v : Fin 2 → F), ρ a (c • v) = φ a c • ρ a v)
    (hker : φ.ker ≠ ⊥) (a : A) (ha : φ a ≠ 1) :
    Nat.card φ.ker * Nat.card (fixedSpace ρ A) ≤ Nat.card F := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let : IsElementaryAbelian 2 A := hA
  have hpow (x : A) : x ^ 2 = 1 :=
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p) x
  have hcomm (x y : A) : x * y = y * x := (IsMulCommutative.is_comm (M := A)).comm x y
  obtain ⟨⟨b, hb⟩, hbne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker
  have hb' : φ b = 1 := hb
  have hbne' : b ≠ 1 := fun h => hbne (Subtype.ext h)
  let T : Module.End F (Fin 2 → F) :=
    { toFun := ρ (b : H)
      map_add' := (ρ (b : H)).map_add
      map_smul' := by intro c v; simpa only [hb', RingAut.one_apply, RingHom.id_apply] using hsemi b c v }
  have hT : T * T = 1 := by
    apply LinearMap.ext
    intro v
    change ρ (b : H) (ρ (b : H) v) = v
    have he := congrArg (fun x : A => ρ (x : H)) (hpow b)
    simpa only [pow_two, Subgroup.coe_mul, map_mul, Subgroup.coe_one, map_one,
      Module.End.mul_apply, Module.End.one_apply] using LinearMap.congr_fun he v
  have hTne : T ≠ 1 := by
    intro h
    apply hbne'
    apply Subtype.ext
    apply hfaith
    apply LinearMap.ext
    intro v
    have hh : ρ (b : H) v = v := LinearMap.congr_fun h v
    simpa only [Subgroup.coe_one, map_one, Module.End.one_apply] using hh
  obtain ⟨e, he⟩ := involution_coordinates T hT hTne
  let f (x : A) : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := fun v => e (ρ (x : H) (e.symm v))
      map_zero' := by simp
      map_add' := by intro v w; simp }
  have f_apply (x : A) (v : Fin 2 → F) : f x v = e (ρ (x : H) (e.symm v)) := rfl
  have f_smul (x : A) (c : F) (v : Fin 2 → F) : f x (c • v) = φ x c • f x v := by
    simp only [f_apply, e.symm.map_smul, hsemi, e.map_smul]
  have f_mul (x y : A) (v : Fin 2 → F) : f (x * y) v = f x (f y v) := by
    simp only [f_apply, Subgroup.coe_mul, map_mul, Module.End.mul_apply, e.symm_apply_apply]
  have f_one (v : Fin 2 → F) : f 1 v = v := by simp [f_apply]
  have f_sq (x : A) (v : Fin 2 → F) : f x (f x v) = v := by
    rw [← f_mul, ← pow_two, hpow, f_one]
  have f_faith (x y : A) (h : ∀ v, f x v = f y v) : x = y := by
    apply Subtype.ext
    apply hfaith
    apply LinearMap.ext
    intro v
    apply e.injective
    simpa only [f_apply, e.symm_apply_apply] using h (e v)
  have f_b (v : Fin 2 → F) : f b v = ![v 0 + v 1, v 1] := by
    change e (T (e.symm v)) = _
    have hh := he (e.symm v)
    simpa only [e.apply_symm_apply] using hh
  have f_comm (x y : A) (v : Fin 2 → F) : f x (f y v) = f y (f x v) := by
    rw [← f_mul, ← f_mul, hcomm]
  let d (x : A) := f x ![0, 1] 1
  let t (x : A) := f x ![0, 1] 0
  have shape (x : A) (v : Fin 2 → F) :
      f x v = ![d x * φ x (v 0) + t x * φ x (v 1), d x * φ x (v 1)] := by
    apply commuting_transvection_shape (f x) (φ x) (f_smul x)
    intro v
    rw [← f_b, f_comm, f_b]
  have d_ne_zero (x : A) : d x ≠ 0 := by
    intro hd
    have hf0 : f x ![1, 0] = 0 := by simp [shape, hd]
    have hh := f_sq x ![1, 0]
    rw [hf0, map_zero] at hh
    have hh0 := congrFun hh 0
    simp at hh0
  have d_ker (x : φ.ker) : d x = 1 := by
    have hx : φ x = 1 := x.property
    have hh := congrFun (f_sq x ![1, 0]) 0
    simp only [shape, hx, RingAut.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero] at hh
    have hsq : d x ^ 2 = 1 := by simpa only [pow_two] using hh
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  have t_inj : Function.Injective (fun x : φ.ker => t x) := by
    intro x y ht
    apply Subtype.ext
    apply f_faith
    intro v
    have hx : φ x = 1 := x.property
    have hy : φ y = 1 := y.property
    simp only [shape, hx, hy, d_ker, RingAut.one_apply, ht]
  have t_fixed (x : φ.ker) : φ a (t x) = t x := by
    have hx : φ x = 1 := x.property
    have hh := congrFun (f_comm a x ![0, 1]) 0
    simp only [shape, hx, d_ker, RingAut.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, map_zero, map_one, mul_zero, mul_one, zero_add, one_mul] at hh
    have hc : d a * φ a (t x) = d a * t x := by linear_combination hh
    exact mul_left_cancel₀ (d_ne_zero a) hc
  let K := {x : F // φ a x = x}
  let E := {x : F // φ a x = (d a)⁻¹ * x}
  have hK : Nat.card φ.ker ≤ Nat.card K :=
    Nat.card_le_card_of_injective (fun x : φ.ker => (⟨t x, t_fixed x⟩ : K))
      (fun x y h => t_inj (congrArg Subtype.val h))
  have hfixed (v : fixedSpace ρ A) (x : A) : f x (e v.val) = e v.val := by
    rw [f_apply, e.symm_apply_apply]
    exact congrArg e (v.property x)
  have fixed_second (v : fixedSpace ρ A) : e v.val 1 = 0 := by
    have hh := congrFun (hfixed v b) 0
    rw [f_b] at hh
    simpa using hh
  have fixed_first (v : fixedSpace ρ A) : φ a (e v.val 0) = (d a)⁻¹ * e v.val 0 := by
    have hh := congrFun (hfixed v a) 0
    rw [shape] at hh
    simp only [Matrix.cons_val_zero, fixed_second, map_zero, mul_zero, add_zero] at hh
    calc
      φ a (e v.val 0) = (d a)⁻¹ * (d a * φ a (e v.val 0)) := by
        rw [← mul_assoc, inv_mul_cancel₀ (d_ne_zero a), one_mul]
      _ = (d a)⁻¹ * e v.val 0 := congrArg ((d a)⁻¹ * ·) hh
  have hE : Nat.card (fixedSpace ρ A) ≤ Nat.card E := by
    apply Nat.card_le_card_of_injective
      (fun v : fixedSpace ρ A => (⟨e v.val 0, fixed_first v⟩ : E))
    intro v w h
    apply Subtype.ext
    apply e.injective
    have h0 : e v.val 0 = e w.val 0 := congrArg Subtype.val h
    ext i
    fin_cases i
    · exact h0
    · exact (fixed_second v).trans (fixed_second w).symm
  exact (Nat.mul_le_mul hK hE).trans (coefficient_eigenspace_card_mul_le (φ a) ha (d a)⁻¹)

end Representation.SL2NaturalOffenders
