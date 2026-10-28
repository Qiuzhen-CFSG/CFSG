module

public import Theory.Representation.SL2NaturalOffenders.FieldAction.Kernel

/-!
# The order of an elementary semilinear plane group

A nontrivial linear involution supplies transvection coordinates. Commuting
linear actors embed in the upper-right field parameter. When the coefficient
action is nontrivial, these parameters are fixed scalars, whose squared order
is at most the field order. The coefficient image has order at most two, so
the whole elementary actor has order at most the field order as well.

This is the model counting input for the literal plane automizer in 11.5.3(3).
The coordinate calculation reuses the proof of the kernel estimate in
`SL2NaturalOffenders.FieldAction.Kernel`, without requiring an offender.
Source: Aschbacher--Smith, 11.5.3(3), printed pp.779--780.
-/

public section

open Subgroup Representation.BinaryOffender
open Representation.SL2NaturalOffenders
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.PlaneRank
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group H] [Finite H]

omit [Finite H] in
private theorem kernel_parameters
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hfaith : Function.Injective ρ)
    (A : Subgroup H) (hA : IsElementaryAbelian 2 A)
    (φ : A →* (F ≃+* F))
    (hsemi : ∀ (a : A) (c : F) (v : Fin 2 → F), ρ a (c • v) = φ a c • ρ a v)
    (hker : φ.ker ≠ ⊥) :
    ∃ t : φ.ker → F, Function.Injective t ∧
      ∀ (a : A) (x : φ.ker), φ a (t x) = t x := by
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
  have t_fixed (a : A) (x : φ.ker) : φ a (t x) = t x := by
    have hx : φ x = 1 := x.property
    have hh := congrFun (f_comm a x ![0, 1]) 0
    simp only [shape, hx, d_ker, RingAut.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, map_zero, map_one, mul_zero, mul_one, zero_add, one_mul] at hh
    have hc : d a * φ a (t x) = d a * t x := by linear_combination hh
    exact mul_left_cancel₀ (d_ne_zero a) hc
  exact ⟨fun x => t x, t_inj, t_fixed⟩

/-- An elementary group acting faithfully and semilinearly on a binary field
plane has order at most the order of the field. -/
theorem elementary_semilinear_card_le
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hfaith : Function.Injective ρ)
    (hsemi : ∀ h : H, ∃ σ : F ≃+* F,
      ∀ (c : F) (v : Fin 2 → F), ρ h (c • v) = σ c • ρ h v)
    (A : Subgroup H) (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ Nat.card F := by
  let φ : A →* (F ≃+* F) := (fieldAction ρ hsemi).comp A.subtype
  have hφ (a : A) (c : F) (v : Fin 2 → F) :
      ρ a (c • v) = φ a c • ρ a v := fieldAction_smul ρ hsemi a c v
  have hcard := card_le_two_mul_fieldAction_ker A hA φ
  by_cases hk : φ.ker = ⊥
  · have htwo : Nat.card A ≤ 2 := by simpa only [hk, Subgroup.card_bot, mul_one] using hcard
    exact htwo.trans (by exact Finite.one_lt_card)
  obtain ⟨t, ht, htf⟩ := kernel_parameters ρ hfaith A hA φ hφ hk
  by_cases htriv : ∀ a : A, φ a = 1
  · have hrange : φ.range = ⊥ := by
      apply bot_unique
      rintro _ ⟨a, rfl⟩
      exact mem_bot.mpr (htriv a)
    have hc : Nat.card A = Nat.card φ.ker := by
      calc
        Nat.card A = Nat.card φ.ker * Nat.card φ.range := by
          rw [← Subgroup.index_ker, Subgroup.card_mul_index]
        _ = _ := by rw [hrange, Subgroup.card_bot, mul_one]
    rw [hc]
    exact Nat.card_le_card_of_injective t ht
  push Not at htriv
  obtain ⟨a, ha⟩ := htriv
  let K := {x : F // φ a x = x}
  have hK : Nat.card φ.ker ≤ Nat.card K :=
    Nat.card_le_card_of_injective (fun x : φ.ker => (⟨t x, htf a x⟩ : K))
      (fun x y h => ht (congrArg Subtype.val h))
  have hsq : Nat.card K * Nat.card K ≤ Nat.card F := by
    simpa only [one_mul] using coefficient_eigenspace_card_mul_le (φ a) ha 1
  have htwo : 2 ≤ Nat.card φ.ker := by
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hk
  nlinarith

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.PlaneRank
