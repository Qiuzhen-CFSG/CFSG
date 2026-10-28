module

public import Theory.SpecificGroups.SymmetricSix.PolarAffine.QuadraticAutomorphism

/-!
# A quadratic adjustment fixing the original cubic normalizer

For a cubic actor T, its quadratic cocycle value has norm zero. Conjugating
the original quadratic automorphism by the kernel vector T(Q(T)) therefore
fixes the specified original cubic. If its kernel centralizer is trivial,
the same automorphism fixes the entire normalizer of that cubic subgroup.
The original quotient, full kernel coordinates, and nonprincipal adjustment
are retained; no complement or split-extension model is required.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymmetricSix.PolarAffine
open Subgroup

private theorem cubic_correction (a : A6) (ha : a ^ 3 = 1) :
    polarAction a.val (quadratic a) + quadratic a +
      polarAction a.val (polarAction a.val (quadratic a)) = 0 := by
  have hh : quadratic ((a*a)*a) = 0 := by
    rw [← pow_two, ← pow_succ, ha, quadratic_one]
  rw [quadratic_mul, quadratic_mul, Subgroup.coe_mul, polarAction_mul] at hh
  simpa only [add_comm, add_left_comm, add_assoc] using hh

private theorem fixes_normalizer {D : Type*} [Group D]
    (q : D →* A6) (β : MulAut D) (hβq : ∀ g, q (β g) = q g)
    (t : D) (hβt : β t = t)
    (hct : ∀ a : q.ker, Commute (a : D) t → a = 1)
    (g : D) (hg : g ∈ normalizer (zpowers t : Set D)) : β g = g := by
  have hfix (a : D) (ha : a ∈ zpowers t) : β a = a := by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    rw [map_zpow, hβt]
  have he := hfix (g*t*g⁻¹) ((mem_normalizer_iff.mp hg t).mp (mem_zpowers t))
  rw [map_mul, map_mul, map_inv, hβt] at he
  let a : q.ker := ⟨g⁻¹ * β g, by
    change q (g⁻¹ * β g) = 1
    rw [map_mul, map_inv, hβq, inv_mul_cancel]⟩
  have ha : Commute (a : D) t := by
    change g⁻¹ * β g * t = t * (g⁻¹ * β g)
    calc
      g⁻¹ * β g * t = g⁻¹ * (β g * t * (β g)⁻¹) * β g := by group
      _ = g⁻¹ * (g * t * g⁻¹) * β g := by rw [he]
      _ = t * (g⁻¹ * β g) := by group
  have ha1 := congrArg Subtype.val (hct a ha)
  change g⁻¹ * β g = 1 at ha1
  exact (inv_mul_eq_one.mp ha1).symm

/-- Normalize the nonprincipal quadratic adjustment on the original cubic.
It fixes the full original cubic normalizer pointwise while retaining the
quotient and every kernel element. Its explicit correcting vector is
`polarAction (q t).val (quadratic (q t))`. -/
theorem exists_cubic_normalized_quadratic_automorphism {D : Type*} [Group D]
    (q : D →* A6) (hq : Function.Surjective q)
    (k : q.ker ≃* Multiplicative NaturalModule)
    (hk : ∀ (g : D) (a : q.ker), k (MulAut.conjNormal g a) =
      Multiplicative.ofAdd (polarAction (q g).val (k a).toAdd))
    (t : D) (ht : orderOf t = 3)
    (hct : ∀ a : q.ker, Commute (a : D) t → a = 1) :
    ∃ β : MulAut D,
      (∀ g, q (β g) = q g) ∧
      (∀ a : q.ker, β a = (a : D)) ∧
      β t = t ∧
      (∀ g ∈ normalizer (zpowers t : Set D), β g = g) ∧
      (∀ g, β (β g) = g) ∧
      (∀ g, let v := polarAction (q t).val (quadratic (q t))
        let c := (k.symm (Multiplicative.ofAdd v) : D)
        β g = c * ((k.symm (Multiplicative.ofAdd (quadratic (q g))) : D) * g) * c⁻¹) ∧
      ¬ ∃ a : q.ker, ∀ g, β g = (a : D)⁻¹ * g * a := by
  obtain ⟨α, hαq, hαk, hα, hα2, hαni⟩ :=
    exists_original_quadratic_automorphism q hq k hk
  let j : NaturalModule → D := fun v => k.symm (Multiplicative.ofAdd v)
  have hj0 : j 0 = 1 := by simp [j]
  have hjadd (v w : NaturalModule) : j (v+w) = j v * j w := by
    change ((k.symm (Multiplicative.ofAdd v * Multiplicative.ofAdd w) : q.ker) : D) = _
    rw [map_mul]
    rfl
  have hjconj (g : D) (v : NaturalModule) :
      j (polarAction (q g).val v) = g * j v * g⁻¹ := by
    have hh := congrArg (fun x : Multiplicative NaturalModule => (k.symm x : D))
      (hk g (k.symm (Multiplicative.ofAdd v)))
    simpa only [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply,
      toAdd_ofAdd, MulAut.conjNormal_apply, j] using hh.symm
  let v := polarAction (q t).val (quadratic (q t))
  let c : q.ker := k.symm (Multiplicative.ofAdd v)
  have hc2 : (c : D) * c = 1 := by
    change j v * j v = 1
    rw [← hjadd]
    have h : v+v=0 := by ext i; exact CharTwo.add_self_eq_zero _
    rw [h, hj0]
  have hci : (c : D)⁻¹ = c := inv_eq_of_mul_eq_one_left hc2
  have hcomm (a : q.ker) : Commute (c : D) (a : D) := by
    have hh : c*a=a*c := k.injective (by simp only [map_mul, mul_comm])
    exact congrArg Subtype.val hh
  let β : MulAut D := MulAut.conj (c : D) * α
  have hβ (g : D) : β g = (c : D) * α g * (c : D)⁻¹ := rfl
  have hβq (g : D) : q (β g) = q g := by
    rw [hβ, map_mul, map_mul, map_inv, c.property, hαq, one_mul, inv_one, mul_one]
  have hβk (a : q.ker) : β a = (a : D) := by
    rw [hβ, hαk, (hcomm a).eq, mul_inv_cancel_right]
  have hβt : β t = t := by
    have ht3 : (q t)^3=1 := by rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
    have hv := cubic_correction (q t) ht3
    rw [hβ, hα, hci]
    change j v * (j (quadratic (q t)) * t) * j v = t
    calc
      j v * (j (quadratic (q t)) * t) * j v =
          (j v * j (quadratic (q t)) * (t * j v * t⁻¹)) * t := by group
      _ = j (v + quadratic (q t) + polarAction (q t).val v) * t := by
        rw [← hjconj, ← hjadd, ← hjadd]
      _ = t := by rw [hv, hj0, one_mul]
  refine ⟨β, hβq, hβk, hβt, fixes_normalizer q β hβq t hβt hct, ?_, ?_, ?_⟩
  · intro g
    rw [hβ, hβ, map_mul, map_mul, map_inv, hαk, hα2, hci]
    calc
      (c : D) * ((c : D) * g * (c : D)) * c = ((c : D)*c) * g * ((c : D)*c) := by group
      _ = g := by rw [hc2, one_mul, mul_one]
  · intro g
    exact (hβ g).trans (by rw [hα])
  · rintro ⟨a, ha⟩
    apply hαni
    refine ⟨a*c, fun g => ?_⟩
    have hh := ha g
    rw [hβ] at hh
    change α g = ((a : D)*(c : D))⁻¹ * g * ((a : D)*(c : D))
    calc
      α g = (c : D)⁻¹ * ((c : D) * α g * (c : D)⁻¹) * c := by group
      _ = (c : D)⁻¹ * ((a : D)⁻¹ * g * a) * c := by rw [hh]
      _ = ((a : D)*(c : D))⁻¹ * g * ((a : D)*(c : D)) := by group

end Theory.SpecificGroups.SymmetricSix.PolarAffine
